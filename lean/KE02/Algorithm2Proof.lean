import KE02.Algorithm2Statement
import KE02.EndpointProof
import Mathlib.Tactic

noncomputable section

namespace KE02

/-! ## The threshold `K`, the parameter `θ` and the scalar constants -/

theorem alg2K_spec (n : ℕ) : 16 * n ^ 3 ≤ 2 ^ alg2K n ∧ ∀ k < alg2K n, 2 ^ k < 16 * n ^ 3 := by
  have hex : ∃ K : ℕ, 16 * n ^ 3 ≤ 2 ^ K := ⟨16 * n ^ 3, Nat.lt_two_pow_self.le⟩
  exact ⟨Nat.find_spec hex, fun k hk => lt_of_not_ge (Nat.find_min hex hk)⟩

theorem doublingSearch_eq (target : ℕ) (hex : ∃ K : ℕ, target ≤ 2 ^ K) :
    ∀ fuel k, k ≤ Nat.find hex → Nat.find hex ≤ k + fuel →
      doublingSearch target fuel k (2 ^ k) = Nat.find hex := by
  intro fuel
  induction fuel with
  | zero =>
    intro k h₁ h₂
    simp only [doublingSearch]
    omega
  | succ fuel ih =>
    intro k h₁ h₂
    simp only [doublingSearch]
    split_ifs with h
    · exact le_antisymm h₁ (Nat.find_min' hex h)
    · have hlt : k < Nat.find hex :=
        lt_of_le_of_ne h₁ (fun e => h (by rw [e]; exact Nat.find_spec hex))
      rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
      exact ih (k + 1) hlt (by omega)

theorem doublingExponent_eq (target : ℕ) (hex : ∃ K : ℕ, target ≤ 2 ^ K) :
    doublingExponent target = Nat.find hex := by
  have h := doublingSearch_eq target hex target 0 (Nat.zero_le _)
    (by have := Nat.find_min' hex (Nat.lt_two_pow_self (n := target)).le; omega)
  simpa [doublingExponent] using h

theorem alg2K_doubling (n : ℕ) : doublingExponent (16 * n ^ 3) = alg2K n :=
  doublingExponent_eq _ _

theorem alg2K_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ alg2K n := by
  by_contra h
  have h0 : alg2K n = 0 := by omega
  have hs := (alg2K_spec n).1
  rw [h0] at hs
  have : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  omega

theorem alg2K_upper (n : ℕ) (hn : 1 ≤ n) : 2 ^ alg2K n < 32 * n ^ 3 := by
  have hK := alg2K_pos n hn
  obtain ⟨m, hm⟩ : ∃ m, alg2K n = m + 1 := ⟨alg2K n - 1, by omega⟩
  have h := (alg2K_spec n).2 m (by omega)
  rw [hm, pow_succ]
  omega

theorem alg2K_ceil (n : ℕ) (hn : 1 ≤ n) :
    alg2K n = ⌈Real.logb 2 (16 * (n : ℝ) ^ 3)⌉₊ := by
  have hx : (0 : ℝ) < 16 * (n : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have key : ∀ k : ℕ, ⌈Real.logb 2 (16 * (n : ℝ) ^ 3)⌉₊ ≤ k ↔ 16 * n ^ 3 ≤ 2 ^ k := by
    intro k
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow (by norm_num) hx, Real.rpow_natCast]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  apply le_antisymm
  · unfold alg2K
    exact Nat.find_min' _ ((key _).mp le_rfl)
  · exact (key _).mpr (alg2K_spec n).1

theorem alg2Theta_facts (n : ℕ) (hn : 1 ≤ n) :
    0 < alg2Theta n ∧ alg2Theta n ≤ 1 / 4 ∧
      1 / 2 - alg2Theta n = 1 / 2 * (1 - 1 / (2 * (alg2K n : ℝ))) := by
  have hK : (1 : ℝ) ≤ alg2K n := by exact_mod_cast alg2K_pos n hn
  unfold alg2Theta
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · field_simp
    ring

theorem bernoulli_half (K : ℕ) (hK : 1 ≤ K) : (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (K : ℝ))) ^ K := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsmall : 1 / (2 * (K : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hpos : 0 < 1 / (2 * (K : ℝ)) := by positivity
  have h := one_add_mul_le_pow (a := -(1 / (2 * (K : ℝ)))) (by linarith) K
  have e : (1 : ℝ) + (K : ℝ) * -(1 / (2 * (K : ℝ))) = 1 / 2 := by
    field_simp
    ring
  rw [e, ← sub_eq_add_neg] at h
  exact h

theorem LK_bound (n : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ) :
    δ / (64 * (n : ℝ) ^ 4) < δ / n * (1 / 2 - alg2Theta n) ^ alg2K n := by
  obtain ⟨_, _, hθe⟩ := alg2Theta_facts n hn
  have hKpos := alg2K_pos n hn
  have hup : (2 : ℝ) ^ alg2K n < 32 * (n : ℝ) ^ 3 := by exact_mod_cast alg2K_upper n hn
  have hb := bernoulli_half (alg2K n) hKpos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2K : (0 : ℝ) < 2 ^ alg2K n := by positivity
  rw [hθe, mul_pow, one_div_pow]
  have hinv : 1 / (32 * (n : ℝ) ^ 3) < 1 / 2 ^ alg2K n := one_div_lt_one_div_of_lt h2K hup
  have hdn : 0 < δ / n := by positivity
  calc δ / (64 * (n : ℝ) ^ 4) = δ / n * (1 / (32 * (n : ℝ) ^ 3) * (1 / 2)) := by
        field_simp
        ring
    _ < δ / n * (1 / 2 ^ alg2K n * (1 / 2)) := by
        apply mul_lt_mul_of_pos_left _ hdn
        exact mul_lt_mul_of_pos_right hinv (by norm_num)
    _ ≤ δ / n * (1 / 2 ^ alg2K n * (1 - 1 / (2 * (alg2K n : ℝ))) ^ alg2K n) := by
        apply mul_le_mul_of_nonneg_left _ hdn.le
        exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem centered_estimate_error_tol (F : ℝ → ℝ) {h τ : ℝ} (c lower middle upper : ℝ)
    (hh : 0 < h) (e₀ : |lower - F (c - h)| ≤ τ) (e₁ : |middle - F c| ≤ τ)
    (e₂ : |upper - F (c + h)| ≤ τ) :
    |centeredEstimate h lower middle upper - centeredVariation F h c| ≤ 4 * τ / h := by
  rw [centeredVariation_eq_estimate]
  unfold centeredEstimate
  have key : (upper - middle) / h - (middle - lower) / h -
      ((F (c + h) - F c) / h - (F c - F (c - h)) / h) =
      ((upper - F (c + h)) - 2 * (middle - F c) + (lower - F (c - h))) / h := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hh, div_le_div_iff_of_pos_right hh]
  have t₀ := abs_le.mp e₀
  have t₁ := abs_le.mp e₁
  have t₂ := abs_le.mp e₂
  rw [abs_le]
  constructor <;> linarith

theorem midpoint_estimate_error (F : ℝ → ℝ) {θ h : ℝ} (c lower middle upper : ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 4) (hh : 0 < h)
    (e₀ : |lower - F (c - h)| ≤ 2 * θ * h / 256) (e₁ : |middle - F c| ≤ 2 * θ * h / 256)
    (e₂ : |upper - F (c + h)| ≤ 2 * θ * h / 256) :
    |centeredEstimate h lower middle upper - centeredVariation F h c| ≤ θ / 32 ∧
      θ / 32 ≤ 1 / 128 := by
  refine ⟨?_, by linarith⟩
  have := centered_estimate_error_tol F c lower middle upper hh e₀ e₁ e₂
  rw [show 4 * (2 * θ * h / 256) / h = θ / 32 by field_simp; ring] at this
  exact this

/-! ## One loop pass -/

/-- Names for the quantities computed in one loop pass. -/
def stepRadius (θ : ℝ) (s : Alg2State) : ℝ := (1 / 2 - θ) * s.h

def stepTol (θ : ℝ) (s : Alg2State) : ℝ := 2 * θ * stepRadius θ s / 256

def stepValues (O : Oracle) (θ : ℝ) (s : Alg2State) : Fin 7 → ℝ :=
  fun i => O (s.log.length + i) (refinePoint θ (stepRadius θ s) s.t i) (stepTol θ s)

def stepLeft (O : Oracle) (θ : ℝ) (s : Alg2State) : ℝ :=
  endpointEstimate θ (stepRadius θ s) (stepValues O θ s 0) (stepValues O θ s 1)
    (stepValues O θ s 2) (stepValues O θ s 3)

def stepRight (O : Oracle) (θ : ℝ) (s : Alg2State) : ℝ :=
  endpointEstimate θ (stepRadius θ s) (stepValues O θ s 3) (stepValues O θ s 4)
    (stepValues O θ s 5) (stepValues O θ s 6)

def stepMid (O : Oracle) (θ : ℝ) (s : Alg2State) : ℝ :=
  O (s.log.length + 7) (selectCenter (stepRadius θ s) s.t (stepLeft O θ s) (stepRight O θ s))
    (stepTol θ s)

section Step

variable (O : Oracle) (θ : ℝ) (s : Alg2State)

theorem step_h : (alg2Step O θ s).h = stepRadius θ s := rfl

theorem step_t : (alg2Step O θ s).t =
    selectCenter (stepRadius θ s) s.t (stepLeft O θ s) (stepRight O θ s) := rfl

theorem step_estimate : (alg2Step O θ s).estimate =
    if stepLeft O θ s ≤ stepRight O θ s then
      centeredEstimate (stepRadius θ s) (stepValues O θ s 0) (stepMid O θ s) (stepValues O θ s 3)
    else
      centeredEstimate (stepRadius θ s) (stepValues O θ s 3) (stepMid O θ s)
        (stepValues O θ s 6) := rfl

theorem step_log : (alg2Step O θ s).log = s.log ++
    List.ofFn (fun i => (⟨refinePoint θ (stepRadius θ s) s.t i, stepTol θ s,
      stepValues O θ s i⟩ : Query)) ++
    [⟨selectCenter (stepRadius θ s) s.t (stepLeft O θ s) (stepRight O θ s), stepTol θ s,
      stepMid O θ s⟩] := rfl

theorem step_log_length : (alg2Step O θ s).log.length = s.log.length + 8 := by
  rw [step_log]
  simp

theorem step_value_mem (i : Fin 7) :
    (⟨refinePoint θ (stepRadius θ s) s.t i, stepTol θ s, stepValues O θ s i⟩ : Query) ∈
      (alg2Step O θ s).log := by
  rw [step_log]
  simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

theorem step_mid_mem :
    (⟨selectCenter (stepRadius θ s) s.t (stepLeft O θ s) (stepRight O θ s), stepTol θ s,
      stepMid O θ s⟩ : Query) ∈ (alg2Step O θ s).log := by
  rw [step_log]
  simp

variable {θ}

theorem step_window (hθ : 0 < θ) (_hθ' : θ ≤ 1 / 4) (hs : 0 < s.h) :
    s.t - s.h ≤ (alg2Step O θ s).t - (alg2Step O θ s).h ∧
      (alg2Step O θ s).t + (alg2Step O θ s).h ≤ s.t + s.h := by
  rw [step_t, step_h]
  unfold selectCenter stepRadius
  have : 0 ≤ θ * s.h := (mul_pos hθ hs).le
  split_ifs <;> constructor <;> nlinarith

theorem step_queries (hθ : 0 < θ) (hθ' : θ ≤ 1 / 4) (hs : 0 < s.h) :
    ∀ q ∈ (alg2Step O θ s).log, q ∈ s.log ∨
      (s.t - s.h ≤ q.point ∧ q.point ≤ s.t + s.h ∧ q.tol = stepTol θ s) := by
  intro q hq
  rw [step_log] at hq
  simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hq
  rcases hq with (hq | ⟨i, rfl⟩) | rfl
  · exact Or.inl hq
  · exact Or.inr ⟨(refinePoint_in_parent hθ hθ' hs i).1, (refinePoint_in_parent hθ hθ' hs i).2,
      rfl⟩
  · right
    have w := step_window O s hθ hθ' hs
    rw [step_t, step_h] at w
    have hr : 0 < stepRadius θ s := mul_pos (by linarith) hs
    refine ⟨by linarith [w.1], by linarith [w.2], rfl⟩

end Step

/-! ## The run -/

section Run

variable (O : Oracle) (n : ℕ) (δ : ℝ)

theorem alg2State_zero : alg2State O n δ 0 = alg2Init O n δ := rfl

theorem alg2State_succ (j : ℕ) :
    alg2State O n δ (j + 1) = alg2Step O (alg2Theta n) (alg2State O n δ j) := by
  unfold alg2State
  rw [Function.iterate_succ_apply']

theorem state_h (j : ℕ) :
    (alg2State O n δ j).h = (1 / 2 - alg2Theta n) ^ j * (δ / (2 * n)) := by
  induction j with
  | zero => rw [pow_zero, one_mul]; rfl
  | succ j ih =>
    rw [alg2State_succ, step_h, stepRadius, ih, pow_succ]
    ring

theorem state_log_length (j : ℕ) : (alg2State O n δ j).log.length = 3 + 8 * j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [alg2State_succ, step_log_length, ih]
    ring

theorem state_log_prefix {i j : ℕ} (hij : i ≤ j) :
    (alg2State O n δ i).log <+: (alg2State O n δ j).log := by
  induction hij with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rw [alg2State_succ, step_log, List.append_assoc]
    exact ih.trans (List.prefix_append _ _)

variable {n δ}

theorem state_h_pos (hn : 1 ≤ n) (hδ : 0 < δ) (j : ℕ) : 0 < (alg2State O n δ j).h := by
  obtain ⟨_, hθ', _⟩ := alg2Theta_facts n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [state_h]
  have : 0 < 1 / 2 - alg2Theta n := by linarith
  positivity

theorem state_window (hn : 1 ≤ n) (hδ : 0 < δ) (j : ℕ) :
    0 ≤ (alg2State O n δ j).t - (alg2State O n δ j).h ∧
      (alg2State O n δ j).t + (alg2State O n δ j).h ≤ δ / n := by
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  induction j with
  | zero =>
    show 0 ≤ δ / (2 * n) - δ / (2 * n) ∧ δ / (2 * n) + δ / (2 * n) ≤ δ / n
    constructor
    · simp
    · apply le_of_eq
      field_simp
      ring
  | succ j ih =>
    rw [alg2State_succ]
    have w := step_window O (alg2State O n δ j) hθ hθ' (state_h_pos O hn hδ j)
    constructor <;> linarith [ih.1, ih.2, w.1, w.2]

theorem state_nested (hn : 1 ≤ n) (hδ : 0 < δ) (j : ℕ) :
    (alg2State O n δ j).t - (alg2State O n δ j).h ≤
      (alg2State O n δ (j + 1)).t - (alg2State O n δ (j + 1)).h ∧
    (alg2State O n δ (j + 1)).t + (alg2State O n δ (j + 1)).h ≤
      (alg2State O n δ j).t + (alg2State O n δ j).h := by
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  rw [alg2State_succ]
  exact step_window O (alg2State O n δ j) hθ hθ' (state_h_pos O hn hδ j)

theorem state_h_le (hn : 1 ≤ n) (hδ : 0 < δ) (j : ℕ) :
    (alg2State O n δ j).h ≤ δ / (2 * n) := by
  obtain ⟨_, hθ', _⟩ := alg2Theta_facts n hn
  rw [state_h]
  have : (1 / 2 - alg2Theta n) ^ j ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have : 0 ≤ δ / (2 * (n : ℝ)) := by positivity
  nlinarith

theorem state_tol_upper (hn : 1 ≤ n) (hδ : 0 < δ) :
    ∀ j, ∀ q ∈ (alg2State O n δ j).log, q.tol ≤ δ / (512 * n) := by
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  intro j
  induction j with
  | zero =>
    intro q hq
    simp only [alg2State_zero, alg2Init, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact le_of_eq (by ring)
  | succ j ih =>
    intro q hq
    rw [alg2State_succ] at hq
    rcases step_queries O (alg2State O n δ j) hθ hθ' (state_h_pos O hn hδ j) q hq with
      hq' | ⟨_, _, htol⟩
    · exact ih q hq'
    · rw [htol, stepTol, stepRadius]
      have hs := state_h_le O hn hδ j
      have hs0 := state_h_pos O hn hδ j
      have hc : 2 * alg2Theta n * (1 / 2 - alg2Theta n) ≤ 1 := by nlinarith
      have hc0 : 0 ≤ 2 * alg2Theta n * (1 / 2 - alg2Theta n) := by
        apply mul_nonneg (by linarith) (by linarith)
      have key : 2 * alg2Theta n * ((1 / 2 - alg2Theta n) * (alg2State O n δ j).h) ≤
          δ / (2 * n) := by
        calc 2 * alg2Theta n * ((1 / 2 - alg2Theta n) * (alg2State O n δ j).h) =
            (2 * alg2Theta n * (1 / 2 - alg2Theta n)) * (alg2State O n δ j).h := by ring
          _ ≤ 1 * (alg2State O n δ j).h := mul_le_mul_of_nonneg_right hc hs0.le
          _ ≤ δ / (2 * n) := by linarith
      rw [show δ / (512 * (n : ℝ)) = δ / (2 * n) / 256 by ring]
      exact div_le_div_of_nonneg_right key (by norm_num)

theorem radius_lower_aux (hn : 1 ≤ n) (hδ : 0 < δ) {j : ℕ} (hj : j ≤ alg2K n) :
    δ / (128 * (n : ℝ) ^ 4) < (alg2State O n δ j).h := by
  obtain ⟨_, hθ', _⟩ := alg2Theta_facts n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLK := LK_bound n δ hn hδ
  rw [state_h]
  have hpow : (1 / 2 - alg2Theta n) ^ alg2K n ≤ (1 / 2 - alg2Theta n) ^ j :=
    pow_le_pow_of_le_one (by linarith) (by linarith) hj
  have e : δ / (128 * (n : ℝ) ^ 4) = δ / (64 * (n : ℝ) ^ 4) / 2 := by
    field_simp
    ring
  have e' : (1 / 2 - alg2Theta n) ^ alg2K n * (δ / (2 * n)) =
      δ / n * (1 / 2 - alg2Theta n) ^ alg2K n / 2 := by
    field_simp
  have hδn : 0 ≤ δ / (2 * n) := by positivity
  calc δ / (128 * (n : ℝ) ^ 4) < δ / n * (1 / 2 - alg2Theta n) ^ alg2K n / 2 := by
        rw [e]; linarith
    _ = (1 / 2 - alg2Theta n) ^ alg2K n * (δ / (2 * n)) := e'.symm
    _ ≤ (1 / 2 - alg2Theta n) ^ j * (δ / (2 * n)) := mul_le_mul_of_nonneg_right hpow hδn

theorem state_queries (hn : 1 ≤ n) (hδ : 0 < δ) :
    ∀ j ≤ alg2K n, ∀ q ∈ (alg2State O n δ j).log,
      0 ≤ q.point ∧ q.point ≤ δ / n ∧
        δ / (2 ^ 16 * (alg2K n : ℝ) * (n : ℝ) ^ 4) < q.tol := by
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : (1 : ℝ) ≤ alg2K n := by exact_mod_cast alg2K_pos n hn
  intro j
  induction j with
  | zero =>
    intro _ q hq
    have hdn : δ / (2 * n) + δ / (2 * n) = δ / n := by field_simp; ring
    have hpos : 0 < δ / (2 * n) := by positivity
    have htol : δ / (2 ^ 16 * (alg2K n : ℝ) * (n : ℝ) ^ 4) < δ / (2 * n) / 256 := by
      rw [div_div]
      apply div_lt_div_of_pos_left hδ (by positivity)
      have : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn' (by norm_num)
      nlinarith
    simp only [alg2State_zero, alg2Init, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨by simp, by simp; positivity, htol⟩
    · exact ⟨hpos.le, by linarith, htol⟩
    · exact ⟨by positivity, le_of_eq hdn, htol⟩
  | succ j ih =>
    intro hj q hq
    rw [alg2State_succ] at hq
    rcases step_queries O (alg2State O n δ j) hθ hθ' (state_h_pos O hn hδ j) q hq with
      hq' | ⟨hlo, hhi, htol⟩
    · exact ih (by omega) q hq'
    · have w := state_window O hn hδ j
      have hr := radius_lower_aux O hn hδ hj
      rw [alg2State_succ, step_h] at hr
      refine ⟨by linarith [w.1], by linarith [w.2], ?_⟩
      rw [htol, stepTol]
      unfold alg2Theta at hr ⊢
      have e : 2 * (1 / (4 * (alg2K n : ℝ))) * stepRadius (1 / (4 * (alg2K n : ℝ)))
          (alg2State O n δ j) / 256 =
          stepRadius (1 / (4 * (alg2K n : ℝ))) (alg2State O n δ j) / (512 * alg2K n) := by
        field_simp
        ring
      rw [e]
      have e' : δ / (2 ^ 16 * (alg2K n : ℝ) * (n : ℝ) ^ 4) =
          δ / (128 * (n : ℝ) ^ 4) / (512 * alg2K n) := by
        field_simp
        ring
      rw [e']
      exact div_lt_div_of_pos_right hr (by positivity)

/-- The loop returns the first state whose test succeeds, or the state after
all passes. -/
theorem loop_spec (θ : ℝ) (S : ℕ → Alg2State) (hS : ∀ j, S (j + 1) = alg2Step O θ (S j)) :
    ∀ m j, j ≤ (alg2Loop O θ m j (S j)).refinements ∧
      (alg2Loop O θ m j (S j)).refinements ≤ j + m ∧
      (alg2Loop O θ m j (S j)).state = S (alg2Loop O θ m j (S j)).refinements ∧
      (∀ i, j ≤ i → i < (alg2Loop O θ m j (S j)).refinements → ¬ alg2Stops (S i)) ∧
      ((alg2Loop O θ m j (S j)).returned = true ↔
        alg2Stops (S (alg2Loop O θ m j (S j)).refinements)) ∧
      ((alg2Loop O θ m j (S j)).refinements < j + m →
        alg2Stops (S (alg2Loop O θ m j (S j)).refinements)) := by
  intro m
  induction m with
  | zero =>
    intro j
    show j ≤ j ∧ j ≤ j + 0 ∧ S j = S j ∧ (∀ i, j ≤ i → i < j → ¬ alg2Stops (S i)) ∧
      (decide (alg2Stops (S j)) = true ↔ alg2Stops (S j)) ∧ (j < j + 0 → alg2Stops (S j))
    exact ⟨le_rfl, by omega, rfl, fun i h₁ h₂ => absurd h₂ (by omega), decide_eq_true_iff,
      fun h => absurd h (by omega)⟩
  | succ m ih =>
    intro j
    by_cases hstop : alg2Stops (S j)
    · have e : alg2Loop O θ (m + 1) j (S j) = ⟨S j, j, true⟩ := by
        simp only [alg2Loop, hstop, ↓reduceIte]
      rw [e]
      show j ≤ j ∧ j ≤ j + (m + 1) ∧ S j = S j ∧ (∀ i, j ≤ i → i < j → ¬ alg2Stops (S i)) ∧
        (true = true ↔ alg2Stops (S j)) ∧ (j < j + (m + 1) → alg2Stops (S j))
      exact ⟨le_rfl, by omega, rfl, fun i h₁ h₂ => absurd h₂ (by omega),
        ⟨fun _ => hstop, fun _ => rfl⟩, fun _ => hstop⟩
    · have e : alg2Loop O θ (m + 1) j (S j) = alg2Loop O θ m (j + 1) (S (j + 1)) := by
        simp only [alg2Loop, hstop, ↓reduceIte, hS j]
      rw [e]
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih (j + 1)
      refine ⟨by omega, by omega, h₃, ?_, h₅, fun h => h₆ (by omega)⟩
      intro i hi₁ hi₂
      rcases Nat.eq_or_lt_of_le hi₁ with rfl | hlt
      · exact hstop
      · exact h₄ i (by omega) hi₂

theorem run_spec :
    (alg2Run O n δ).refinements ≤ alg2K n ∧
      (alg2Run O n δ).state = alg2State O n δ (alg2Run O n δ).refinements ∧
      (∀ i < (alg2Run O n δ).refinements, ¬ alg2Stops (alg2State O n δ i)) ∧
      ((alg2Run O n δ).returned = true ↔
        alg2Stops (alg2State O n δ (alg2Run O n δ).refinements)) ∧
      ((alg2Run O n δ).refinements < alg2K n →
        alg2Stops (alg2State O n δ (alg2Run O n δ).refinements)) := by
  obtain ⟨_, h₂, h₃, h₄, h₅, h₆⟩ :=
    loop_spec O (alg2Theta n) (alg2State O n δ) (alg2State_succ O n δ) (alg2K n) 0
  simp only [zero_add] at h₂ h₆
  exact ⟨h₂, h₃, fun i hi => h₄ i (Nat.zero_le i) hi, h₅, h₆⟩

end Run

/-! ## Accuracy-dependent facts along the run -/

section Accuracy

variable {O : Oracle} {n : ℕ} {δ : ℝ} {F : ℝ → ℝ}

theorem estimate_error_zero
    (hacc : ∀ q ∈ (alg2State O n δ 0).log, |q.reply - F q.point| ≤ q.tol)
    (hn : 1 ≤ n) (hδ : 0 < δ) :
    |(alg2State O n δ 0).estimate -
      centeredVariation F (alg2State O n δ 0).h (alg2State O n δ 0).t| ≤ 1 / 64 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set t : ℝ := δ / (2 * (n : ℝ)) with ht
  set τ : ℝ := t / 256 with hτ
  have hh : 0 < t := by positivity
  have hlog : (alg2State O n δ 0).log =
      [⟨t - t, τ, O 0 (t - t) τ⟩, ⟨t, τ, O 1 t τ⟩, ⟨t + t, τ, O 2 (t + t) τ⟩] := rfl
  have e₀ := hacc ⟨t - t, τ, O 0 (t - t) τ⟩ (by rw [hlog]; simp)
  have e₁ := hacc ⟨t, τ, O 1 t τ⟩ (by rw [hlog]; simp)
  have e₂ := hacc ⟨t + t, τ, O 2 (t + t) τ⟩ (by rw [hlog]; simp)
  have h := centered_estimate_error_tol F t (O 0 (t - t) τ) (O 1 t τ) (O 2 (t + t) τ) hh e₀ e₁ e₂
  rw [show 4 * τ / t = 1 / 64 by rw [hτ]; field_simp; ring] at h
  exact h

theorem estimate_error_succ (j : ℕ)
    (hacc : ∀ q ∈ (alg2State O n δ (j + 1)).log, |q.reply - F q.point| ≤ q.tol)
    (hn : 1 ≤ n) (hδ : 0 < δ) :
    |(alg2State O n δ (j + 1)).estimate -
      centeredVariation F (alg2State O n δ (j + 1)).h (alg2State O n δ (j + 1)).t| ≤
        alg2Theta n / 32 := by
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  set s := alg2State O n δ j with hs
  have hpos : 0 < stepRadius (alg2Theta n) s := mul_pos (by linarith) (state_h_pos O hn hδ j)
  rw [alg2State_succ] at hacc ⊢
  rw [← hs] at hacc ⊢
  have hv : ∀ i : Fin 7, |stepValues O (alg2Theta n) s i -
      F (refinePoint (alg2Theta n) (stepRadius (alg2Theta n) s) s.t i)| ≤
        stepTol (alg2Theta n) s := fun i => hacc _ (step_value_mem O (alg2Theta n) s i)
  have hm := hacc _ (step_mid_mem O (alg2Theta n) s)
  simp only at hm
  rw [step_estimate, step_h, step_t]
  unfold selectCenter at hm ⊢
  unfold stepTol at hv hm
  split_ifs with hlr
  · simp only [hlr, ↓reduceIte] at hm
    refine (midpoint_estimate_error F (s.t - stepRadius (alg2Theta n) s) _ _ _ hθ hθ' hpos
      (by simpa [refinePoint] using hv 0) hm ?_).1
    have := hv 3
    simp only [refinePoint] at this
    simpa [sub_add_cancel] using this
  · simp only [hlr, ↓reduceIte] at hm
    refine (midpoint_estimate_error F (s.t + stepRadius (alg2Theta n) s) _ _ _ hθ hθ' hpos
      ?_ hm (by simpa [refinePoint] using hv 6)).1
    have := hv 3
    simp only [refinePoint] at this
    simpa [add_sub_cancel_right] using this

theorem potential_step_succ (hF : ConvexOn ℝ Set.univ F) (j : ℕ)
    (hacc : ∀ q ∈ (alg2State O n δ (j + 1)).log, |q.reply - F q.point| ≤ q.tol)
    (hn : 1 ≤ n) (hδ : 0 < δ) :
    endpointVariation F (alg2Theta n) (alg2State O n δ (j + 1)).h
        (alg2State O n δ (j + 1)).t ≤
      1 / 2 * endpointVariation F (alg2Theta n) (alg2State O n δ j).h
          (alg2State O n δ j).t + 1 / 32 := by
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  set s := alg2State O n δ j with hs
  rw [alg2State_succ] at hacc ⊢
  rw [← hs] at hacc ⊢
  have hv : ∀ i : Fin 7, |stepValues O (alg2Theta n) s i -
      F (refinePoint (alg2Theta n) ((1 / 2 - alg2Theta n) * s.h) s.t i)| ≤
        2 * alg2Theta n * ((1 / 2 - alg2Theta n) * s.h) / 256 :=
    fun i => hacc _ (step_value_mem O (alg2Theta n) s i)
  rw [step_h, step_t]
  exact endpoint_potential_step hF s.t (stepValues O (alg2Theta n) s) hθ hθ'
    (state_h_pos O hn hδ j) hv

end Accuracy

/-! ## Theorem 4.2 (scalar contract) -/

theorem initial_potential_lt {n : ℕ} {δ : ℝ} {F : ℝ → ℝ} (O : Oracle) (hn : 1 ≤ n)
    (hδ : 0 < δ)
    (hslope : ∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) :
    endpointVariation F (alg2Theta n) (alg2State O n δ 0).h (alg2State O n δ 0).t <
      (n : ℝ) ^ 3 := by
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := state_h_pos O hn hδ 0
  set t := (alg2State O n δ 0).t
  set h := (alg2State O n δ 0).h
  have p := mul_pos hθ hh
  rw [endpointVariation_eq_secant]
  have h₁ := (hslope (t + (1 - 2 * alg2Theta n) * h) (t + h) (by nlinarith)).2
  have h₂ := (hslope (t - h) (t - (1 - 2 * alg2Theta n) * h) (by nlinarith)).1
  nlinarith

theorem algorithm2_outcome (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (O : Oracle) (hn : 1 ≤ n)
    (hδ : 0 < δ) (hF : ConvexOn ℝ Set.univ F)
    (hslope : ∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
      secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2)
    (hacc : ∀ q ∈ (alg2Run O n δ).state.log, |q.reply - F q.point| ≤ q.tol) :
    Algorithm2Outcome n δ F O (alg2Run O n δ) := by
  obtain ⟨hJK, hstate, hearly, hret, hlate⟩ := run_spec O (n := n) (δ := δ)
  obtain ⟨hθ, hθ', _⟩ := alg2Theta_facts n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKpos := alg2K_pos n hn
  have hKreal : (1 : ℝ) ≤ alg2K n := by exact_mod_cast hKpos
  set J := (alg2Run O n δ).refinements with hJ
  set S := alg2State O n δ with hS
  set θ := alg2Theta n with hθdef
  rw [hstate] at hacc
  -- Accuracy of every request made before the returned state.
  have hacc' : ∀ i ≤ J, ∀ q ∈ (S i).log, |q.reply - F q.point| ≤ q.tol :=
    fun i hi q hq => hacc q ((state_log_prefix O n δ hi).subset hq)
  have hstep : ∀ i < J,
      endpointVariation F θ (S (i + 1)).h (S (i + 1)).t ≤
        1 / 2 * endpointVariation F θ (S i).h (S i).t + 1 / 32 :=
    fun i hi => potential_step_succ hF i (hacc' (i + 1) hi) hn hδ
  have hbound : ∀ j ≤ J, endpointVariation F θ (S j).h (S j).t ≤
      (1 / 2) ^ j * endpointVariation F θ (S 0).h (S 0).t +
        1 / 32 * ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h₁ := hstep j hj
      have h₂ := ih (by omega)
      rw [Finset.sum_range_succ', pow_succ]
      simp only [pow_zero]
      have e : ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ (i + 1) =
          1 / 2 * ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_succ]
        ring
      rw [e]
      linarith
  have hP0 := initial_potential_lt O hn hδ hslope
  -- After all K refinements the endpoint variation is below 1/8.
  have hfinal : J = alg2K n → endpointVariation F θ (S J).h (S J).t < 1 / 8 := by
    intro hJeq
    have hb := hbound J le_rfl
    have hgeom : ∑ i ∈ Finset.range J, (1 / 2 : ℝ) ^ i < 2 := by
      rw [geom_sum_eq (by norm_num)]
      have : 0 < (1 / 2 : ℝ) ^ J := by positivity
      rw [div_lt_iff_of_neg (by norm_num)]
      linarith
    have hpowpos : (0 : ℝ) < (1 / 2) ^ J := by positivity
    have hthr : (16 : ℝ) * (n : ℝ) ^ 3 ≤ 2 ^ J := by
      rw [hJeq]
      exact_mod_cast (alg2K_spec n).1
    have hsmall : (1 / 2 : ℝ) ^ J * (n : ℝ) ^ 3 ≤ 1 / 16 := by
      rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity)
        (by norm_num)]
      linarith
    have := mul_lt_mul_of_pos_left hP0 hpowpos
    nlinarith
  -- The test succeeds at the returned state.
  have hstops : alg2Stops (S J) := by
    rcases Nat.lt_or_ge J (alg2K n) with hlt | hge
    · exact hlate hlt
    · have hJeq : J = alg2K n := le_antisymm hJK hge
      have hPJ := hfinal hJeq
      have hcent := centered_le_endpoint hF (S J).t hθ (by linarith)
        (state_h_pos O hn hδ J)
      obtain ⟨m, hm⟩ : ∃ m, J = m + 1 := ⟨J - 1, by omega⟩
      have herr := estimate_error_succ m (by rw [← hm]; exact hacc) hn hδ
      rw [← hm] at herr
      have ha := abs_le.mp herr
      show (S J).estimate + 1 / 64 < 1 / 2
      have : θ / 32 ≤ 1 / 128 := by linarith
      linarith [ha.2]
  -- Accuracy of the returned test.
  have herr : |(S J).estimate - centeredVariation F (S J).h (S J).t| ≤ 1 / 64 := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0]
      exact estimate_error_zero (by rw [← h0]; exact hacc) hn hδ
    · obtain ⟨m, hm⟩ : ∃ m, J = m + 1 := ⟨J - 1, by omega⟩
      have := estimate_error_succ m (by rw [← hm]; exact hacc) hn hδ
      rw [← hm] at this
      linarith
  have hcentered : centeredVariation F (S J).h (S J).t < 1 / 2 := by
    have ha := abs_le.mp herr
    have : (S J).estimate + 1 / 64 < 1 / 2 := hstops
    linarith [ha.1]
  have hrl := radius_lower_aux O hn hδ hJK
  have hru : (S J).h ≤ δ / (2 * n) := by
    rw [state_h]
    have : (1 / 2 - θ) ^ J ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have : 0 ≤ δ / (2 * (n : ℝ)) := by positivity
    nlinarith
  have hwin := state_window O hn hδ J
  have hq := state_queries O hn hδ J hJK
  refine
    { returns := by rw [hret]; exact hstops
      refinements_le := hJK
      state_eq := hstate
      earlier_tests_fail := hearly
      returned_test_passes := by rw [hstate]; exact hstops
      radius_formula := state_h O n δ
      windows_inside := state_window O hn hδ
      windows_nested := state_nested O hn hδ
      initial_potential := hP0
      potential_step := hstep
      potential_bound := hbound
      potential_final := hfinal
      estimate_accuracy := by rw [hstate]; exact herr
      centered_lt_half := by rw [hstate]; exact hcentered
      radius_lower := by rw [hstate]; exact hrl
      radius_upper := by rw [hstate]; exact hru
      window := by rw [hstate]; exact hwin
      budget := ?_
      queries_inside := ?_
      tolerance_upper := by rw [hstate]; exact state_tol_upper O hn hδ J
      tolerance_lt_one := ?_
      radius_lt_one := ?_
      calls_exact := by rw [hstate]; exact state_log_length O n δ J
      calls_le := by rw [hstate, state_log_length]; omega
      gap_scale := ?_
      min_accuracy := ?_ }
  · rw [hstate]
    have hh := state_h_pos O hn hδ J
    have hn0 : (0 : ℝ) < n := by linarith
    refine ⟨by linarith [hwin.1], ?_⟩
    have : (S J).t ≤ δ / n := by linarith [hwin.2]
    calc (n : ℝ) * (S J).t ≤ n * (δ / n) := mul_le_mul_of_nonneg_left this hn0.le
      _ = δ := by field_simp
  · rw [hstate]
    intro q hqm
    obtain ⟨a, b, c⟩ := hq q hqm
    have : 0 < δ / (2 ^ 16 * (alg2K n : ℝ) * (n : ℝ) ^ 4) := by positivity
    exact ⟨a, b, by linarith⟩
  · intro hδ2 q hq
    rw [hstate] at hq
    have hq' := state_tol_upper O hn hδ J q hq
    have : δ / (512 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    linarith
  · intro hδ2
    rw [hstate]
    have : δ / (2 * (n : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    linarith
  · rw [hstate]
    have hpos : 0 < δ / (128 * (n : ℝ) ^ 4) := by positivity
    have hsq : (δ / (128 * (n : ℝ) ^ 4)) ^ 2 < (S J).h ^ 2 := by
      exact pow_lt_pow_left₀ hrl hpos.le (by norm_num)
    have e : (2 : ℝ)⁻¹ ^ 34 * δ ^ 2 / (n : ℝ) ^ 12 =
        (δ / (128 * (n : ℝ) ^ 4)) ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) := by
      field_simp
      ring
    rw [e]
    exact div_lt_div_of_pos_right hsq (by positivity)
  · rw [hstate]
    exact fun q hqm => (hq q hqm).2.2

/-- With the exact oracle `O i x τ = G x`, every recorded reply is exact. -/
theorem exact_oracle_log (G : ℝ → ℝ) (n : ℕ) (δ : ℝ) :
    ∀ j, ∀ q ∈ (alg2State (fun _ x _ => G x) n δ j).log, q.reply = G q.point := by
  intro j
  induction j with
  | zero =>
    intro q hq
    simp only [alg2State_zero, alg2Init, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> rfl
  | succ j ih =>
    intro q hq
    rw [alg2State_succ, step_log] at hq
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hq
    rcases hq with (hq | ⟨i, rfl⟩) | rfl
    · exact ih q hq
    · rfl
    · rfl

theorem main_bound_form (n : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (2 : ℝ)⁻¹ ^ 34 * (δ / n) ^ 12 ≤ (2 : ℝ)⁻¹ ^ 34 * δ ^ 2 / (n : ℝ) ^ 12 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_of_le_one hδ.le hδ1.le (by norm_num)

theorem algorithm2_premises_satisfiable (n : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ) :
    ∃ (F : ℝ → ℝ) (O : Oracle), ConvexOn ℝ Set.univ F ∧
      (∀ u v : ℝ, u < v → (n : ℝ) * (n + 1) / 2 ≤ secant F u v ∧
        secant F u v ≤ (n : ℝ) ^ 2 * (n + 1) / 2) ∧
      ∀ q ∈ (alg2Run O n δ).state.log, |q.reply - F q.point| ≤ q.tol := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKreal : (1 : ℝ) ≤ alg2K n := by exact_mod_cast alg2K_pos n hn
  set c : ℝ := (n : ℝ) * (n + 1) / 2 with hc
  refine ⟨fun x => c * x, fun _ x _ => c * x, ?_, ?_, ?_⟩
  · have hc0 : 0 ≤ c := by positivity
    simpa [smul_eq_mul] using
      (convexOn_id (convex_univ : Convex ℝ (Set.univ : Set ℝ))).smul hc0
  · intro u v huv
    have hs : secant (fun x => c * x) u v = c := by
      unfold secant
      field_simp [sub_ne_zero.mpr huv.ne']
    rw [hs]
    refine ⟨le_rfl, ?_⟩
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h2 : (0 : ℝ) ≤ n + 1 := by positivity
    rw [hc]
    nlinarith
  · obtain ⟨hJK, hstate, -⟩ := run_spec (fun _ x _ => c * x) (n := n) (δ := δ)
    intro q hq
    rw [hstate] at hq
    have htol := (state_queries (fun _ x _ => c * x) hn hδ _ hJK q hq).2.2
    have hpos : 0 < δ / (2 ^ 16 * (alg2K n : ℝ) * (n : ℝ) ^ 4) := by positivity
    rw [exact_oracle_log (fun x => c * x) n δ _ q hq, sub_self, abs_zero]
    linarith

theorem algorithm2Certificate : Algorithm2Certificate where
  K_spec := alg2K_spec
  K_doubling := alg2K_doubling
  K_ceil_log := alg2K_ceil
  K_upper := fun n hn => ⟨alg2K_upper n hn, alg2K_pos n hn⟩
  theta_range := alg2Theta_facts
  bernoulli := bernoulli_half
  LK_bound := LK_bound
  main_bound_form := main_bound_form
  stopping_constants := by norm_num
  midpoint_estimate_error := fun F _ _ c lower middle upper hθ hθ' hh e₀ e₁ e₂ =>
    midpoint_estimate_error F c lower middle upper hθ hθ' hh e₀ e₁ e₂
  run := algorithm2_outcome
  premises_satisfiable := algorithm2_premises_satisfiable

end KE02
