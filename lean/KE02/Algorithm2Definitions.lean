import KE02.SlopeDefinitions
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn

/-!
# Algorithm 2 (improved selection) as an explicit transcript

The algorithm only sees the replies of an evaluation oracle. A reply is an
arbitrary real number; accuracy is never part of a definition here and
appears only as an explicit premise of the theorems.

Request number `i` (counted from `0` over the whole run), made at the point
`x` with requested absolute error `τ`, receives the reply `O i x τ`. Because
the algorithm is deterministic, every adaptive reply strategy is described
by such a function `O`.
-/

noncomputable section

namespace KE02

/-- One evaluation request: the point, the requested absolute error and
the reply that the algorithm received. -/
structure Query where
  point : ℝ
  tol : ℝ
  reply : ℝ

/-- An evaluation oracle: `O i x τ` is the reply to request number `i`, made
at `x` with requested absolute error `τ`. -/
abbrev Oracle := ℕ → ℝ → ℝ → ℝ

/-- `K = ⌈log₂(16 n³)⌉`, defined as the least natural number with
`16 n³ ≤ 2^K`. -/
def alg2K (n : ℕ) : ℕ :=
  Nat.find (⟨16 * n ^ 3, Nat.lt_two_pow_self.le⟩ : ∃ K : ℕ, 16 * n ^ 3 ≤ 2 ^ K)

/-- Repeated doubling: starting from exponent `k` with current power `p`,
double until the power reaches `target`, using at most `fuel` doublings. -/
def doublingSearch (target : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, k, _ => k
  | fuel + 1, k, p => if target ≤ p then k else doublingSearch target fuel (k + 1) (2 * p)

/-- The exponent found by doubling `1, 2, 4, …` until `target` is reached. -/
def doublingExponent (target : ℕ) : ℕ := doublingSearch target target 0 1

/-- `θ = 1/(4K)`. -/
def alg2Theta (n : ℕ) : ℝ := 1 / (4 * (alg2K n : ℝ))

/-- The seven evaluation points of one refinement of Algorithm 2, for the
current center `t` and the updated radius `h`: the four points of
`S_h^(θ)(t-h)` (indices 0–3) and the four points of `S_h^(θ)(t+h)`
(indices 3–6). The point `t = (t-h)+h = (t+h)-h` serves both. -/
def refinePoint (θ h t : ℝ) : Fin 7 → ℝ :=
  ![(t - h) - h, (t - h) - (1 - 2 * θ) * h, (t - h) + (1 - 2 * θ) * h, t,
    (t + h) - (1 - 2 * θ) * h, (t + h) + (1 - 2 * θ) * h, (t + h) + h]

/-- Selection rule of Algorithm 2: move to `t-h` when the left estimate is
at most the right estimate (ties go left), otherwise to `t+h`. -/
def selectCenter (h t leftEstimate rightEstimate : ℝ) : ℝ :=
  if leftEstimate ≤ rightEstimate then t - h else t + h

/-- The state of Algorithm 2 after a test: center, radius, the computed
value of `Ŝ_h(t)` used by the stopping test, and every request so far. -/
structure Alg2State where
  t : ℝ
  h : ℝ
  estimate : ℝ
  log : List Query

/-- The stopping test `Ŝ_h(t) + 1/64 < 1/2`. -/
abbrev alg2Stops (s : Alg2State) : Prop := s.estimate + 1 / 64 < 1 / 2

/-- Lines 2–3 of Algorithm 2: `t = h = δ/(2n)` and three requests with
absolute error `h/256`. -/
def alg2Init (O : Oracle) (n : ℕ) (δ : ℝ) : Alg2State :=
  let t := δ / (2 * (n : ℝ))
  let h := δ / (2 * (n : ℝ))
  let τ := h / 256
  let a := O 0 (t - h) τ
  let b := O 1 t τ
  let c := O 2 (t + h) τ
  ⟨t, h, centeredEstimate h a b c, [⟨t - h, τ, a⟩, ⟨t, τ, b⟩, ⟨t + h, τ, c⟩]⟩

/-- One pass through the body of the loop of Algorithm 2: update the radius,
request the seven values for the two endpoint variations, select with ties
to the left, request the new midpoint value, and compute `Ŝ_h(t)` at the
new center from the new midpoint value and the two already requested
values at the new center `∓ h`. All eight requests use absolute error
`2θh/256` with the updated `h`. -/
def alg2Step (O : Oracle) (θ : ℝ) (s : Alg2State) : Alg2State :=
  let h := (1 / 2 - θ) * s.h
  let τ := 2 * θ * h / 256
  let base := s.log.length
  let x := refinePoint θ h s.t
  let v : Fin 7 → ℝ := fun i => O (base + i) (x i) τ
  let leftEstimate := endpointEstimate θ h (v 0) (v 1) (v 2) (v 3)
  let rightEstimate := endpointEstimate θ h (v 3) (v 4) (v 5) (v 6)
  let t := selectCenter h s.t leftEstimate rightEstimate
  let m := O (base + 7) t τ
  let estimate :=
    if leftEstimate ≤ rightEstimate then centeredEstimate h (v 0) m (v 3)
    else centeredEstimate h (v 3) m (v 6)
  ⟨t, h, estimate, s.log ++ List.ofFn (fun i => (⟨x i, τ, v i⟩ : Query)) ++ [⟨t, τ, m⟩]⟩

/-- The result of a run: the final state, the number of refinements
performed, and whether a `return` statement was executed. -/
structure Alg2Result where
  state : Alg2State
  refinements : ℕ
  returned : Bool

/-- The stopping test followed by at most `fuel` further loop passes;
`j` counts the refinements performed so far. With no passes left, the run
ends, and `returned` records whether the last test succeeded. -/
def alg2Loop (O : Oracle) (θ : ℝ) : ℕ → ℕ → Alg2State → Alg2Result
  | 0, j, s => ⟨s, j, decide (alg2Stops s)⟩
  | fuel + 1, j, s =>
      if alg2Stops s then ⟨s, j, true⟩ else alg2Loop O θ fuel (j + 1) (alg2Step O θ s)

/-- Algorithm 2: the initial test and the loop `for j = 0, …, K-1`. -/
def alg2Run (O : Oracle) (n : ℕ) (δ : ℝ) : Alg2Result :=
  alg2Loop O (alg2Theta n) (alg2K n) 0 (alg2Init O n δ)

/-- The state after `j` refinements when no test is applied; used to name
the intermediate centers `t_j` and radii `h_j`. -/
def alg2State (O : Oracle) (n : ℕ) (δ : ℝ) (j : ℕ) : Alg2State :=
  (alg2Step O (alg2Theta n))^[j] (alg2Init O n δ)

end KE02
