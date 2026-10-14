import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.VecNotation

noncomputable section

namespace KE02

/-- The endpoints used by the scalar selector. Positivity is a conclusion,
not an invariant imposed on the data type. -/
structure SelectorInterval where
  left : ℝ
  right : ℝ

def selectorLength (I : SelectorInterval) : ℝ := I.right - I.left

def selectorInitial (n : ℕ) (δ : ℝ) : SelectorInterval := ⟨0, δ / n⟩

def selectorSecant (F : ℝ → ℝ) (u v : ℝ) : ℝ := (F v - F u) / (v - u)

def selectorPotential (F : ℝ → ℝ) (I : SelectorInterval) : ℝ :=
  selectorSecant F (I.right - selectorLength I / 4) I.right -
    selectorSecant F I.left (I.left + selectorLength I / 4)

/-- `false` is the left middle-quarter child; `true` is the right one. -/
def selectorChild (I : SelectorInterval) (right : Bool) : SelectorInterval :=
  if right then
    ⟨I.left + selectorLength I / 2, I.left + 3 * selectorLength I / 4⟩
  else
    ⟨I.left + selectorLength I / 4, I.left + selectorLength I / 2⟩

/-- The four value requests are ordered as u, u+ell/4, v-ell/4, v. -/
def selectorQueryPoint (I : SelectorInterval) (q : Fin 4) : ℝ :=
  ![I.left, I.left + selectorLength I / 4,
    I.right - selectorLength I / 4, I.right] q

def selectorTolerance (I : SelectorInterval) : ℝ := selectorLength I / 1024

def selectorEstimate (I : SelectorInterval) (values : Fin 4 → ℝ) : ℝ :=
  4 * (values 3 - values 2 - values 1 + values 0) / selectorLength I

/-- Each round has eight separate replies. Identical query points may receive
different replies, and no sign or consistency condition is imposed here. -/
abbrev SelectorReplies := ℕ → Bool → Fin 4 → ℝ

/-- This comparison implements the prescribed tie-to-left rule. -/
noncomputable def selectorStep (I : SelectorInterval) (values : Bool → Fin 4 → ℝ) :
    SelectorInterval := by
  classical
  exact if selectorEstimate (selectorChild I false) (values false) ≤
      selectorEstimate (selectorChild I true) (values true) then
    selectorChild I false
  else
    selectorChild I true

/-- An actual value request, including the reply used by the selection rule. -/
structure SelectorCall where
  point : ℝ
  tolerance : ℝ
  value : ℝ

def selectorCall (I : SelectorInterval) (values : Fin 4 → ℝ) (q : Fin 4) :
    SelectorCall :=
  ⟨selectorQueryPoint I q, selectorTolerance I, values q⟩

/-- All four left requests followed by all four right requests; no requests
are identified or reused, even when their points coincide. -/
def selectorRoundCalls (I : SelectorInterval) (values : Bool → Fin 4 → ℝ) :
    List SelectorCall :=
  List.ofFn (selectorCall (selectorChild I false) (values false)) ++
    List.ofFn (selectorCall (selectorChild I true) (values true))

structure SelectorState where
  interval : SelectorInterval
  calls : List SelectorCall

/-- The recursive state records the exact request transcript as well as the
interval chosen from the replies in that same round. -/
noncomputable def selectorRun (n : ℕ) (δ : ℝ) (replies : SelectorReplies) :
    ℕ → SelectorState
  | 0 => ⟨selectorInitial n δ, []⟩
  | j + 1 =>
      let prior := selectorRun n δ replies j
      ⟨selectorStep prior.interval (replies j),
        prior.calls ++ selectorRoundCalls prior.interval (replies j)⟩

noncomputable def selectorIntervalAt (n : ℕ) (δ : ℝ) (replies : SelectorReplies)
    (j : ℕ) : SelectorInterval :=
  (selectorRun n δ replies j).interval

def selectorThreshold (n : ℕ) : ℕ := 16 * n ^ 3

/-- The least doubling exponent. The witness only supplies existence to
`Nat.find`; it does not change the least-threshold stopping rule. -/
def selectorK (n : ℕ) : ℕ :=
  Nat.find (show ∃ k : ℕ, selectorThreshold n ≤ 2 ^ k from
    ⟨selectorThreshold n, (selectorThreshold n).lt_two_pow_self.le⟩)

def selectorCenter (I : SelectorInterval) : ℝ := (I.left + I.right) / 2

def selectorRadius (I : SelectorInterval) : ℝ := selectorLength I / 4

noncomputable def selectorFinal (n : ℕ) (δ : ℝ) (replies : SelectorReplies) :
    SelectorInterval := selectorIntervalAt n δ replies (selectorK n)

/-- The only oracle premise: the absolute error of each actual request before
the stopping round is at most that child's length divided by 1024. -/
def SelectorReplyContract (n : ℕ) (δ : ℝ) (F : ℝ → ℝ) (replies : SelectorReplies) :
    Prop :=
  ∀ j < selectorK n, ∀ side : Bool, ∀ q : Fin 4,
    |replies j side q -
      F (selectorQueryPoint (selectorChild (selectorIntervalAt n δ replies j) side) q)| ≤
        selectorTolerance (selectorChild (selectorIntervalAt n δ replies j) side)

end KE02
