import KE02.ContinuantStatement
import Mathlib.Tactic

noncomputable section

namespace KE02

open Polynomial

theorem det_tridiag {R : Type*} [CommRing R] (a b c : ℕ → R) :
    ∀ k, (tridiag k a b c).det = continuant a b c k
  | 0 => by simp [continuant]
  | 1 => by simp [continuant, tridiag, Matrix.det_unique]
  | k + 2 => by
    have h1 := det_tridiag a b c (k + 1)
    have h0 := det_tridiag a b c k
    rw [Matrix.det_succ_row _ (Fin.last (k + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hzero : ∑ j : Fin k, (-1 : R) ^ ((Fin.last (k + 1) : ℕ) + (j.castSucc.castSucc : ℕ)) *
        tridiag (k + 2) a b c (Fin.last (k + 1)) j.castSucc.castSucc *
        ((tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
          j.castSucc.castSucc.succAbove).det = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have : tridiag (k + 2) a b c (Fin.last (k + 1)) j.castSucc.castSucc = 0 := by
        simp only [tridiag, Fin.val_last, Fin.val_castSucc]
        have := j.isLt
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [this, mul_zero, zero_mul]
    rw [hzero, zero_add]
    have hlast : (tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
        (Fin.last (k + 1)).succAbove = tridiag (k + 1) a b c := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, tridiag, Fin.val_castSucc]
    have hcol : ((tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
        (Fin.last k).castSucc.succAbove).det = b k * continuant a b c k := by
      rw [Matrix.det_succ_column _ (Fin.last k), Fin.sum_univ_castSucc]
      have hz : ∑ i : Fin k, (-1 : R) ^ ((i.castSucc : ℕ) + (Fin.last k : ℕ)) *
          ((tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
            (Fin.last k).castSucc.succAbove) i.castSucc (Fin.last k) *
          (((tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
            (Fin.last k).castSucc.succAbove).submatrix i.castSucc.succAbove
              (Fin.last k).succAbove).det = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have : ((tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
            (Fin.last k).castSucc.succAbove) i.castSucc (Fin.last k) = 0 := by
          simp only [Matrix.submatrix_apply, Fin.succAbove_last]
          rw [Fin.succAbove_of_le_castSucc _ _ le_rfl]
          simp only [tridiag, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
          have := i.isLt
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [this, mul_zero, zero_mul]
      rw [hz, zero_add]
      have e₁ : ((tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
          (Fin.last k).castSucc.succAbove) (Fin.last k) (Fin.last k) = b k := by
        simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        rw [Fin.succAbove_of_le_castSucc _ _ le_rfl]
        simp only [tridiag, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
        rw [ite_eq_right (by omega)]
        simp
      have e₂ : ((tridiag (k + 2) a b c).submatrix (Fin.last (k + 1)).succAbove
          (Fin.last k).castSucc.succAbove).submatrix (Fin.last k).succAbove
            (Fin.last k).succAbove = tridiag k a b c := by
        ext i j
        simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
        simp only [tridiag, Fin.val_castSucc]
      rw [e₁, e₂, h0]
      simp only [Fin.val_last]
      rw [show (-1 : R) ^ (k + k) = 1 by rw [← two_mul, pow_mul]; simp]
      ring
    have hd : tridiag (k + 2) a b c (Fin.last (k + 1)) (Fin.last (k + 1)) = a (k + 1) := by
      simp [tridiag]
    have ho : tridiag (k + 2) a b c (Fin.last (k + 1)) (Fin.last k).castSucc = c k := by
      simp only [tridiag, Fin.val_castSucc, Fin.val_last]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    rw [hlast, hcol, hd, ho, h1]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [show (-1 : R) ^ (k + 1 + k) = -1 by
      rw [show k + 1 + k = 2 * k + 1 by ring, pow_succ, pow_mul]; simp,
      show (-1 : R) ^ (k + 1 + (k + 1)) = 1 by
      rw [show k + 1 + (k + 1) = 2 * (k + 1) by ring, pow_mul]; simp]
    simp only [continuant]
    ring

theorem charMatrix_eq_tridiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → A i j = 0) :
    Matrix.diagonal (fun _ => (X : ℝ[X])) + Matrix.diagonal (fun _ => (2 : ℝ[X])) + A.map C =
      tridiag n (fun i => X + C (2 + diagEntry A i)) (fun i => C (superEntry A i))
        (fun i => C (subEntry A i)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.map_apply, tridiag]
  by_cases hij : (i : ℕ) = j
  · have e : i = j := Fin.ext hij
    subst e
    simp only [ite_true, diagEntry, dite_eq_left i.isLt, Fin.eta]
    rw [map_add, map_ofNat]
    ring_nf
  · have hne : i ≠ j := fun e => hij (congrArg Fin.val e)
    rw [ite_eq_right hne, ite_eq_right hne, ite_eq_right hij]
    by_cases hsup : (j : ℕ) = i + 1
    · rw [ite_eq_left hsup]
      simp only [superEntry, dite_eq_left (show (i : ℕ) + 1 < n by have := j.isLt; omega)]
      have : (⟨i + 1, by omega⟩ : Fin n) = j := Fin.ext hsup.symm
      rw [this]
      simp
    · rw [ite_eq_right hsup]
      by_cases hsub : (i : ℕ) = j + 1
      · rw [ite_eq_left hsub]
        simp only [subEntry, dite_eq_left (show (j : ℕ) + 1 < n by have := i.isLt; omega)]
        have : (⟨j + 1, by omega⟩ : Fin n) = i := Fin.ext hsub.symm
        rw [this]
        simp
      · rw [ite_eq_right hsub, hA i j (by omega)]
        simp

theorem continuant_eq_charRecurrence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ k, continuant (fun i => X + C (2 + diagEntry A i)) (fun i => C (superEntry A i))
      (fun i => C (subEntry A i)) k = charRecurrence A k
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    rw [continuant, charRecurrence, continuant_eq_charRecurrence A (k + 1),
      continuant_eq_charRecurrence A k, map_mul]

theorem det_char (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → A i j = 0) :
    (Matrix.diagonal (fun _ => (X : ℝ[X])) + Matrix.diagonal (fun _ => (2 : ℝ[X])) +
      A.map C).det = charRecurrence A n := by
  rw [charMatrix_eq_tridiag A hA, det_tridiag, continuant_eq_charRecurrence]

theorem symmetric_coeff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose = A) (i : ℕ) :
    superEntry A i * subEntry A i = superEntry A i ^ 2 := by
  unfold superEntry subEntry
  split_ifs with h
  · have := congrFun (congrFun hA ⟨i, by omega⟩) ⟨i + 1, h⟩
    rw [Matrix.transpose_apply] at this
    rw [this, sq]
  · ring

theorem continuantCertificate : ContinuantCertificate where
  det_tridiag := fun _ _ a b c k => det_tridiag a b c k
  det_char := det_char
  symmetric_coeff := symmetric_coeff

end KE02
