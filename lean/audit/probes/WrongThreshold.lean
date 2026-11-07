import KE02

open KE02

example : alg2K 2 = 7 := by rw [alg2K, Nat.find_eq_iff]; decide

example : alg2K 2 = 6 := by rw [alg2K, Nat.find_eq_iff]; decide
