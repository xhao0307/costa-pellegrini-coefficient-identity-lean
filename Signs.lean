import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

namespace CostaPellegrini

theorem choose_add_two (u v : ℕ) :
    (u + v).choose 2 = u.choose 2 + v.choose 2 + u * v := by
  induction v with
  | zero => simp
  | succ v ih =>
      rw [Nat.add_succ, Nat.choose_succ_succ (u + v) 1,
        Nat.choose_succ_succ v 1, Nat.choose_one_right, Nat.choose_one_right, ih]
      ring

theorem reflection_sign_product (u v : ℕ) :
    (-1 : ℤ) ^ (u + v) * (-1) ^ (u.choose 2 + v.choose 2) *
      (-1) ^ (u + v + u * v) = (-1) ^ ((u + v).choose 2) := by
  rw [choose_add_two]
  have heven : (-1 : ℤ) ^ (2 * (u + v)) = 1 := by
    rw [pow_mul]
    norm_num
  calc
    _ = (-1 : ℤ) ^ (2 * (u + v)) *
        (-1) ^ (u.choose 2 + v.choose 2 + u * v) := by
          simp only [← pow_add]
          congr 1
          omega
    _ = _ := by rw [heven, one_mul]

theorem choose_two_sign_eq_floor (n : ℕ) :
    (-1 : ℤ) ^ (n.choose 2) = (-1) ^ (n / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih _ =>
      rw [choose_add_two n 2]
      norm_num only [Nat.choose_self]
      have hexp : n.choose 2 + 1 + n * 2 = 2 * n + (n.choose 2 + 1) := by omega
      rw [hexp, pow_add, pow_mul]
      norm_num only [neg_one_sq, one_pow, one_mul]
      rw [pow_add, ih]
      have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
      rw [hdiv, pow_add]

theorem reflection_sign_for_index {k : ℕ} (j : Fin k) :
    (-1 : ℤ) ^ (k - 1) *
      (-1) ^ (j.val.choose 2 + (k - 1 - j.val).choose 2) *
      (-1) ^ (k - 1 + j.val * (k - 1 - j.val)) = (-1) ^ ((k - 1) / 2) := by
  have hsum : j.val + (k - 1 - j.val) = k - 1 := by omega
  have h := reflection_sign_product j.val (k - 1 - j.val)
  rw [hsum, choose_two_sign_eq_floor] at h
  exact h

end CostaPellegrini
