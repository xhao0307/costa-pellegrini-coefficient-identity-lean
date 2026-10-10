import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators
open MvPolynomial

namespace CostaPellegrini

noncomputable section

abbrev Poly (k : ℕ) := MvPolynomial (Fin k) ℤ

def intervalPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun p ↦ p.1 < p.2

def intervalSum {k : ℕ} (a b : Fin k) : Poly k :=
  ∑ i ∈ Finset.Icc a b, X i

def totalSum (k : ℕ) : Poly k := ∑ i, X i

def vandermonde (k : ℕ) : Poly k :=
  ∏ p ∈ intervalPairs k, (X p.2 - X p.1)

def intervalProduct (k : ℕ) : Poly k :=
  ∏ p ∈ intervalPairs k, intervalSum p.1 p.2

-- Delete the full-interval factor as a polynomial, before any evaluation.
def deletedIntervalProduct (k : ℕ) : Poly k :=
  ∏ p ∈ (intervalPairs k).filter (fun p ↦ ¬ (p.1.val = 0 ∧ p.2.val + 1 = k)),
    intervalSum p.1 p.2

def balancedExponent (k : ℕ) : Fin k →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ ↦ k - 1) (by simp)

def cExponent (k : ℕ) (j : Fin k) : Fin k →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i ↦ if i = j then k - 2 else k - 1) (by simp)

def eExponent (k : ℕ) (j : Fin k) : Fin k →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i ↦ if i = j then 0 else k) (by simp)

def cCoefficient (k : ℕ) (j : Fin k) : ℤ :=
  (vandermonde k * deletedIntervalProduct k).coeff (cExponent k j)

def eCoefficient (k : ℕ) (j : Fin k) : ℤ :=
  (vandermonde k * intervalProduct k).coeff (eExponent k j)

def trace (k : ℕ) (P : Poly k) : ℤ :=
  (vandermonde k * P).coeff (balancedExponent k)

theorem intervalSum_full (k : ℕ) (hk : 2 ≤ k) :
    intervalSum (⟨0, by omega⟩ : Fin k) ⟨k - 1, by omega⟩ = totalSum k := by
  have hset : Finset.Icc (⟨0, by omega⟩ : Fin k) ⟨k - 1, by omega⟩ =
      Finset.univ := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_univ, iff_true, Fin.le_iff_val_le_val]
    constructor <;> omega
  simp [intervalSum, totalSum, hset]

theorem intervalProduct_eq_totalSum_mul_deleted (k : ℕ) (hk : 2 ≤ k) :
    intervalProduct k = totalSum k * deletedIntervalProduct k := by
  classical
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨k - 1, by omega⟩
  have hab : (a, b) ∈ intervalPairs k := by
    simp only [intervalPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.lt_def]
    dsimp [a, b]
    omega
  have hfull (p : Fin k × Fin k) :
      (p.1.val = 0 ∧ p.2.val + 1 = k) ↔ p = (a, b) := by
    constructor
    · rintro ⟨ha, hb⟩
      apply Prod.ext <;> apply Fin.ext
      · exact ha
      · dsimp [b]
        omega
    · rintro rfl
      dsimp [a, b]
      omega
  have hfilter :
      (intervalPairs k).filter (fun p ↦ ¬ (p.1.val = 0 ∧ p.2.val + 1 = k)) =
      (intervalPairs k).erase (a, b) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, hfull]
    exact and_comm
  have hsum : intervalSum a b = totalSum k := intervalSum_full k hk
  rw [intervalProduct, ← Finset.mul_prod_erase _ _ hab, hsum]
  simp only [deletedIntervalProduct, hfilter]

theorem trace_X_mul_deleted_eq_c (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    trace k (X j * deletedIntervalProduct k) = cCoefficient k j := by
  classical
  have hexp : cExponent k j + Finsupp.single j 1 = balancedExponent k := by
    ext i
    simp only [cExponent, balancedExponent, Finsupp.add_apply,
      Finsupp.onFinset_apply, Finsupp.single_apply]
    split_ifs <;> omega
  rw [trace, cCoefficient, show vandermonde k * (X j * deletedIntervalProduct k) =
    X j * (vandermonde k * deletedIntervalProduct k) by ring, ← hexp]
  simpa only [add_comm] using
    (MvPolynomial.coeff_X_mul (cExponent k j) j
      (vandermonde k * deletedIntervalProduct k))

end

end CostaPellegrini
