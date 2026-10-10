import Transport

open scoped BigOperators
open MvPolynomial

namespace CostaPellegrini

noncomputable section

theorem rename_vandermonde {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    rename σ (vandermonde k) = C (Equiv.Perm.sign σ : ℤ) * vandermonde k := by
  classical
  rw [vandermonde_eq_det, (rename σ).map_det]
  have hmatrix : (rename σ).mapMatrix (Matrix.vandermonde (fun i : Fin k ↦ (X i : Poly k))) =
      (Matrix.vandermonde (fun i : Fin k ↦ (X i : Poly k))).submatrix σ id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [hmatrix, Matrix.det_permute, ← vandermonde_eq_det]
  simp

theorem balancedExponent_mapDomain {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (balancedExponent k).mapDomain σ = balancedExponent k := by
  classical
  ext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  rw [Finsupp.mapDomain_apply_of_injective σ.injective]
  simp [balancedExponent]

theorem trace_rename {k : ℕ} (σ : Equiv.Perm (Fin k)) (P : Poly k) :
    trace k (rename σ P) = (Equiv.Perm.sign σ : ℤ) * trace k P := by
  classical
  have hcoeff : (rename σ (vandermonde k * P)).coeff (balancedExponent k) = trace k P := by
    rw [← balancedExponent_mapDomain σ, coeff_rename_mapDomain σ σ.injective]
    rfl
  rw [map_mul, rename_vandermonde, mul_assoc, coeff_C_mul] at hcoeff
  change (Equiv.Perm.sign σ : ℤ) * trace k (rename σ P) = trace k P at hcoeff
  have hsign : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  calc
    trace k (rename σ P) =
        (Equiv.Perm.sign σ : ℤ) * ((Equiv.Perm.sign σ : ℤ) * trace k (rename σ P)) := by
          rw [← mul_assoc, hsign, one_mul]
    _ = _ := by rw [hcoeff]

end

end CostaPellegrini
