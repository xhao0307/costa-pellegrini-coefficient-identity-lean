import Annihilation
import Boundary
import Covariance
import Signs

open MvPolynomial

namespace CostaPellegrini

noncomputable section

theorem trace_sub (k : ℕ) (P Q : Poly k) :
    trace k (P - Q) = trace k P - trace k Q := by
  simp [trace, mul_sub]

theorem trace_C_mul (k : ℕ) (a : ℤ) (P : Poly k) :
    trace k (C a * P) = a * trace k P := by
  unfold trace
  rw [show vandermonde k * (C a * P) = C a * (vandermonde k * P) by ring,
    coeff_C_mul]

theorem coefficient_identity {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    eCoefficient k j = (-1 : ℤ) ^ ((k - 1) / 2) * cCoefficient k j := by
  obtain ⟨Q, hQ⟩ := exists_boundary_multiplier hk j
  have htrace := congrArg (trace k) hQ
  rw [trace_sub, trace_rename, trace_C_mul, trace_X_mul_deleted_eq_c k hk j,
    trace_totalSum_mul] at htrace
  have heq : (Equiv.Perm.sign (blockReverse j) : ℤ) *
      trace k (zeroAt j (intervalProduct k)) =
      (-1 : ℤ) ^ (k - 1 + j.val * (k - 1 - j.val)) * cCoefficient k j :=
    sub_eq_zero.mp htrace
  have hs : (Equiv.Perm.sign (blockReverse j) : ℤ) *
      (Equiv.Perm.sign (blockReverse j) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (blockReverse j)) with h | h <;> simp [h]
  have ht : trace k (zeroAt j (intervalProduct k)) =
      (Equiv.Perm.sign (blockReverse j) : ℤ) *
      ((-1 : ℤ) ^ (k - 1 + j.val * (k - 1 - j.val)) * cCoefficient k j) := by
    calc
      _ = (Equiv.Perm.sign (blockReverse j) : ℤ) *
          ((Equiv.Perm.sign (blockReverse j) : ℤ) *
            trace k (zeroAt j (intervalProduct k))) := by
              rw [← mul_assoc, hs, one_mul]
      _ = _ := by rw [heq]
  calc
    eCoefficient k j = (-1 : ℤ) ^ (k - 1) *
        trace k (zeroAt j (intervalProduct k)) := eCoefficient_eq_trace_zeroAt k hk j
    _ = ((-1 : ℤ) ^ (k - 1) * (Equiv.Perm.sign (blockReverse j) : ℤ) *
        (-1) ^ (k - 1 + j.val * (k - 1 - j.val))) * cCoefficient k j := by
          rw [ht]
          ring
    _ = _ := by rw [sign_blockReverse, reflection_sign_for_index]

end

end CostaPellegrini
