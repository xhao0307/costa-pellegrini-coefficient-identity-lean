import Transport

open scoped BigOperators
open MvPolynomial

namespace CostaPellegrini

noncomputable section

def advanceIndex {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) : Fin k :=
  σ.symm (finRotate k (σ i))

def adjacentPermutation {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    Equiv.Perm (Fin k) := σ * Equiv.swap i (advanceIndex σ i)

@[simp] theorem apply_advanceIndex {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    σ (advanceIndex σ i) = finRotate k (σ i) := by
  simp [advanceIndex]

@[simp] theorem adjacentPermutation_at {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    adjacentPermutation σ i i = σ (advanceIndex σ i) := by
  simp [adjacentPermutation, Equiv.Perm.mul_apply]

@[simp] theorem adjacentPermutation_advance {k : ℕ} (σ : Equiv.Perm (Fin k))
    (i : Fin k) : adjacentPermutation σ i (advanceIndex σ i) = σ i := by
  simp [adjacentPermutation, Equiv.Perm.mul_apply]

@[simp] theorem advanceIndex_adjacent {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    advanceIndex (adjacentPermutation σ i) (advanceIndex σ i) = i := by
  apply (adjacentPermutation σ i).injective
  rw [apply_advanceIndex, adjacentPermutation_advance, adjacentPermutation_at,
    apply_advanceIndex]

def annihilationPartner {k : ℕ} (a : Equiv.Perm (Fin k) × Fin k) :
    Equiv.Perm (Fin k) × Fin k :=
  (adjacentPermutation a.1 a.2, advanceIndex a.1 a.2)

theorem annihilationPartner_involutive {k : ℕ} :
    Function.Involutive (@annihilationPartner k) := by
  rintro ⟨σ, i⟩
  apply Prod.ext
  · change adjacentPermutation σ i *
      Equiv.swap (advanceIndex σ i)
        (advanceIndex (adjacentPermutation σ i) (advanceIndex σ i)) = σ
    rw [advanceIndex_adjacent, adjacentPermutation]
    rw [Equiv.swap_comm (advanceIndex σ i) i, mul_assoc, Equiv.swap_mul_self, mul_one]
  · exact advanceIndex_adjacent σ i

def incrementExponent {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) : Fin k →₀ ℕ :=
  permutationExponent σ + Finsupp.single i 1

def annihilationWeight {k : ℕ} (Q : Poly k) (a : Equiv.Perm (Fin k) × Fin k) : ℤ :=
  (monomial (incrementExponent a.1 a.2) (Equiv.Perm.sign a.1 : ℤ) * Q).coeff
    (balancedExponent k)

theorem annihilationWeight_top {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k)
    (Q : Poly k) (h : (σ i).val = k - 1) : annihilationWeight Q (σ, i) = 0 := by
  classical
  have hnle : ¬ incrementExponent σ i ≤ balancedExponent k := by
    intro hle
    have hi := hle i
    simp only [incrementExponent, Finsupp.add_apply, permutationExponent_apply,
      Finsupp.single_eq_same, balancedExponent, Finsupp.onFinset_apply, h] at hi
    omega
  simp only [annihilationWeight, coeff_monomial_mul', ite_eq_right hnle]

theorem advanceIndex_ne_of_not_top {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k)
    (h : (σ i).val ≠ k - 1) : advanceIndex σ i ≠ i := by
  intro heq
  have hv := congrArg Fin.val (apply_advanceIndex σ i)
  rw [heq, rotate_value, ite_eq_right h] at hv
  omega

theorem incrementExponent_adjacent {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k)
    (h : (σ i).val ≠ k - 1) :
    incrementExponent (adjacentPermutation σ i) (advanceIndex σ i) =
      incrementExponent σ i := by
  classical
  have hne := advanceIndex_ne_of_not_top σ i h
  have hv : (σ (advanceIndex σ i)).val = (σ i).val + 1 := by
    rw [apply_advanceIndex, rotate_value, ite_eq_right h]
  ext q
  simp only [incrementExponent, Finsupp.add_apply, permutationExponent_apply]
  by_cases hqi : q = i
  · subst q
    rw [adjacentPermutation_at, hv]
    simp [hne]
  · by_cases hql : q = advanceIndex σ i
    · subst q
      rw [adjacentPermutation_advance, hv]
      simp [hne]
    · have hfix : adjacentPermutation σ i q = σ q := by
        simp [adjacentPermutation, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hqi hql]
      rw [hfix]
      simp [hqi, hql]

theorem annihilationWeight_add_partner {k : ℕ} (Q : Poly k)
    (a : Equiv.Perm (Fin k) × Fin k) :
    annihilationWeight Q a + annihilationWeight Q (annihilationPartner a) = 0 := by
  classical
  rcases a with ⟨σ, i⟩
  by_cases ht : (σ i).val = k - 1
  · have ht' : (adjacentPermutation σ i (advanceIndex σ i)).val = k - 1 := by
      rw [adjacentPermutation_advance, ht]
    rw [annihilationWeight_top σ i Q ht]
    change 0 + annihilationWeight Q (adjacentPermutation σ i, advanceIndex σ i) = 0
    rw [annihilationWeight_top _ _ Q ht', add_zero]
  · have hne := advanceIndex_ne_of_not_top σ i ht
    have hs : (Equiv.Perm.sign (adjacentPermutation σ i) : ℤ) =
        -(Equiv.Perm.sign σ : ℤ) := by
      simp [adjacentPermutation, Equiv.Perm.sign_swap hne.symm]
    simp only [annihilationWeight, annihilationPartner,
      incrementExponent_adjacent σ i ht, hs, map_neg, neg_mul, coeff_neg]
    exact add_neg_cancel _

theorem annihilationPartner_ne_of_weight_ne_zero {k : ℕ} (Q : Poly k)
    (a : Equiv.Perm (Fin k) × Fin k) (h : annihilationWeight Q a ≠ 0) :
    annihilationPartner a ≠ a := by
  rcases a with ⟨σ, i⟩
  have ht : (σ i).val ≠ k - 1 := fun he ↦ h (annihilationWeight_top σ i Q he)
  intro heq
  exact advanceIndex_ne_of_not_top σ i ht (congrArg Prod.snd heq)

theorem trace_totalSum_mul_eq_weight_sum (k : ℕ) (Q : Poly k) :
    trace k (totalSum k * Q) =
      ∑ a : Equiv.Perm (Fin k) × Fin k, annihilationWeight Q a := by
  classical
  rw [trace, vandermonde_signed_expansion, totalSum]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum, coeff_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro i hi
  simp only [annihilationWeight, incrementExponent, ← mul_assoc, X,
    monomial_mul_monomial, mul_one]

theorem trace_totalSum_mul (k : ℕ) (Q : Poly k) : trace k (totalSum k * Q) = 0 := by
  classical
  rw [trace_totalSum_mul_eq_weight_sum]
  exact Finset.sum_involution (fun a _ ↦ annihilationPartner a)
    (fun a _ ↦ annihilationWeight_add_partner Q a)
    (fun a _ h ↦ annihilationPartner_ne_of_weight_ne_zero Q a h)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun a _ ↦ annihilationPartner_involutive a)

end

end CostaPellegrini
