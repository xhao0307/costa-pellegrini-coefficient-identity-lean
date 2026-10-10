import Definitions
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.GroupTheory.Perm.Fin

open scoped BigOperators
open MvPolynomial

namespace CostaPellegrini

noncomputable section

def permutationExponent {k : ℕ} (σ : Equiv.Perm (Fin k)) : Fin k →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i ↦ (σ i).val) (by simp)

@[simp] theorem permutationExponent_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    permutationExponent σ i = (σ i).val := by
  simp [permutationExponent]

theorem vandermonde_eq_det (k : ℕ) :
    vandermonde k = Matrix.det (Matrix.vandermonde (fun i : Fin k ↦ (X i : Poly k))) := by
  classical
  rw [Matrix.det_vandermonde]
  unfold vandermonde intervalPairs
  rw [Finset.prod_filter]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  have hset : Finset.Ioi i = Finset.univ.filter (fun j : Fin k ↦ i < j) := by
    ext j
    simp
  rw [hset, Finset.prod_filter]

theorem vandermonde_signed_expansion (k : ℕ) :
    vandermonde k = ∑ σ : Equiv.Perm (Fin k),
      monomial (permutationExponent σ) (Equiv.Perm.sign σ : ℤ) := by
  classical
  rw [vandermonde_eq_det, ← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
  rw [MvPolynomial.prod_X_pow]
  have hexp : Finsupp.indicator Finset.univ (fun i _ ↦ (σ i).val) =
      permutationExponent σ := by
    ext i
    simp [permutationExponent]
  rw [hexp]
  rw [show ((Equiv.Perm.sign σ : ℤ) : Poly k) = C (Equiv.Perm.sign σ : ℤ) by simp,
    C_mul_monomial]
  simp

def zeroAt {k : ℕ} (j : Fin k) : Poly k →ₐ[ℤ] Poly k :=
  (MvPolynomial.rename (fun i : {i : Fin k // i ≠ j} ↦ i.val)).comp
    (MvPolynomial.killCompl (f := fun i : {i : Fin k // i ≠ j} ↦ i.val)
      Subtype.val_injective)

@[simp] theorem zeroAt_X {k : ℕ} (j i : Fin k) :
    zeroAt j (X i) = if i = j then 0 else X i := by
  classical
  have hrange : (i ∈ Set.range (fun a : {a : Fin k // a ≠ j} ↦ a.val)) ↔ i ≠ j := by
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
  simp only [zeroAt, AlgHom.comp_apply, MvPolynomial.killCompl, aeval_X]
  by_cases hi : i = j
  · simp [hi]
  · rw [dite_eq_left (hrange.mpr hi), ite_eq_right hi, rename_X]
    congr 1
    exact congrArg Subtype.val
      ((Equiv.ofInjective _ Subtype.val_injective).apply_symm_apply ⟨i, hrange.mpr hi⟩)

theorem coeff_zeroAt {k : ℕ} (j : Fin k) (P : Poly k) (d : Fin k →₀ ℕ) :
    (zeroAt j P).coeff d = if d j = 0 then P.coeff d else 0 := by
  classical
  let f : {i : Fin k // i ≠ j} → Fin k := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hj : j ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact i.property hi
  by_cases hd : d j = 0
  · have hs : (↑d.support : Set (Fin k)) ⊆ Set.range f := by
      intro i hi
      refine ⟨⟨i, ?_⟩, rfl⟩
      intro heq
      subst i
      exact Finsupp.mem_support_iff.mp hi hd
    have hmap := Finsupp.mapDomain_comapDomain f hf d hs
    rw [ite_eq_left hd, ← hmap]
    change (rename f (killCompl hf P)).coeff
      ((d.comapDomain f hf.injOn).mapDomain f) = _
    rw [coeff_rename_mapDomain f hf, coeff_killCompl]
  · rw [ite_eq_right hd]
    change (rename f (killCompl hf P)).coeff d = 0
    apply coeff_rename_eq_zero
    intro u hu
    have hz := Finsupp.mapDomain_of_notMem_range u j hj
    rw [hu] at hz
    exact (hd hz).elim

theorem rotate_value {k : ℕ} (i : Fin k) :
    (finRotate k i).val = if i.val = k - 1 then 0 else i.val + 1 := by
  cases k with
  | zero => exact i.elim0
  | succ n =>
    have heq : i = Fin.last n ↔ i.val = n := by simp [Fin.ext_iff]
    simpa only [Nat.add_sub_cancel, heq] using coe_finRotate i

theorem permutationExponent_le_balanced {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    permutationExponent σ ≤ balancedExponent k := by
  intro i
  simp only [permutationExponent_apply, balancedExponent, Finsupp.onFinset_apply]
  have hi := (σ i).isLt
  omega

theorem rotated_coefficient_term {k : ℕ} (hk : 2 ≤ k) (j : Fin k)
    (σ : Equiv.Perm (Fin k)) (P : Poly k) :
    (monomial (permutationExponent (finRotate k * σ))
      (Equiv.Perm.sign (finRotate k * σ) : ℤ) * P).coeff (eExponent k j) =
    (-1 : ℤ) ^ (k - 1) *
      (monomial (permutationExponent σ) (Equiv.Perm.sign σ : ℤ) *
        zeroAt j P).coeff (balancedExponent k) := by
  classical
  have hb := permutationExponent_le_balanced σ
  rw [coeff_monomial_mul', coeff_monomial_mul', ite_eq_left hb, coeff_zeroAt]
  have hs : (Equiv.Perm.sign (finRotate k * σ) : ℤ) =
      (-1 : ℤ) ^ (k - 1) * (Equiv.Perm.sign σ : ℤ) := by
    simp
  by_cases hj : (σ j).val = k - 1
  · have hle : permutationExponent (finRotate k * σ) ≤ eExponent k j := by
      intro i
      simp only [permutationExponent_apply, Equiv.Perm.mul_apply, rotate_value,
        eExponent, Finsupp.onFinset_apply]
      by_cases hi : i = j
      · simp [hi, hj]
      · have hne : (σ i).val ≠ k - 1 := by
          intro heq
          have he : σ i = σ j := Fin.ext (heq.trans hj.symm)
          exact hi (σ.injective he)
        simp only [hne, hi, ↓reduceIte]
        have hlt := (σ i).isLt
        omega
    have hzero : (balancedExponent k - permutationExponent σ) j = 0 := by
      simp [balancedExponent, hj]
    have hdiff : eExponent k j - permutationExponent (finRotate k * σ) =
        balancedExponent k - permutationExponent σ := by
      ext i
      simp only [Finsupp.tsub_apply, eExponent, balancedExponent,
        Finsupp.onFinset_apply, permutationExponent_apply, Equiv.Perm.mul_apply,
        rotate_value]
      by_cases hi : i = j
      · simp [hi, hj]
      · have hne : (σ i).val ≠ k - 1 := by
          intro heq
          exact hi (σ.injective (Fin.ext (heq.trans hj.symm)))
        simp only [hi, hne, ↓reduceIte]
        omega
    rw [ite_eq_left hle, ite_eq_left hzero, hdiff, hs]
    ring
  · have hnle : ¬ permutationExponent (finRotate k * σ) ≤ eExponent k j := by
      intro hle
      have hlj := hle j
      simp only [permutationExponent_apply, Equiv.Perm.mul_apply, rotate_value,
        eExponent, Finsupp.onFinset_apply, hj, ↓reduceIte] at hlj
      omega
    have hnonzero : (balancedExponent k - permutationExponent σ) j ≠ 0 := by
      simp only [Finsupp.tsub_apply, balancedExponent, Finsupp.onFinset_apply,
        permutationExponent_apply]
      have hlt := (σ j).isLt
      omega
    rw [ite_eq_right hnle, ite_eq_right hnonzero]
    ring

theorem zero_coordinate_coefficient_bridge {k : ℕ} (hk : 2 ≤ k)
    (j : Fin k) (P : Poly k) :
    (vandermonde k * P).coeff (eExponent k j) =
      (-1 : ℤ) ^ (k - 1) * trace k (zeroAt j P) := by
  classical
  rw [trace, vandermonde_signed_expansion]
  simp only [Finset.sum_mul, coeff_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft (finRotate k))
    (fun σ : Equiv.Perm (Fin k) ↦
      (monomial (permutationExponent σ) (Equiv.Perm.sign σ : ℤ) * P).coeff
        (eExponent k j))]
  change (∑ σ : Equiv.Perm (Fin k),
    (monomial (permutationExponent (finRotate k * σ))
      (Equiv.Perm.sign (finRotate k * σ) : ℤ) * P).coeff (eExponent k j)) = _
  simp only [rotated_coefficient_term hk j, Finset.mul_sum]

theorem eCoefficient_eq_trace_zeroAt (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    eCoefficient k j = (-1 : ℤ) ^ (k - 1) * trace k (zeroAt j (intervalProduct k)) :=
  zero_coordinate_coefficient_bridge hk j (intervalProduct k)

theorem zeroAt_idempotent {k : ℕ} (j : Fin k) (P : Poly k) :
    zeroAt j (zeroAt j P) = zeroAt j P := by
  simp only [zeroAt, AlgHom.comp_apply, killCompl_rename_app]

theorem zero_coordinate_independent_bridge {k : ℕ} (hk : 2 ≤ k)
    (j : Fin k) (P : Poly k) (hP : zeroAt j P = P) :
    (zeroAt j (vandermonde k) * P).coeff (eExponent k j) =
      (-1 : ℤ) ^ (k - 1) * trace k P := by
  have he : eExponent k j j = 0 := by simp [eExponent]
  calc
    (zeroAt j (vandermonde k) * P).coeff (eExponent k j) =
        (zeroAt j (vandermonde k * P)).coeff (eExponent k j) := by
      rw [map_mul, hP]
    _ = (vandermonde k * P).coeff (eExponent k j) := by
      rw [coeff_zeroAt, ite_eq_left he]
    _ = (-1 : ℤ) ^ (k - 1) * trace k P := by
      rw [zero_coordinate_coefficient_bridge hk j, hP]

end

end CostaPellegrini
