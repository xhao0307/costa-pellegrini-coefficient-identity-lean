import Reflection
import PrefixProduct
import IntervalBijection
import Mathlib.RingTheory.Ideal.Quotient.Defs

open scoped BigOperators
open MvPolynomial

namespace CostaPellegrini

noncomputable section

theorem zeroAt_rename_of_fixed {k : ℕ} (j : Fin k) (σ : Equiv.Perm (Fin k))
    (hj : σ j = j) (P : Poly k) :
    zeroAt j (rename σ P) = rename σ (zeroAt j P) := by
  classical
  have heq (i : Fin k) : σ i = j ↔ i = j := by
    constructor
    · intro h
      exact σ.injective (h.trans hj.symm)
    · rintro rfl
      exact hj
  have hcomm : (zeroAt j).comp (rename σ) = (rename σ).comp (zeroAt j) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, zeroAt_X, heq]
    by_cases hi : i = j <;> simp [hi]
  exact AlgHom.congr_fun hcomm P

theorem zeroAt_blockReverse_rename {k : ℕ} (j : Fin k) (P : Poly k) :
    zeroAt j (rename (blockReverse j) P) = rename (blockReverse j) (zeroAt j P) :=
  zeroAt_rename_of_fixed j (blockReverse j) (blockReverse_apply_eq j) P

theorem mem_transformed_left {k : ℕ} (j a b q : Fin k) (hab : a ≤ b) (hb : b < j) :
    q ∈ Finset.Icc (segmentTransform j a b hab).1 (segmentTransform j a b hab).2 ↔
      a ≤ blockReverse j q ∧ blockReverse j q ≤ b ∧ q ≠ j := by
  obtain ⟨h1, h2⟩ := segmentTransform_left_values j a b hab hb
  simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
  rw [h1, h2]
  have hav : a.val ≤ b.val := hab
  have hbv : b.val < j.val := hb
  by_cases hq : q < j
  · rw [blockReverse_apply_lt j q hq]
    have hqv : q.val < j.val := hq
    have hne : q ≠ j := ne_of_lt hq
    omega
  · by_cases heq : q = j
    · subst q
      rw [blockReverse_apply_eq]
      omega
    · have hgt : j < q := lt_of_le_of_ne (le_of_not_gt hq) (fun h ↦ heq h.symm)
      rw [blockReverse_apply_gt j q hgt]
      have hqv : j.val < q.val := hgt
      have hqk := q.isLt
      omega

theorem mem_transformed_right {k : ℕ} (j a b q : Fin k) (hab : a ≤ b) (ha : j < a) :
    q ∈ Finset.Icc (segmentTransform j a b hab).1 (segmentTransform j a b hab).2 ↔
      a ≤ blockReverse j q ∧ blockReverse j q ≤ b ∧ q ≠ j := by
  obtain ⟨h1, h2⟩ := segmentTransform_right_values j a b hab ha
  simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
  rw [h1, h2]
  have hav : j.val < a.val := ha
  have habv : a.val ≤ b.val := hab
  have hbk := b.isLt
  by_cases hq : q < j
  · rw [blockReverse_apply_lt j q hq]
    have hqv : q.val < j.val := hq
    omega
  · by_cases heq : q = j
    · subst q
      rw [blockReverse_apply_eq]
      omega
    · have hgt : j < q := lt_of_le_of_ne (le_of_not_gt hq) (fun h ↦ heq h.symm)
      rw [blockReverse_apply_gt j q hgt]
      have hqv : j.val < q.val := hgt
      have hqk := q.isLt
      omega

theorem mem_transformed_cross {k : ℕ} (j a b q : Fin k) (hab : a ≤ b)
    (ha : a ≤ j) (hb : j ≤ b) :
    q ∈ Finset.Icc (segmentTransform j a b hab).1 (segmentTransform j a b hab).2 ↔
      ¬ (a ≤ blockReverse j q ∧ blockReverse j q ≤ b ∧ q ≠ j) := by
  obtain ⟨h1, h2⟩ := segmentTransform_cross_values j a b hab ha hb
  simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
  rw [h1, h2]
  have hav : a.val ≤ j.val := ha
  have hbv : j.val ≤ b.val := hb
  have hbk := b.isLt
  by_cases hq : q < j
  · rw [blockReverse_apply_lt j q hq]
    have hqv : q.val < j.val := hq
    have hne : q ≠ j := ne_of_lt hq
    omega
  · by_cases heq : q = j
    · subst q
      rw [blockReverse_apply_eq]
      omega
    · have hgt : j < q := lt_of_le_of_ne (le_of_not_gt hq) (fun h ↦ heq h.symm)
      rw [blockReverse_apply_gt j q hgt]
      have hqv : j.val < q.val := hgt
      have hqk := q.isLt
      omega

theorem intervalSum_eq_univ_sum {k : ℕ} (a b : Fin k) :
    intervalSum a b = ∑ q : Fin k, if q ∈ Finset.Icc a b then X q else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (fun q : Fin k ↦ q ∈ Finset.Icc a b) =
      Finset.Icc a b := by ext q; simp
  rw [hset]
  rfl

theorem reflected_zero_interval_eq_sum {k : ℕ} {R : Type*} [CommRing R]
    (Φ : Poly k →+* R) (j a b : Fin k) :
    Φ (rename (blockReverse j) (zeroAt j (intervalSum a b))) =
      ∑ q : Fin k, if a ≤ blockReverse j q ∧ blockReverse j q ≤ b ∧ q ≠ j then
        Φ (X q) else 0 := by
  classical
  rw [intervalSum_eq_univ_sum]
  simp only [map_sum, apply_ite, map_zero, zeroAt_X, rename_X]
  rw [← Equiv.sum_comp (blockReverse j)
    (fun i : Fin k ↦ if i ∈ Finset.Icc a b then
      if i = j then 0 else Φ (X (blockReverse j i)) else 0)]
  apply Finset.sum_congr rfl
  intro q hq
  have heq : blockReverse j q = j ↔ q = j := by
    constructor
    · intro h
      exact (blockReverse j).injective (h.trans (blockReverse_apply_eq j).symm)
    · intro h
      simpa only [h] using blockReverse_apply_eq j
  simp only [Finset.mem_Icc, blockReverse_involutive j q, heq]
  split_ifs <;> simp_all

theorem interval_factor_left {k : ℕ} {R : Type*} [CommRing R]
    (Φ : Poly k →+* R) (j a b : Fin k) (hab : a ≤ b) (hb : b < j) :
    Φ (rename (blockReverse j) (zeroAt j (intervalSum a b))) =
      Φ (intervalSum (segmentTransform j a b hab).1 (segmentTransform j a b hab).2) := by
  classical
  rw [reflected_zero_interval_eq_sum, intervalSum_eq_univ_sum]
  simp only [map_sum, apply_ite, map_zero, mem_transformed_left j a b _ hab hb]

theorem interval_factor_right {k : ℕ} {R : Type*} [CommRing R]
    (Φ : Poly k →+* R) (j a b : Fin k) (hab : a ≤ b) (ha : j < a) :
    Φ (rename (blockReverse j) (zeroAt j (intervalSum a b))) =
      Φ (intervalSum (segmentTransform j a b hab).1 (segmentTransform j a b hab).2) := by
  classical
  rw [reflected_zero_interval_eq_sum, intervalSum_eq_univ_sum]
  simp only [map_sum, apply_ite, map_zero, mem_transformed_right j a b _ hab ha]

theorem interval_factor_cross_add {k : ℕ} {R : Type*} [CommRing R]
    (Φ : Poly k →+* R) (j a b : Fin k) (hab : a ≤ b) (ha : a ≤ j) (hb : j ≤ b) :
    Φ (rename (blockReverse j) (zeroAt j (intervalSum a b))) +
      Φ (intervalSum (segmentTransform j a b hab).1 (segmentTransform j a b hab).2) =
        Φ (totalSum k) := by
  classical
  rw [reflected_zero_interval_eq_sum, intervalSum_eq_univ_sum]
  simp only [map_sum, apply_ite, map_zero, mem_transformed_cross j a b _ hab ha hb,
    totalSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> simp_all

theorem interval_factor_transport {k : ℕ} {R : Type*} [CommRing R]
    (Φ : Poly k →+* R) (hΦ : Φ (totalSum k) = 0)
    (j a b : Fin k) (hab : a ≤ b) :
    Φ (rename (blockReverse j) (zeroAt j (intervalSum a b))) =
      (if a ≤ j ∧ j ≤ b then -1 else 1) *
        Φ (intervalSum (segmentTransform j a b hab).1 (segmentTransform j a b hab).2) := by
  classical
  by_cases hb : b < j
  · have hn : ¬ (a ≤ j ∧ j ≤ b) := by omega
    rw [ite_eq_right hn, one_mul]
    exact interval_factor_left Φ j a b hab hb
  · by_cases ha : j < a
    · have hn : ¬ (a ≤ j ∧ j ≤ b) := by omega
      rw [ite_eq_right hn, one_mul]
      exact interval_factor_right Φ j a b hab ha
    · have haj : a ≤ j := le_of_not_gt ha
      have hjb : j ≤ b := le_of_not_gt hb
      rw [ite_eq_left ⟨haj, hjb⟩, neg_one_mul]
      have h := interval_factor_cross_add Φ j a b hab haj hjb
      rw [hΦ] at h
      exact eq_neg_of_add_eq_zero_left h

theorem prod_crossing_sign_card {k : ℕ} {R : Type*} [CommRing R] (j : Fin k) :
    (∏ p ∈ strictSegments k,
      (if p.val.1 ≤ j ∧ j ≤ p.val.2 then (-1 : R) else 1)) =
    (-1 : R) ^ ((strictSegments k).filter (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card := by
  classical
  rw [← Finset.prod_filter, Finset.prod_const]

theorem boundary_map_card {k : ℕ} (hk : 2 ≤ k) {R : Type*} [CommRing R]
    (Φ : Poly k →+* R) (hΦ : Φ (totalSum k) = 0) (j : Fin k) :
    Φ (rename (blockReverse j) (zeroAt j (intervalProduct k))) =
      (-1 : R) ^ ((strictSegments k).filter (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card *
        Φ (X j * deletedIntervalProduct k) := by
  classical
  rw [intervalProduct_eq_segment_prod]
  simp only [map_prod]
  have hterm (p : Segment k) :
      Φ (rename (blockReverse j) (zeroAt j (intervalSum p.val.1 p.val.2))) =
        (if p.val.1 ≤ j ∧ j ≤ p.val.2 then (-1 : R) else 1) *
          Φ (intervalSum (segmentPermutation j p).val.1 (segmentPermutation j p).val.2) := by
    exact interval_factor_transport Φ hΦ j p.val.1 p.val.2 p.property
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, prod_crossing_sign_card,
    product_reflected_segments hk j (fun p ↦ Φ (intervalSum p.val.1 p.val.2))]
  have hc : intervalSum (centerSegment j).val.1 (centerSegment j).val.2 = X j := by
    simp [intervalSum, centerSegment]
  rw [hc, map_mul, deletedIntervalProduct_eq_segment_prod, map_prod]

theorem exists_boundary_multiplier_card {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    ∃ Q : Poly k,
      rename (blockReverse j) (zeroAt j (intervalProduct k)) -
        C ((-1 : ℤ) ^
          ((strictSegments k).filter (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card) *
            (X j * deletedIntervalProduct k) = totalSum k * Q := by
  classical
  let I : Ideal (Poly k) := Ideal.span {totalSum k}
  let Φ : Poly k →+* (Poly k ⧸ I) := Ideal.Quotient.mk I
  have hΦ : Φ (totalSum k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have heq := boundary_map_card hk Φ hΦ j
  have hz : Φ (rename (blockReverse j) (zeroAt j (intervalProduct k)) -
      C ((-1 : ℤ) ^
        ((strictSegments k).filter (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card) *
          (X j * deletedIntervalProduct k)) = 0 := by
    rw [map_sub, map_mul]
    have hC : Φ (C ((-1 : ℤ) ^
        ((strictSegments k).filter (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card)) =
      (-1 : (Poly k ⧸ I)) ^
        ((strictSegments k).filter (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card := by
      simp
    rw [hC, heq, sub_self]
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨Q, by simpa only [mul_comm] using hQ.symm⟩

theorem boundary_map {k : ℕ} (hk : 2 ≤ k) {R : Type*} [CommRing R]
    (Φ : Poly k →+* R) (hΦ : Φ (totalSum k) = 0) (j : Fin k) :
    Φ (rename (blockReverse j) (zeroAt j (intervalProduct k))) =
      (-1 : R) ^ (k - 1 + j.val * (k - 1 - j.val)) *
        Φ (X j * deletedIntervalProduct k) := by
  simpa only [crossingSegments_card] using boundary_map_card hk Φ hΦ j

theorem exists_boundary_multiplier {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    ∃ Q : Poly k,
      rename (blockReverse j) (zeroAt j (intervalProduct k)) -
        C ((-1 : ℤ) ^ (k - 1 + j.val * (k - 1 - j.val))) *
          (X j * deletedIntervalProduct k) = totalSum k * Q := by
  simpa only [crossingSegments_card] using exists_boundary_multiplier_card hk j

theorem exists_boundary_multiplier_zeroAt_rename {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    ∃ Q : Poly k,
      zeroAt j (rename (blockReverse j) (intervalProduct k)) -
        C ((-1 : ℤ) ^ (k - 1 + j.val * (k - 1 - j.val))) *
          (X j * deletedIntervalProduct k) = totalSum k * Q := by
  rw [zeroAt_blockReverse_rename]
  exact exists_boundary_multiplier hk j

end

end CostaPellegrini
