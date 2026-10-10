import PrefixProduct

open scoped BigOperators

namespace CostaPellegrini

abbrev Segment (k : ℕ) := {p : Fin k × Fin k // p.1 ≤ p.2}

def segmentReflectionFun {k : ℕ} (j : Fin k) (p : Segment k) : Segment k :=
  ⟨segmentTransform j p.val.1 p.val.2 p.property,
    segmentTransform_valid j p.val.1 p.val.2 p.property⟩

theorem segmentReflectionFun_involutive {k : ℕ} (j : Fin k) :
    Function.Involutive (segmentReflectionFun j) := by
  rintro ⟨⟨a, b⟩, hab⟩
  apply Subtype.ext
  exact segmentTransform_involutive j a b hab

def segmentPermutation {k : ℕ} (j : Fin k) : Equiv.Perm (Segment k) :=
  Function.Involutive.toPerm (segmentReflectionFun j) (segmentReflectionFun_involutive j)

def centerSegment {k : ℕ} (j : Fin k) : Segment k := ⟨(j, j), le_rfl⟩

def strictSegments (k : ℕ) : Finset (Segment k) :=
  Finset.univ.filter fun p ↦ p.val.1 < p.val.2

def deletedSegments (k : ℕ) : Finset (Segment k) :=
  (strictSegments k).filter fun p ↦ ¬ (p.val.1.val = 0 ∧ p.val.2.val + 1 = k)

theorem segmentTransform_equal_iff {k : ℕ} (j a b : Fin k) (hab : a ≤ b) :
    (segmentTransform j a b hab).1 = (segmentTransform j a b hab).2 ↔
      (a = b ∧ a ≠ j) ∨ (a.val = 0 ∧ b.val + 1 = k) := by
  by_cases hb : b < j
  · obtain ⟨h1, h2⟩ := segmentTransform_left_values j a b hab hb
    rw [Fin.ext_iff, h1, h2]
    simp only [Fin.ext_iff, Fin.lt_def] at *
    omega
  · by_cases ha : j < a
    · obtain ⟨h1, h2⟩ := segmentTransform_right_values j a b hab ha
      rw [Fin.ext_iff, h1, h2]
      simp only [Fin.ext_iff, Fin.lt_def] at *
      omega
    · obtain ⟨h1, h2⟩ := segmentTransform_cross_values j a b hab
        (le_of_not_gt ha) (le_of_not_gt hb)
      rw [Fin.ext_iff, h1, h2]
      simp only [Fin.ext_iff, Fin.lt_def] at *
      omega

theorem segmentTransform_full_iff {k : ℕ} (j a b : Fin k) (hab : a ≤ b) :
    ((segmentTransform j a b hab).1.val = 0 ∧
      (segmentTransform j a b hab).2.val + 1 = k) ↔ a = j ∧ b = j := by
  by_cases hb : b < j
  · obtain ⟨h1, h2⟩ := segmentTransform_left_values j a b hab hb
    rw [h1, h2]
    simp only [Fin.ext_iff, Fin.lt_def] at *
    omega
  · by_cases ha : j < a
    · obtain ⟨h1, h2⟩ := segmentTransform_right_values j a b hab ha
      rw [h1, h2]
      simp only [Fin.ext_iff, Fin.lt_def] at *
      omega
    · obtain ⟨h1, h2⟩ := segmentTransform_cross_values j a b hab
        (le_of_not_gt ha) (le_of_not_gt hb)
      rw [h1, h2]
      simp only [Fin.ext_iff, Fin.lt_def] at *
      omega

theorem reflected_strictSegments_image {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    (strictSegments k).image (segmentPermutation j) =
      insert (centerSegment j) (deletedSegments k) := by
  classical
  have hinv : Function.Involutive (segmentPermutation j) := segmentReflectionFun_involutive j
  ext p
  have himage : p ∈ (strictSegments k).image (segmentPermutation j) ↔
      segmentPermutation j p ∈ strictSegments k := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [hinv q]
      exact hq
    · intro hp
      exact ⟨segmentPermutation j p, hp, hinv p⟩
  rw [himage]
  rcases p with ⟨⟨a, b⟩, hab⟩
  have hstrict : (segmentTransform j a b hab).1 < (segmentTransform j a b hab).2 ↔
      ¬ ((a = b ∧ a ≠ j) ∨ (a.val = 0 ∧ b.val + 1 = k)) := by
    rw [lt_iff_le_and_ne]
    simp only [segmentTransform_valid, true_and, ne_eq, segmentTransform_equal_iff]
  simp only [strictSegments, deletedSegments, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, segmentPermutation, Function.Involutive.toPerm,
    segmentReflectionFun, Equiv.coe_fn_mk, centerSegment, Subtype.mk.injEq,
    Prod.mk.injEq]
  rw [hstrict]
  have habv : a.val ≤ b.val := hab
  simp only [Fin.ext_iff, Fin.lt_def] at *
  omega

theorem product_reflected_segments {R : Type*} [CommMonoid R] {k : ℕ}
    (hk : 2 ≤ k) (j : Fin k) (f : Segment k → R) :
    (∏ p ∈ strictSegments k, f (segmentPermutation j p)) =
      f (centerSegment j) * ∏ p ∈ deletedSegments k, f p := by
  classical
  rw [← Finset.prod_image (by
    intro a _ b _ h
    exact (segmentPermutation j).injective h), reflected_strictSegments_image hk j]
  rw [Finset.prod_insert]
  simp [deletedSegments, strictSegments, centerSegment]

theorem product_strictSegments {R : Type*} [CommMonoid R] (k : ℕ)
    (f : Fin k × Fin k → R) :
    (∏ p ∈ strictSegments k, f p.val) = ∏ p ∈ intervalPairs k, f p := by
  classical
  refine Finset.prod_bij (fun p _ ↦ p.val) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [strictSegments, intervalPairs] using hp
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro p hp
    have hlt : p.1 < p.2 := by simpa [intervalPairs] using hp
    refine ⟨⟨p, le_of_lt hlt⟩, ?_, rfl⟩
    simpa [strictSegments] using hlt
  · intro p _
    rfl

theorem product_deletedSegments {R : Type*} [CommMonoid R] (k : ℕ)
    (f : Fin k × Fin k → R) :
    (∏ p ∈ deletedSegments k, f p.val) =
      ∏ p ∈ (intervalPairs k).filter (fun p ↦ ¬ (p.1.val = 0 ∧ p.2.val + 1 = k)), f p := by
  classical
  refine Finset.prod_bij (fun p _ ↦ p.val) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [deletedSegments, strictSegments, intervalPairs] using hp
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro p hp
    have hlt : p.1 < p.2 := by
      have := (Finset.mem_filter.mp hp).1
      simpa [intervalPairs] using this
    refine ⟨⟨p, le_of_lt hlt⟩, ?_, rfl⟩
    simpa [deletedSegments, strictSegments, intervalPairs] using hp
  · intro p _
    rfl

theorem intervalProduct_eq_segment_prod (k : ℕ) :
    intervalProduct k = ∏ p ∈ strictSegments k, intervalSum p.val.1 p.val.2 := by
  exact (product_strictSegments k (fun p ↦ intervalSum p.1 p.2)).symm

theorem deletedIntervalProduct_eq_segment_prod (k : ℕ) :
    deletedIntervalProduct k = ∏ p ∈ deletedSegments k, intervalSum p.val.1 p.val.2 := by
  exact (product_deletedSegments k (fun p ↦ intervalSum p.1 p.2)).symm

theorem crossingSegments_card {k : ℕ} (j : Fin k) :
    ((strictSegments k).filter
      (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card =
      k - 1 + j.val * (k - 1 - j.val) := by
  classical
  let rectangle := (Finset.Iic j).product (Finset.Ici j)
  have hj : (j, j) ∈ rectangle := by simp [rectangle]
  have hcard : ((strictSegments k).filter
      (fun p ↦ p.val.1 ≤ j ∧ j ≤ p.val.2)).card =
      (rectangle.erase (j, j)).card := by
    refine Finset.card_bij (fun p _ ↦ p.val) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, strictSegments, Finset.mem_univ, true_and] at hp
      change p.val ∈ ((Finset.Iic j).product (Finset.Ici j)).erase (j, j)
      simp only [Finset.mem_erase, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_Iic, Finset.mem_Ici]
      exact ⟨by intro h; simpa [h] using hp.1, hp.2⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro p hp
      change p ∈ ((Finset.Iic j).product (Finset.Ici j)).erase (j, j) at hp
      simp only [Finset.mem_erase, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_Iic, Finset.mem_Ici] at hp
      have hlt : p.1 < p.2 := by
        by_contra hnlt
        have heq : p = (j, j) := by
          apply Prod.ext <;> apply Fin.ext
          · change p.1.val = j.val
            omega
          · change p.2.val = j.val
            omega
        exact hp.1 heq
      refine ⟨⟨p, le_of_lt hlt⟩, ?_, rfl⟩
      simpa [strictSegments] using And.intro hlt hp.2
  rw [hcard, Finset.card_erase_of_mem hj]
  change ((Finset.Iic j).product (Finset.Ici j)).card - 1 = _
  rw [Finset.product_eq_sprod, Finset.card_product, Fin.card_Iic, Fin.card_Ici]
  have hbound := j.isLt
  have hsub : k - j.val = (k - 1 - j.val) + 1 := by omega
  rw [hsub]
  have hsum : k - 1 = j.val + (k - 1 - j.val) := by omega
  have hmul : (j.val + 1) * ((k - 1 - j.val) + 1) =
      j.val + (k - 1 - j.val) + j.val * (k - 1 - j.val) + 1 := by ring
  rw [hmul]
  omega

end CostaPellegrini
