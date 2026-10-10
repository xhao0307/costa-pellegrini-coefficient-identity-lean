import Definitions

namespace CostaPellegrini

def segmentTransform {k : ℕ} (j a b : Fin k) (hab : a ≤ b) : Fin k × Fin k :=
  if hb : b < j then
    (⟨j.val - 1 - b.val, by omega⟩, ⟨j.val - 1 - a.val, by omega⟩)
  else if ha : j < a then
    (⟨k + j.val - b.val, by omega⟩, ⟨k + j.val - a.val, by omega⟩)
  else
    (⟨j.val - a.val, by omega⟩, ⟨k + j.val - b.val - 1, by omega⟩)

theorem segmentTransform_valid {k : ℕ} (j a b : Fin k) (hab : a ≤ b) :
    (segmentTransform j a b hab).1 ≤ (segmentTransform j a b hab).2 := by
  unfold segmentTransform
  split_ifs <;> simp only [Fin.le_iff_val_le_val] <;> omega

theorem segmentTransform_left_values {k : ℕ} (j a b : Fin k) (hab : a ≤ b)
    (hb : b < j) :
    (segmentTransform j a b hab).1.val = j.val - 1 - b.val ∧
      (segmentTransform j a b hab).2.val = j.val - 1 - a.val := by
  simp [segmentTransform, hb]

theorem segmentTransform_right_values {k : ℕ} (j a b : Fin k) (hab : a ≤ b)
    (ha : j < a) :
    (segmentTransform j a b hab).1.val = k + j.val - b.val ∧
      (segmentTransform j a b hab).2.val = k + j.val - a.val := by
  have hb : ¬ b < j := by omega
  simp [segmentTransform, hb, ha]

theorem segmentTransform_cross_values {k : ℕ} (j a b : Fin k) (hab : a ≤ b)
    (ha : a ≤ j) (hb : j ≤ b) :
    (segmentTransform j a b hab).1.val = j.val - a.val ∧
      (segmentTransform j a b hab).2.val = k + j.val - b.val - 1 := by
  simp [segmentTransform, not_lt_of_ge ha, not_lt_of_ge hb]

theorem segmentTransform_involutive {k : ℕ} (j a b : Fin k) (hab : a ≤ b) :
    segmentTransform j (segmentTransform j a b hab).1 (segmentTransform j a b hab).2
      (segmentTransform_valid j a b hab) = (a, b) := by
  let p := segmentTransform j a b hab
  have hp := segmentTransform_valid j a b hab
  by_cases hb : b < j
  · obtain ⟨h1, h2⟩ := segmentTransform_left_values j a b hab hb
    have hb' : p.2 < j := by
      change p.2.val < j.val
      change (segmentTransform j a b hab).2.val < j.val
      rw [h2]
      omega
    obtain ⟨h1', h2'⟩ := segmentTransform_left_values j p.1 p.2 hp hb'
    apply Prod.ext <;> apply Fin.ext
    · change (segmentTransform j p.1 p.2 hp).1.val = a.val
      rw [h1', h2]
      omega
    · change (segmentTransform j p.1 p.2 hp).2.val = b.val
      rw [h2', h1]
      omega
  · by_cases ha : j < a
    · obtain ⟨h1, h2⟩ := segmentTransform_right_values j a b hab ha
      have ha' : j < p.1 := by
        change j.val < (segmentTransform j a b hab).1.val
        rw [h1]
        omega
      obtain ⟨h1', h2'⟩ := segmentTransform_right_values j p.1 p.2 hp ha'
      apply Prod.ext <;> apply Fin.ext
      · change (segmentTransform j p.1 p.2 hp).1.val = a.val
        rw [h1', h2]
        omega
      · change (segmentTransform j p.1 p.2 hp).2.val = b.val
        rw [h2', h1]
        omega
    · have haj : a ≤ j := le_of_not_gt ha
      have hjb : j ≤ b := le_of_not_gt hb
      obtain ⟨h1, h2⟩ := segmentTransform_cross_values j a b hab haj hjb
      have ha' : p.1 ≤ j := by
        change (segmentTransform j a b hab).1.val ≤ j.val
        rw [h1]
        omega
      have hb' : j ≤ p.2 := by
        change j.val ≤ (segmentTransform j a b hab).2.val
        rw [h2]
        omega
      obtain ⟨h1', h2'⟩ := segmentTransform_cross_values j p.1 p.2 hp ha' hb'
      apply Prod.ext <;> apply Fin.ext
      · change (segmentTransform j p.1 p.2 hp).1.val = a.val
        rw [h1', h1]
        omega
      · change (segmentTransform j p.1 p.2 hp).2.val = b.val
        rw [h2', h2]
        omega

theorem segmentTransform_singleton {k : ℕ} (j : Fin k) :
    (segmentTransform j j j le_rfl).1.val = 0 ∧
      (segmentTransform j j j le_rfl).2.val = k - 1 := by
  obtain ⟨h1, h2⟩ := segmentTransform_cross_values j j j le_rfl le_rfl le_rfl
  rw [h1, h2]
  constructor <;> omega

theorem segmentTransform_full {k : ℕ} (j a b : Fin k)
    (ha : a.val = 0) (hb : b.val = k - 1) (hab : a ≤ b) :
    segmentTransform j a b hab = (j, j) := by
  have haj : a ≤ j := by omega
  have hjb : j ≤ b := by omega
  obtain ⟨h1, h2⟩ := segmentTransform_cross_values j a b hab haj hjb
  apply Prod.ext <;> apply Fin.ext
  · change (segmentTransform j a b hab).1.val = j.val
    rw [h1, ha]
    omega
  · change (segmentTransform j a b hab).2.val = j.val
    rw [h2, hb]
    omega

end CostaPellegrini
