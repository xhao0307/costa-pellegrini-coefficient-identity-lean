import Transport
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Choose.Basic

open scoped BigOperators

namespace CostaPellegrini

noncomputable section

def blockReverseFun {k : ℕ} (j i : Fin k) : Fin k :=
  if h : i < j then ⟨j.val - 1 - i.val, by have := j.isLt; omega⟩
  else if h' : i = j then j
  else ⟨k + j.val - i.val, by
    have := i.isLt
    have := j.isLt
    have hgt : j.val < i.val := by
      have hne : i.val ≠ j.val := fun he ↦ h' (Fin.ext he)
      simp only [Fin.lt_def] at h
      omega
    omega⟩

theorem blockReverseFun_val_lt {k : ℕ} (j i : Fin k) (h : i < j) :
    (blockReverseFun j i).val = j.val - 1 - i.val := by
  simp [blockReverseFun, h]

@[simp] theorem blockReverseFun_eq {k : ℕ} (j : Fin k) :
    blockReverseFun j j = j := by
  simp [blockReverseFun]

theorem blockReverseFun_val_gt {k : ℕ} (j i : Fin k) (h : j < i) :
    (blockReverseFun j i).val = k + j.val - i.val := by
  simp [blockReverseFun, h.not_gt, h.ne.symm]

theorem blockReverseFun_involutive {k : ℕ} (j : Fin k) :
    Function.Involutive (blockReverseFun j) := by
  intro i
  by_cases hlt : i < j
  · have hval : (blockReverseFun j i).val = j.val - 1 - i.val := by
      simp [blockReverseFun, hlt]
    have hlt' : blockReverseFun j i < j := by
      simp only [Fin.lt_def, hval]
      have hi : i.val < j.val := hlt
      omega
    apply Fin.ext
    rw [blockReverseFun_val_lt j _ hlt', hval]
    have hi : i.val < j.val := hlt
    omega
  · by_cases heq : i = j
    · subst i
      simp [blockReverseFun]
    · have hval : (blockReverseFun j i).val = k + j.val - i.val := by
        simp [blockReverseFun, hlt, heq]
      have hgt : j.val < i.val := by
        have hne : i.val ≠ j.val := fun he ↦ heq (Fin.ext he)
        simp only [Fin.lt_def] at hlt
        omega
      have hnlt : ¬ blockReverseFun j i < j := by
        simp only [Fin.lt_def, hval]
        have hi := i.isLt
        omega
      have hneq : blockReverseFun j i ≠ j := by
        intro he
        have hv := congrArg Fin.val he
        rw [hval] at hv
        have hi := i.isLt
        omega
      have hgt' : j < blockReverseFun j i := lt_of_le_of_ne
        (le_of_not_gt hnlt) hneq.symm
      apply Fin.ext
      rw [blockReverseFun_val_gt j _ hgt', hval]
      have hi := i.isLt
      omega

def blockReverse {k : ℕ} (j : Fin k) : Equiv.Perm (Fin k) :=
  Function.Involutive.toPerm (blockReverseFun j) (blockReverseFun_involutive j)

theorem blockReverse_apply_lt {k : ℕ} (j i : Fin k) (h : i < j) :
    (blockReverse j i).val = j.val - 1 - i.val := by
  simp [blockReverse, Function.Involutive.toPerm, blockReverseFun, h]

@[simp] theorem blockReverse_apply_eq {k : ℕ} (j : Fin k) :
    blockReverse j j = j := by
  simp [blockReverse, Function.Involutive.toPerm, blockReverseFun]

theorem blockReverse_apply_gt {k : ℕ} (j i : Fin k) (h : j < i) :
    (blockReverse j i).val = k + j.val - i.val := by
  simp [blockReverse, Function.Involutive.toPerm, blockReverseFun,
    h.not_gt, h.ne.symm]

theorem blockReverse_involutive {k : ℕ} (j : Fin k) :
    Function.Involutive (blockReverse j) := blockReverseFun_involutive j

@[simp] theorem blockReverse_symm {k : ℕ} (j : Fin k) :
    (blockReverse j).symm = blockReverse j := rfl

def revFirst (n : ℕ) : Equiv.Perm (Fin (n + 1)) :=
  finSumFinEquiv.permCongr
    (Equiv.sumCongr (@Fin.revPerm n) (Equiv.refl (Fin 1)))

@[simp] theorem revFirst_castSucc (n : ℕ) (i : Fin n) :
    revFirst n i.castSucc = i.rev.castSucc := by
  simp only [revFirst, Equiv.permCongr_apply,
    finSumFinEquiv_symm_apply_castSucc, Equiv.sumCongr_apply,
    Sum.map_inl, Fin.revPerm_apply, finSumFinEquiv_apply_left]
  rfl

@[simp] theorem revFirst_last (n : ℕ) : revFirst n (Fin.last n) = Fin.last n := by
  apply Fin.ext
  simp [revFirst, Equiv.permCongr_apply, finSumFinEquiv_symm_last]

theorem revPerm_succ_decomposition (n : ℕ) :
    (@Fin.revPerm (n + 1)) = finRotate (n + 1) * revFirst n := by
  ext i
  refine Fin.lastCases ?_ (fun a ↦ ?_) i
  · simp [Equiv.Perm.mul_apply]
  · simp only [Fin.revPerm_apply, Fin.val_rev, Equiv.Perm.mul_apply,
      revFirst_castSucc, rotate_value, Fin.val_castSucc]
    have ha := a.isLt
    have hr := a.rev.isLt
    simp only [Nat.add_sub_cancel]
    split_ifs <;> omega

theorem sign_revPerm (n : ℕ) :
    Equiv.Perm.sign (@Fin.revPerm n) = (-1 : ℤˣ) ^ (n.choose 2) := by
  induction n with
  | zero =>
    have heq : (@Fin.revPerm 0) = 1 := Subsingleton.elim _ _
    simp [heq]
  | succ n ih =>
    rw [revPerm_succ_decomposition, Equiv.Perm.sign_mul]
    simp only [sign_finRotate, Nat.add_sub_cancel, revFirst,
      Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.sign_refl, mul_one, ih]
    rw [← pow_add]
    congr 1
    rw [Nat.choose_succ_succ, Nat.choose_one_right]

def blockIndexEquiv {k : ℕ} (j : Fin k) :
    ((Fin j.val ⊕ Fin 1) ⊕ Fin (k - 1 - j.val)) ≃ Fin k :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by have := j.isLt; omega))

def blockSumReverse {k : ℕ} (j : Fin k) :
    Equiv.Perm ((Fin j.val ⊕ Fin 1) ⊕ Fin (k - 1 - j.val)) :=
  Equiv.sumCongr (Equiv.sumCongr Fin.revPerm (Equiv.refl _)) Fin.revPerm

@[simp] theorem blockIndexEquiv_val_left {k : ℕ} (j : Fin k) (i : Fin j.val) :
    (blockIndexEquiv j (Sum.inl (Sum.inl i))).val = i.val := by
  simp [blockIndexEquiv]

@[simp] theorem blockIndexEquiv_val_middle {k : ℕ} (j : Fin k) (i : Fin 1) :
    (blockIndexEquiv j (Sum.inl (Sum.inr i))).val = j.val := by
  simp [blockIndexEquiv]

@[simp] theorem blockIndexEquiv_val_right {k : ℕ} (j : Fin k)
    (i : Fin (k - 1 - j.val)) :
    (blockIndexEquiv j (Sum.inr i)).val = j.val + 1 + i.val := by
  simp [blockIndexEquiv]

theorem blockReverse_blockIndexEquiv {k : ℕ} (j : Fin k)
    (i : ((Fin j.val ⊕ Fin 1) ⊕ Fin (k - 1 - j.val))) :
    blockReverse j (blockIndexEquiv j i) = blockIndexEquiv j (blockSumReverse j i) := by
  rcases i with (i | i) | i
  · have hlt : blockIndexEquiv j (Sum.inl (Sum.inl i)) < j := by
      simpa only [Fin.lt_def, blockIndexEquiv_val_left] using i.isLt
    apply Fin.ext
    rw [blockReverse_apply_lt j _ hlt]
    simp only [blockSumReverse, Equiv.sumCongr_apply, Sum.map_inl,
      Fin.revPerm_apply,
      blockIndexEquiv_val_left, Fin.val_rev]
    omega
  · have heq : blockIndexEquiv j (Sum.inl (Sum.inr i)) = j :=
      Fin.ext (blockIndexEquiv_val_middle j i)
    rw [heq, blockReverse_apply_eq]
    apply Fin.ext
    simp [blockSumReverse]
  · have hgt : j < blockIndexEquiv j (Sum.inr i) := by
      simp only [Fin.lt_def, blockIndexEquiv_val_right]
      omega
    apply Fin.ext
    rw [blockReverse_apply_gt j _ hgt]
    simp only [blockSumReverse, Equiv.sumCongr_apply, Sum.map_inr,
      Fin.revPerm_apply,
      blockIndexEquiv_val_right, Fin.val_rev]
    have hj := j.isLt
    have hi := i.isLt
    omega

theorem blockReverse_eq_permCongr {k : ℕ} (j : Fin k) :
    blockReverse j = (blockIndexEquiv j).permCongr (blockSumReverse j) := by
  ext i
  obtain ⟨a, rfl⟩ := (blockIndexEquiv j).surjective i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact congrArg Fin.val (blockReverse_blockIndexEquiv j a)

theorem sign_blockReverse_units {k : ℕ} (j : Fin k) :
    Equiv.Perm.sign (blockReverse j) =
      (-1 : ℤˣ) ^ (j.val.choose 2 + (k - 1 - j.val).choose 2) := by
  rw [blockReverse_eq_permCongr, Equiv.Perm.sign_permCongr]
  simp only [blockSumReverse, Equiv.Perm.sign_sumCongr,
    Equiv.Perm.sign_refl, mul_one, sign_revPerm, pow_add]

theorem sign_blockReverse {k : ℕ} (j : Fin k) :
    (Equiv.Perm.sign (blockReverse j) : ℤ) =
      (-1 : ℤ) ^ (j.val.choose 2 + (k - 1 - j.val).choose 2) := by
  rw [sign_blockReverse_units]
  simp

end

end CostaPellegrini
