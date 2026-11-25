import OAI.ThreeFlat.RAM.MotifRows

namespace OAI
/-! # Overflow-safe admission of a packed histogram

Each active word is compared against the remaining multiplicity, then subtracted.
The final remainder and every unused word must be zero.
-/

namespace ThreeFlat.RAM.MotifAdmission
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr MotifRows
open scoped Classical
variable {n K : ℕ}

private def spend (base : Formula n) : List (Fin K) → Formula n → Formula n
  | [], rem => .select .eq rem (.lit 0) (.lit 1) (.lit 0)
  | i::tail, rem =>
    let count := field base i.val
    .select .lt rem count (.lit 0) (spend base tail (.cut rem count))

private def zeroPad (base : Formula n) : List (Fin K) → Formula n → Formula n
  | [], keep => keep
  | i::tail, keep => .select .eq (field base i.val) (.lit 0) (zeroPad base tail keep) (.lit 0)

/-- A fixed active-coordinate list and padding layout define the native expression. -/
def formula (base copies : Formula n) (active pad : List (Fin K)) : Formula n :=
  zeroPad base pad (spend base active copies)

/-- Counts are tested with their exact natural sum; inactive positions must be zero. -/
def Valid (active pad : List (Fin K)) (counts : Fin K → ℕ) (copies : ℕ) : Prop :=
  (active.map counts).sum = copies ∧ ∀ i ∈ pad, counts i = 0

section Natural
variable (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs

private theorem subtract_guard (r c s : ℕ) :
    (if decide (r<c) then 0 else if s=r-c then 1 else 0 : ℕ) =
      if c+s=r then 1 else 0 := by
  by_cases bad : r<c
  · have unfair : c+s≠r := by omega
    simp [bad,unfair]
  · have eq : s=r-c ↔ c+s=r := by omega
    simp [bad,eq]

private theorem spend_value (base : Formula n) (active : List (Fin K)) (rem : Formula n) :
    V (spend base active rem) = if (active.map (fun i => mem (V base + i.val))).sum = V rem then 1 else 0 := by
  induction active generalizing rem with
  | nil => simp [spend,Formula.natural,natTest,eq_comm]
  | cons i tail ih =>
    simp only [spend, Formula.natural, natTest, field_value, ih, List.map_cons, List.sum_cons]
    exact subtract_guard _ _ _

private theorem zeroPad_value (base : Formula n) (pad : List (Fin K)) (keep : Formula n) :
    V (zeroPad base pad keep) = if ∀ i ∈ pad, mem (V base + i.val)=0 then V keep else 0 := by
  classical
  induction pad with
  | nil => simp [zeroPad]
  | cons i pad ih =>
    simp only [zeroPad,Formula.natural,natTest,field_value,ih,
      List.mem_cons,forall_eq_or_imp]
    split_ifs <;> simp_all

theorem natural_value (base copies : Formula n) (active pad : List (Fin K)) :
    V (formula base copies active pad) =
      if Valid active pad (fun i => mem (V base + i.val)) (V copies) then 1 else 0 := by
  classical
  rw [formula,zeroPad_value,spend_value]
  unfold Valid
  split_ifs <;> simp_all

private theorem field_fits (base : Formula n) (hb : Fit base) (room : V base + K ≤ 2^W) (i : Fin K) :
    Fit (field base i.val) := by
  refine ⟨⟨hb,trivial,trivial⟩,?_⟩
  change V base + i.val < 2^W
  omega

private theorem spend_fits (base : Formula n) (hb : Fit base) (room : V base + K ≤ 2^W)
    (hm : ∀ i : Fin K, mem (V base+i.val) < 2^W)
    (active : List (Fin K)) (rem : Formula n) (hr : Fit rem) (small : V rem < 2^W) :
    Fit (spend base active rem) := by
  induction active generalizing rem with
  | nil =>
    refine ⟨hr,trivial,small,Nat.two_pow_pos W,?_⟩
    split <;> trivial
  | cons i tail ih =>
    have hf := field_fits W data mem vs base hb room i
    have hc : V (field base i.val) < 2^W := hm i
    refine ⟨hr,hf,small,hc,?_⟩
    split
    · trivial
    · exact ih (.cut rem (field base i.val)) ⟨hr,hf,small,hc⟩
        ((Nat.sub_le _ _).trans_lt small)

private theorem pad_fits (base : Formula n) (hb : Fit base) (room : V base + K ≤ 2^W)
    (hm : ∀ i : Fin K, mem (V base+i.val)<2^W) (pad : List (Fin K))
    (keep : Formula n) (hk : Fit keep) : Fit (zeroPad base pad keep) := by
  induction pad with
  | nil => exact hk
  | cons i tail ih =>
    refine ⟨field_fits W data mem vs base hb room i,trivial,hm i,Nat.two_pow_pos W,?_⟩
    split
    · exact ih
    · trivial

/-- No restriction on the sum of the supplied histogram is needed for word fit,
even when it exceeds the entire address space. -/
theorem fits (base copies : Formula n) (active pad : List (Fin K))
    (hb : Fit base) (hc : Fit copies) (room : V base + K ≤ 2^W) (small : V copies < 2^W)
    (hm : ∀ i : Fin K, mem (V base + i.val) < 2^W) : Fit (formula base copies active pad) :=
  pad_fits W data mem vs base hb room hm pad _ (spend_fits W data mem vs base hb room hm active copies hc small)

end Natural

open scoped Fin.CommRing

/-- Word evaluation agrees with unsigned histogram admission for every incoming memory.
Only the base pointer needs sufficient room for its consecutive field addresses. -/
theorem word_value {W : ℕ} (data : Param → Word W) (mem : Memory W) (vs : Fin n → Word W)
    (base copies : Fin n) (active pad : List (Fin K)) (room : (vs base).val + K ≤ 2^W) :
    (formula (.reg base) (.reg copies) active pad).value data mem vs =
      if Valid active pad (fun i => (mem ((vs base).val+i.val)).val) (vs copies).val
        then (1 : Word W) else 0 := by
  let a := fun i => (data i).val
  let m := fun i => (mem i).val
  let v := fun i => (vs i).val
  have h := fits W a m v (.reg base) (.reg copies) active pad trivial trivial room
    (vs copies).isLt (fun i => (mem ((vs base).val+i.val)).isLt)
  have h' := (formula (.reg base) (.reg copies) active pad).value_eq_natural a m v h
  rw [natural_value] at h'
  change (formula (.reg base) (.reg copies) active pad).value _ _ _ =
    ((if Valid active pad (fun i => (mem ((vs base).val+i.val)).val) (vs copies).val then 1 else 0 : ℕ) : Word W) at h'
  simpa [a,m,v,apply_ite Nat.cast] using h'

theorem word_eq_one_iff {W : ℕ} (hW : 0 < W) (data : Param → Word W) (mem : Memory W)
    (vs : Fin n → Word W) (base copies : Fin n) (active pad : List (Fin K))
    (room : (vs base).val + K ≤ 2^W) :
    (formula (.reg base) (.reg copies) active pad).value data mem vs = 1 ↔
      Valid active pad (fun i => (mem ((vs base).val+i.val)).val) (vs copies).val := by
  have hsize : 2 ≤ 2^W := calc
    2 = 2^1 := by decide
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hW
  have ne : (0 : Word W) ≠ 1 := by
    intro he
    have h := congrArg Fin.val he
    change 0 = 1 % (2^W) at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
  rw [word_value _ _ _ _ _ _ _ room]
  split_ifs <;> simp_all

end ThreeFlat.RAM.MotifAdmission

end OAI
