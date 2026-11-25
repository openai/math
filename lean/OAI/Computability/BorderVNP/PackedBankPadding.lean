import OAI.Computability.BorderVNP.CrossingCellProfileBank

/-! # Canonical zero padding of sparse profile banks

The fixed-stride profile layout reserves one row for each bundle. A single
zero record constrains the whole unused suffix of each row. Consequently
padding cannot increase the number of admissible private assignments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCircuit

open Crossing.Profile.Cell CellSparse
open scoped Classical

variable {R : Type*} [Fintype R] (L : BankLayout R)

/-- Occupied prefix of a row of the profile layout. -/
def active (r : R) : ℕ := L.copies r * L.lanes r

/-- Linear bit position in a reserved row. -/
noncomputable def address (r : R) (k : ℕ) : ℕ := (Fintype.equivFin R r).val * L.stride + k

/-- The one suffix descriptor required for this row, including empty suffixes. -/
noncomputable def padding (r : R) : Record :=
  .zero 1 (L.stride - active L r) ⟨address L r (active L r),0,1⟩

/-- Checking the suffix descriptor forces precisely the reserved but unused slots. -/
theorem padding_valid (r : R) (boxes : List (List Factor)) (bank : ℕ → Bool) :
    (padding L r).Valid boxes bank ↔
      ∀ k, active L r ≤ k → k < L.stride → bank (address L r k) = false := by
  constructor
  · intro h k hlo hhi
    have hz := h 0 (by decide) (k-active L r) (by omega)
    simpa only [Port.atBit,zero_mul,add_zero,mul_one,address,Nat.add_assoc,Nat.add_sub_of_le hlo] using hz
  · intro h i hi k hk
    have hzero : i = 0 := by omega
    subst i
    have hv := h (active L r+k) (Nat.le_add_right _ _) (by omega)
    simpa [Port.atBit,address,Nat.add_assoc] using hv

private theorem active_le (r : R) : active L r ≤ L.stride :=
  Finset.single_le_sum (fun i _ => Nat.zero_le (L.copies i * L.lanes i)) (Finset.mem_univ r)

private noncomputable def rowSlot (r : R) (k : Fin L.stride) : Fin (Fintype.card R * L.stride) :=
  finProdFinEquiv (Fintype.equivFin R r,k)

private theorem rowSlot_val (r : R) (k : Fin L.stride) : (rowSlot L r k).val = address L r k.val := by
  simp [rowSlot,address,Nat.mul_comm,Nat.add_comm]

private noncomputable def slotData (y : L.Data) (r : R) (k : Fin L.stride) : Bool :=
  if h : k.val < active L r then
    let b := finProdFinEquiv.symm (⟨k.val,h⟩ : Fin (L.copies r * L.lanes r))
    y r b.1 b.2
  else false

private noncomputable def packed (y : L.Data) (z : Fin (Fintype.card R * L.stride)) : Bool :=
  let a := finProdFinEquiv.symm z
  slotData L y ((Fintype.equivFin R).symm a.1) a.2

/-- Store the actual finite physical data and zero all unused bits. -/
noncomputable def paddedBank (y : L.Data) (t : ℕ) : Bool :=
  if h : t < Fintype.card R * L.stride then packed L y ⟨t,h⟩ else false

private theorem padded_address (y : L.Data) (r : R) (k : Fin L.stride) :
    paddedBank L y (address L r k.val) =
      if h : k.val < active L r then
        let b := finProdFinEquiv.symm (⟨k.val,h⟩ : Fin (L.copies r * L.lanes r))
        y r b.1 b.2 else false := by
  rw [← rowSlot_val L r k]
  rw [paddedBank,dite_eq_left (rowSlot L r k).isLt]
  change packed L y (rowSlot L r k) = _
  simp only [packed,rowSlot,Equiv.symm_apply_apply]
  rfl

/-- The exact finite assignment satisfies each of the padding records. -/
theorem padded_valid (y : L.Data) (boxes : List (List Factor)) (r : R) :
    (padding L r).Valid boxes (paddedBank L y) := by
  rw [padding_valid]
  intro k hlo hhi
  rw [padded_address L y r ⟨k,hhi⟩, dite_eq_right (Nat.not_lt.mpr hlo)]

private theorem lane_address (r : R) (i : Fin (L.copies r)) (k : Fin (L.lanes r)) :
    (L.port r).atBit i k = address L r (finProdFinEquiv (i,k)).val := by
  simp [BankLayout.port,Port.atBit,address,Nat.add_assoc,Nat.mul_comm,Nat.add_comm]

/-- Every occupied bit reads exactly the old physical bundle bit. -/
theorem padded_read (y : L.Data) (r : R) (i : Fin (L.copies r)) (k : Fin (L.lanes r)) :
    paddedBank L y ((L.port r).atBit i k) = y r i k := by
  let u := finProdFinEquiv (i,k)
  let k' : Fin L.stride := ⟨u.val,u.isLt.trans_le (active_le L r)⟩
  have hu : k'.val < active L r := u.isLt
  rw [lane_address]
  change paddedBank L y (address L r k'.val) = _
  rw [padded_address L y r k', dite_eq_left hu]
  change y r (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 = _
  simp [u]

/-- The physical data and the suffix checks uniquely determine the entire allocated bank. -/
theorem padded_unique (y : L.Data) (boxes : List (List Factor)) (bank : ℕ → Bool)
    (hpad : ∀ r, (padding L r).Valid boxes bank)
    (hread : ∀ r (i : Fin (L.copies r)) (k : Fin (L.lanes r)), bank ((L.port r).atBit i k) = y r i k)
    {t : ℕ} (ht : t < Fintype.card R * L.stride) : bank t = paddedBank L y t := by
  obtain ⟨⟨a,k⟩,ha⟩ := finProdFinEquiv.surjective (⟨t,ht⟩ : Fin (Fintype.card R * L.stride))
  let r := (Fintype.equivFin R).symm a
  have hr : address L r k.val = t := by
    rw [← rowSlot_val]
    simpa [rowSlot,r] using congrArg Fin.val ha
  rw [← hr]
  by_cases h : k.val < active L r
  · obtain ⟨⟨i,v⟩,hv⟩ := finProdFinEquiv.surjective (⟨k.val,h⟩ : Fin (L.copies r * L.lanes r))
    have hpos : (L.port r).atBit i v = address L r k.val := by rw [lane_address,hv]
    rw [← hpos, hread, padded_read]
  · have hlow := Nat.le_of_not_gt h
    exact ((padding_valid L r boxes bank).mp (hpad r) k hlow k.isLt).trans
      (((padding_valid L r boxes _).mp (padded_valid L y boxes r) k hlow k.isLt).symm)

end Packing.BankCircuit

end BorderVNP
end Computability
end OAI
