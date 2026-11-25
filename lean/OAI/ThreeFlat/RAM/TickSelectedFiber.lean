import OAI.ThreeFlat.RAM.TickSlotLookup
import Mathlib.Data.List.NodupEquivFin

namespace OAI
/-! # The enumerated output of the real scheduler lookup is the complete slot fiber -/

namespace ThreeFlat.RAM.TickSlotLookup
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

variable {w n groups slots : ℕ} (group : Fin n → Fin groups) (slot : Fin n → Fin slots)
variable (own : Owner w) (reads : ∀ i : Fin n, own i.val = (((group i).val : Word w),((slot i).val : Word w)))
variable (gf : groups ≤ 2^w) (sf : slots ≤ 2^w) (g : Fin groups) (s : Fin slots)

private theorem cast_same {n : ℕ} (room : n ≤ 2^w) (i j : Fin n) :
    ((i.val : Word w)=(j.val : Word w)) ↔ i=j := by
  constructor
  · intro h
    apply Fin.ext
    have eq := congrArg Fin.val h
    simpa only [Fin.val_cast_of_lt (i.isLt.trans_le room),Fin.val_cast_of_lt (j.isLt.trans_le room)] using eq
  · intro h
    rw [h]

include reads gf sf in
private theorem hits (i : Fin n) : matchesOwner own (g.val : Word w) (s.val : Word w) i.val = true ↔
    group i=g ∧ slot i=s := by
  simp only [matchesOwner,decide_eq_true_eq,reads,Prod.mk.injEq,cast_same gf,cast_same sf]

private theorem belongs (i : ℕ) :
    i ∈ selected own g.val s.val 0 n ↔ i<n ∧ matchesOwner own g.val s.val i = true := by
  simp only [selected,← List.range_eq_range',List.mem_filter,List.mem_range]

abbrev Group := {i : Fin n // group i = g}

private def picked :
    {i // i ∈ selected own g.val s.val 0 n} ≃ {j : Group group g // slot j.val=s} where
  toFun i :=
    let yes := (belongs own g s i.val).mp i.property
    let j : Fin n := ⟨i.val,yes.1⟩
    let coordinates := (hits group slot own reads gf sf g s j).mp yes.2
    ⟨⟨j,coordinates.1⟩,coordinates.2⟩
  invFun i := ⟨i.val.val.val,(belongs own g s _).mpr ⟨i.val.val.isLt,
    (hits group slot own reads gf sf g s i.val.val).mpr ⟨i.val.property,i.property⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Finite enumeration in increasing physical root order, exactly as the
11-instruction native cursor appends it to memory. -/
def selectedEquiv : Fin (selected own g.val s.val 0 n).length ≃
    {i : Group group g // slot i.val=s} :=
  (List.Nodup.getEquiv _ (by simpa only [selected,← List.range_eq_range'] using nodup_indices own g.val s.val n)).trans
    (picked group slot own reads gf sf g s)

@[simp] theorem selectedEquiv_val (i : Fin (selected own g.val s.val 0 n).length) :
    (selectedEquiv group slot own reads gf sf g s i).val.val.val = (selected own g.val s.val 0 n).get i := rfl


end ThreeFlat.RAM.TickSlotLookup

end OAI
