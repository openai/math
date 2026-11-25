import OAI.Computability.BorderVNP.DiagonalNativeNumbering

/-! # Physical subtotal arrays in the native batch, grammar and scalar coordinates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.Tally

variable {Team Param Gadget Gadget' : Type*} {B : ℕ}

/-- Scalar positions occupy the dense table directory in their fixed order. -/
def numberScalars (t : Tally Team Param Gadget B) (scalar : Gadget ≃ Gadget') : Tally Team Param Gadget' B :=
  ⟨t.powers,fun j g => t.counts j (scalar.symm g)⟩

private theorem ext_arrays (a b : Tally Team Param Gadget B) (p : a.powers=b.powers) (c : a.counts=b.counts) : a=b := by
  cases a; cases b; simp_all

end Diagonal.Tally

namespace Cube.Physical

open Crossing Diagonal Diagonal.CellEntries
open scoped Classical BigOperators
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1600

variable {n d blocks b h K s D B T H U : ℕ} {P : Type*} {bits : P → ℕ}
    {Cell : Type} {Team Param Gadget : Type*} [Fintype Cell] [DecidableEq Cell]
    [Fintype Team] [Fintype Param]
    {N : Network D P bits} {cell : N.Site → Cell}
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : Packet n d blocks → TableEntry n b h K s → Gadget)
    (words : PowerWords Team Param Gadget B N tags)
    (label : Cell → Label (n+1) d) (owner : Fin d → Team)
    (a : Path N cell n d blocks b h K s) (team : Team ≃ Fin T) (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U)

omit [Fintype Cell] in
/-- The numbered path tally reads identical local power bits and identical
scalar entries. Each lookup is recorded at its actual routed owner. -/
theorem pathTally_number :
    pathTally slot (numberTables param scalar tags) x (fun p => scalar ∘ pos p) (words.number team param scalar)
      label (team ∘ owner) a =
    ((pathTally slot tags x pos words label owner a).renumber team param).numberScalars scalar := by
  apply Tally.ext_arrays
  · rfl
  · funext t g
    let e := Equiv.subtypeEquivRight (fun v : N.Site ⊕ (Packet n d blocks × Vertex (n+1)) =>
      show pathOwner label (team ∘ owner) a v = t ↔ pathOwner label owner a v = team.symm t from by
        cases v <;> exact team.eq_symm_apply.symm)
    simp only [pathTally,PowerWords.localTally,Tally.renumber,Tally.numberScalars]
    refine @Fintype.sum_equiv _ _ ℕ ?_ ?_ _ e _ _ ?_
    intro v
    have vals (w : N.Site ⊕ (Packet n d blocks × Vertex (n+1))) :
        w.elim (fun z => numberTables param scalar tags z (pathEdges slot a z) (fun p => x p.val))
          (pathExtra (fun p => scalar ∘ pos p) a) =
        numberEntry param scalar (w.elim (fun z => tags z (pathEdges slot a z) (fun p => x p.val)) (pathExtra pos a)) := by
      cases w with
      | inl v => rfl
      | inr pv => exact (numberEntry_gadget param scalar _).symm
    change (counters _).2 g = (counters ((e v).val.elim _ _)).2 (scalar.symm g)
    rw [vals,counters_numberEntry,Finsupp.mapDomain_equiv_apply]
    rfl

omit [Fintype Cell] in
/-- The original slot numbering and the present team assignment can differ
inside a row. Summation over all current processors recovers each numbered
exponent and each scalar multiplicity of this very same passing path. -/
theorem sum_numbered_physicalRow (j : Fin (H+U)) :
    (∑ t, physicalRow slot (numberTables param scalar tags) x (fun p => scalar ∘ pos p)
      (words.number team param scalar) label (team ∘ owner) a t j) =
    ∑ t, DiagonalTallyRAM.tallyRow
      (((pathTally slot tags x pos words label owner a).renumber team param).numberScalars scalar) t j := by
  rw [sum_physicalRow,pathTally_number]

end Cube.Physical

end BorderVNP
end Computability
end OAI
