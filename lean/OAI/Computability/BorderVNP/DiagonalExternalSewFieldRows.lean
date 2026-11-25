import OAI.Computability.BorderVNP.DiagonalExternalSewFields

/-! # Semantic exterior rows in the Boolean fields of the final pack -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FieldExport

open Crossing Packing.CellAddressCircuit Packing.CellAddressPhysical ParseBatchSort
open scoped Classical

/-- Positive block width, the two-probe property, and capacity of the initial site directory. -/
structure Params.Valid (p : Params) : Prop where
  /-- The site block is nonempty. -/
  block : 0 < p.g
  /-- A site block meets at most two exterior fields. -/
  small : p.g ≤ p.link
  /-- All processor slots fit the initial site blocks. -/
  room : p.processors*(2*p.literal+p.R*p.link) ≤ p.sites*p.g

/-- The physical nonempty exterior wires. -/
abbrev Params.Wires (p : Params) := Cables p.R p.processors p.literal p.link p.g

/-- Stable injection of true physical wires into the entire four-slot rectangle. -/
def Params.ordinal (p : Params) (h : p.Valid) : p.Wires ↪ Fin p.slots :=
  (⟨FourSlot.index p.sites h.block (by omega) h.room,
    FourSlot.index_injective p.sites h.block h.small (by omega) h.room⟩ :
    p.Wires ↪ Fin (p.R+1) × Fin p.sites × (Bool×Bool)).trans (FourSlot.slotOrdinal _ _).toEmbedding

/-- The three exterior fields at the true wire's stable sparse ordinal are
its low and high host names and its complete field interval width. -/
theorem Params.ordinal_fields (p : Params) (h : p.Valid) (name : ℕ → ℕ → ℕ) (c : p.Wires) :
    let i := p.ordinal h c
    p.pointer name i false = name c.1.1.val.1.val c.2.val.1 ∧
      p.pointer name i true = name c.1.1.val.2.val c.2.val.2 ∧ p.width i = cableWidth c := by
  have fit : p.literal+p.R*p.link ≤ 2*p.literal+p.R*p.link := by omega
  have key : p.key (p.ordinal h c) = FourSlot.index p.sites h.block fit h.room c :=
    (FourSlot.slotOrdinal _ _).symm_apply_apply _
  dsimp only
  simp only [Params.pointer,Params.width,Params.record,key,FourSlot.index,
    FourSlot.row_index c h.block h.small fit,Bool.false_eq_true,ite_false,ite_true]
  exact ⟨trivial,trivial,trivial⟩

/-- A reserved ordinal outside the physical wire image has zero width in the
actual Boolean columns, independently of its natural clipped arithmetic. -/
theorem Params.width_unused (p : Params) (h : p.Valid) (j : Fin p.slots)
    (unused : j ∉ Set.range (p.ordinal h)) : p.width j = 0 := by
  have live : (p.record j).live ≠ true := by
    intro isLive
    obtain ⟨c,he⟩ := (FourSlot.row_live_iff h.block h.small (by omega) h.room (p.key j)).mp isLive
    apply unused
    refine ⟨c,?_⟩
    apply (FourSlot.slotOrdinal _ _).symm.injective
    exact ((FourSlot.slotOrdinal _ _).symm_apply_apply _).trans he
  simp [Params.width,live]

/-- Physical embedding of the union of old cables and sewn exterior cables. -/
def mergedEdges {old : ℕ} {E : Type*} (p : Params) (h : p.Valid) (prev : E ↪ Fin old) :
    (E ⊕ p.Wires) ↪ Fin (old+p.slots) :=
  (prev.sumMap (p.ordinal h)).trans finSumFinEquiv.toEmbedding

/-- Every old or new slot not hit by the combined embedding is a hole on its own side. -/
theorem merged_hole {old : ℕ} {E : Type*} (p : Params) (h : p.Valid) (prev : E ↪ Fin old)
    (i : Fin (old+p.slots)) (hi : i ∉ Set.range (mergedEdges p h prev)) :
    match finSumFinEquiv.symm i with
    | .inl j => j ∉ Set.range prev
    | .inr j => j ∉ Set.range (p.ordinal h) := by
  rcases eq : finSumFinEquiv.symm i with j|j
  · rintro ⟨e,rfl⟩
    exact hi ⟨.inl e,finSumFinEquiv.symm_apply_eq.mp eq |>.symm⟩
  · rintro ⟨e,rfl⟩
    exact hi ⟨.inr e,finSumFinEquiv.symm_apply_eq.mp eq |>.symm⟩

end Diagonal.ExternalSew.FieldExport

end BorderVNP
end Computability
end OAI
