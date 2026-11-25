import OAI.Hierarchy.DescentMeasuredRectangle
import OAI.Hierarchy.DescentMeasuredBaseGeometry
import OAI.Hierarchy.DescentRealizedBasisPrice

namespace OAI
/-! # Authentic neighbor slots and bounded row positions for adaptive reset loads -/
namespace Hierarchy.DescentMeasuredWeights
open DescentGL DescentColonies DescentBaseProfile
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {H Δ k : ℕ}
variable (idx : V≃Fin H) (ns : Native.Neighbors H) (near : V→Finset V)
variable (topology : ∀v,(near v).map idx.toEmbedding=measuredNear ns (idx v))
    (degree : ∀i:Fin H,(ns[i.val]).length≤Δ)

include topology in
omit [Fintype V] [DecidableEq V] in
theorem listed (c : Contacts near) : idx c.2.val∈ns[(idx c.1).val] := by
  rw [←List.mem_toFinset]
  change _∈measuredNear ns (idx c.1)
  rw [←topology c.1]
  exact Finset.mem_map.mpr ⟨c.2.val,c.2.property,rfl⟩

def contactSlot (c : Contacts near) : Fin Δ :=
  ⟨(ns[(idx c.1).val]).idxOf (idx c.2.val),
    (List.idxOf_lt_length_iff.mpr (listed idx ns near topology c)).trans_le (degree _)⟩

/-- Both the owner and the opposite endpoint are read from the previous
native neighbor list. Keeping its first occurrence also handles duplicates. -/
def neighborSlots : Contacts near ↪ Fin H×Fin Δ where
  toFun c := (idx c.1,contactSlot idx ns near topology degree c)
  inj' := by
    rintro ⟨v,a⟩ ⟨u,b⟩ eq
    obtain rfl : v=u := idx.injective (congrArg Prod.fst eq)
    have pos : (ns[(idx v).val]).idxOf (idx a.val)=(ns[(idx v).val]).idxOf (idx b.val) :=
      congrArg (fun z : Fin H×Fin Δ=>z.2.val) eq
    have left:=List.idxOf_lt_length_iff.mpr (listed idx ns near topology (⟨v,a⟩ : Contacts near))
    have right:=List.idxOf_lt_length_iff.mpr (listed idx ns near topology (⟨v,b⟩ : Contacts near))
    let nbr:=ns[(idx v).val]
    have same : (⟨nbr.idxOf (idx a.val),left⟩:Fin nbr.length)=⟨nbr.idxOf (idx b.val),right⟩ := Fin.ext pos
    have hit : idx a.val=idx b.val :=
      (List.getElem_idxOf left).symm.trans ((congrArg nbr.get same).trans (List.getElem_idxOf right))
    obtain rfl : a=b:=Subtype.ext (idx.injective hit)
    rfl

omit [Fintype V] [DecidableEq V] in
theorem get_other (c : Contacts near) :
    (ns[(idx c.1).val])[(contactSlot idx ns near topology degree c).val]'(
      List.idxOf_lt_length_iff.mpr (listed idx ns near topology c))=idx c.2.val :=
  List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (listed idx ns near topology c))

def nativeRow (b : V→ℕ) :
    Item (inputLevels (k:=k) b) (Contacts near) ↪ Fin (H*(k+1)+H*Δ) :=
  rectangle idx _ (fun v=>by dsimp [inputLevels];omega)
    (neighborSlots idx ns near topology degree)

omit [Fintype V] [DecidableEq V] in
theorem live_level (b : V→ℕ) (v : V) (s : Fin (inputLevels (k:=k) b v)) :
    (nativeRow idx ns near topology degree b (.inl ⟨v,s⟩)).val=
      (idx v).val*(k+1)+s.val := by
  change s.val+(k+1)*(idx v).val=_
  ring

omit [Fintype V] [DecidableEq V] in
theorem live_contact (b : V→ℕ) (c : Contacts near) :
    (nativeRow (k:=k) idx ns near topology degree b (.inr c)).val=
      H*(k+1)+(idx c.1).val*Δ+(ns[(idx c.1).val]).idxOf (idx c.2.val) := by
  change H*(k+1)+((ns[(idx c.1).val]).idxOf (idx c.2.val)+Δ*(idx c.1).val)=_
  ring

end
end Hierarchy.DescentMeasuredWeights

end OAI
