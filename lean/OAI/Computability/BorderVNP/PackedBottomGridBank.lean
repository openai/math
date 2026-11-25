import OAI.Computability.BorderVNP.PackedBottomReportSources
import OAI.Computability.BorderVNP.PackedGridPadding
import OAI.Computability.BorderVNP.PackedGridExternal
import OAI.Computability.BorderVNP.PackedInheritedAddresses

/-! # The private one-copy wiring of the padded bottom box

The private fine-circuit lanes retain their original order inside a fixed
capacity. The canonical public incidence words occupy the next interval.
Stored two-bit tables tie every fine supplied bit to its actual grouped
exterior lane or to its private lane of a public cable. Private zero tables
fix the unused part of the fine storage and all unused public cable lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ne np qe qa : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)

/-- The actual one-copy public host with its grouped exterior intervals. -/
noncomputable abbrev grouped : Network D A width := ((N.cellNetwork cell position).uniformGrid src dst H).packExternal width owner

/-- The actual fine supplied bit and its within-word index. -/
abbrev FineInput := Σ u : Supplied N cell v, Fin (suppliedWidth N cell v u)

/-- Read each fine supplied bit at its true channel lane or external slot. -/
noncomputable def publicLane :
    FineInput N cell v → InputLane (grouped (H := H) (src := src) (dst := dst) N cell position width owner) v
  | ⟨.inl e,k⟩ =>
    .inl ⟨⟨pack.channel e.val,e.property.imp ((pack.src_eq e.val).trans) ((pack.dst_eq e.val).trans)⟩,
      (pack.address ⟨e.val,k⟩).2⟩
  | ⟨.inr p,_⟩ => .inr ⟨⟨(lane p.val).1,(aligned p.val).trans p.property⟩,(lane p.val).2⟩

/-- Translate the compact fine supplied order to the actual public grouped order. -/
noncomputable def publicIndex (k : Fin (suppliedSize N cell v)) :
    Fin (incoming (grouped (H := H) (src := src) (dst := dst) N cell position width owner) v) :=
  sourceOrder (grouped (H := H) (src := src) (dst := dst) N cell position width owner) channelID groupID v (publicLane N cell position pack width owner lane aligned v
    ((CellSlabs.ordinal (suppliedRow N cell v edgeID portID) (suppliedWidth N cell v)).symm k))

/-- At a named fine input, the relocation reads the actual packed lane. -/
theorem publicIndex_supplied (u : Supplied N cell v) (k : Fin (suppliedWidth N cell v u)) :
    publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v
      (suppliedOrdinal N cell v edgeID portID u k) =
    sourceOrder (grouped (H := H) (src := src) (dst := dst) N cell position width owner) channelID groupID v (publicLane N cell position pack width owner lane aligned v ⟨u,k⟩) := by
  simp only [publicIndex,suppliedOrdinal,Equiv.symm_apply_apply]

/-- Private fine-to-public copies are described only once, independently of the
number of copies in this bottom bundle. -/
noncomputable def fineTies (capFine : ℕ) : List Factor :=
  List.ofFn fun k : Fin (suppliedSize N cell v) =>
    compareUse (guessedSize N cell v+k.val)
      (capFine+(publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v k).val)

/-- The private address list realizes exactly the pullback from the public grouped
words to the compact fine input, at the current physical copy's offset. -/
theorem fineTies_pass (capFine off copy : ℕ) (bank : ℕ → Bool) :
    ((fineTies N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine).all
      (fun f => (f.observe bank off copy).isSome)) = true ↔
      ∀ k : Fin (suppliedSize N cell v), bank (off+(guessedSize N cell v+k.val)) =
        bank (off+(capFine+(publicIndex N cell position pack width owner lane aligned
          edgeID portID channelID groupID v k).val)) := by
  simp only [fineTies,List.all_eq_true,List.forall_mem_ofFn_iff,
    compareUse_observe]
  constructor
  · intro h k
    by_contra! hn
    simpa [hn] using h k
  · intro h k
    simp [h k]

/-- Private one-bit truth factors for the unused fine-storage suffix. -/
def fineZeros (used capFine : ℕ) : List Factor :=
  (List.range (capFine-used)).map (fun k => GridPadding.zeroFactor (used+k))

/-- A padded fine-storage suffix has exactly one allowed bit at every address. -/
theorem fineZeros_pass (used capFine off copy : ℕ) (bank : ℕ → Bool) :
    ((fineZeros used capFine).all (fun f => (f.observe bank off copy).isSome)) = true ↔
      ∀ k < capFine-used, bank (off+(used+k)) = false := by
  simp only [fineZeros,List.all_eq_true,List.forall_mem_map,List.mem_range,
    GridPadding.observe_zero]
  constructor
  · intro h k hk
    cases he : bank (off+(used+k)) <;> simp_all
  · intro h k hk
    simp [h k hk]

/-- Local cable padding reads the same full grid word as the public repeat ties. -/
noncomputable def channelAddress (capFine : ℕ)
    (z : GridPadding.LocalLane (N := N.cellNetwork cell position) (H := H) (src := src) (dst := dst) v) : ℕ :=
  capFine + (sourceOrder (grouped (H := H) (src := src) (dst := dst) N cell position width owner)
    channelID groupID v (.inl ⟨z.1,z.2⟩)).val

/-- The actual additional private rows: fine-to-public ties, storage zeroes and
unused channel bits. None of these checks receives a weighted source index. -/
noncomputable def wiring (capFine : ℕ) : List Factor :=
  fineTies N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine ++
    fineZeros (GridBoxes.stride N cell v) capFine ++
    GridPadding.factors pack v (channelAddress (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v capFine)

/-- Staging addresses assigned to weighted sources are independent of all private
copy and zero rows added to realize the physical padded grid. -/
theorem wiring_tags (capFine : ℕ) :
    (wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine).filterMap
      factorTag = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro f hf
  simp only [wiring,List.mem_append,fineTies,List.mem_ofFn,fineZeros,List.mem_map,GridPadding.factors] at hf
  rcases hf with ((⟨k,rfl⟩ | ⟨k,_,rfl⟩) | ⟨k,_,rfl⟩) <;> rfl

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
