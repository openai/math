import OAI.ThreeFlat.Diagonal.HistorySupplyRequest
import OAI.ThreeFlat.Diagonal.ShrinkHistoryWires
import OAI.ThreeFlat.Diagonal.CompressorSupplyPhysicalRead
import OAI.ThreeFlat.Diagonal.CompressorHalfPorts

namespace OAI
/-! # The outgoing callback of an occupied shrink motif in actual half-slot order -/
namespace ThreeFlat.Diagonal.CompressorPacking.SupplySend
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms MotifKernel MotifBinaryPacking
open scoped Classical BigOperators
noncomputable section

variable {c d : ℕ} {V H Tag L F : Type} [Field F]
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    (P : PackingData V H Tag L d c)
    (base : P.Motif→Fin 2→ℕ) (r : P.Motif→ℕ) (T : ∀m,FixedMotifTile demandGraph supplyGraph (base m) F)
    (x : Histories P base r T) (hn : ∀a:Tag,-a=a) (good : TagConditions P.slots (shift P) P.offset)
    (lay : Bool) (n : Fin 4→ℕ) (positive : ∀i,0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c)
    (pad : ℕ) (padding : LiftedSlots (V×Tag) pad L)

local notation "fresh" => outGraph P hn good lay n order hc pad padding
local notation "output" => outputWidth P base r T x hn good lay n order hc pad
local notation "cover" => allSlots P hn good lay n order hc pad
local notation "split" => divisions P hn good lay n
local notation "width" => bitsOn P base r T x lay
local notation "motifGraphs" => (fun _ : P.Motif => supplyGraph)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 500000 in
def request (v : Site V Tag L) (m : P.Motif) (a : ExternalAt supplyGraph (partySite P lay m) v)
    (j : Fin (historyWidth P base r T x m a.val.val)) : Σ q : (fresh).Port v,Fin (output q.val.1) :=
  let port : (oldSupply P lay).Port v := incidentPort motifGraphs (partySite P lay) v m a
  let eqv : width port.val.1=historyWidth P base r T x m a.val.val :=
    congrArg width (incidentPort_edge motifGraphs (partySite P lay) v m a)
  SlotRefinement.freshRequest (oldSupply P lay) fresh split width
    (fun e=>positive (typeIndex P hn good lay e)) cover
    (physical_ends P hn good lay n order hc pad padding) port (Fin.cast eqv.symm j)

theorem crossingPin_request {p : ℕ} (v : Site V Tag L)
    (new : (a : (fresh).Port v)→Fin (output a.val.1)→Fin p)
    (m : P.Motif) (a : ExternalAt supplyGraph (partySite P lay m) v)
    (j : Fin (historyWidth P base r T x m a.val.val)) :
    let q:=request P base r T x hn good lay n positive order hc pad padding v m a j
    crossingPin P base r T x hn good lay n positive order hc pad padding v new m a j=new q.1 q.2 := rfl

set_option maxRecDepth 6000 in
set_option maxHeartbeats 500000 in
theorem request_fields (v : Site V Tag L) (m : P.Motif) (a : ExternalAt supplyGraph (partySite P lay m) v)
    (j : Fin (historyWidth P base r T x m a.val.val)) :
    let port : (oldSupply P lay).Port v := incidentPort motifGraphs (partySite P lay) v m a
    let eqv : width port.val.1=historyWidth P base r T x m a.val.val :=
      congrArg width (incidentPort_edge motifGraphs (partySite P lay) v m a)
    let piece := (SlotEnergy.pieceIndex (width port.val.1) (split port.val.1)
      (positive (typeIndex P hn good lay port.val.1))).symm (Fin.cast eqv.symm j)
    let q:=request P base r T x hn good lay n positive order hc pad padding v m a j
    q.1.val=(cover (.inl ⟨port.val.1,piece.1⟩),port.val.2) ∧ q.2.val=piece.2.val := ⟨rfl,rfl⟩

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
theorem supplySide (v : Site V Tag L) (m : P.Motif) (party : {u // partySite P lay m u=v})
    (q : supplyGraph.Port party.val)
    (other : wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) q.val.1=none) :
    (incidentPort (fun _ : P.Motif=>supplyGraph) (partySite P lay) v m (PrivateOrder.onSide party q other)).val.2 =
      decide (party.val≠ShrinkMotif.supplySrc q.val.1) := by
  obtain ⟨⟨e,b⟩,he⟩:=q
  have apart : partySite P lay m (supplyGraph.tail e)≠partySite P lay m (supplyGraph.head e) := by
    intro eqv
    simp [wireOwner,eqv] at other
  cases b with
  | false =>
    change supplyGraph.tail e=party.val at he
    have here:partySite P lay m (supplyGraph.tail e)=v := (congrArg (partySite P lay m) he).trans party.property
    change (incidentPort _ _ _ _ _).val.2=decide (party.val≠supplyGraph.tail e)
    simp [incidentPort,PrivateOrder.onSide,here,he.symm]
  | true =>
    change supplyGraph.head e=party.val at he
    have dst := (congrArg (partySite P lay m) he).trans party.property
    have miss : partySite P lay m (supplyGraph.tail e)≠v := fun same=>apart (same.trans dst.symm)
    have neq : party.val≠supplyGraph.tail e := fun same=>miss ((congrArg (partySite P lay m) same.symm).trans party.property)
    change (incidentPort _ _ _ _ _).val.2=decide (party.val≠supplyGraph.tail e)
    simp [incidentPort,PrivateOrder.onSide,miss,neq]

section Native
open Native Native.Graph Native.ShrinkStage
variable {B : Type} [Fintype B] {t l N : ℕ}
variable (S : Graph.Stage) (P' : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
    (b : B ≃ Fin N) (bound : ∀k,S.pieces k≤S.pieceRadix)
    (ok : TagConditions P'.slots (shift P') P'.offset) (colors : 2≤S.colors)
set_option quotPrecheck false in
local notation "keyOrder" => edgeOrder P' (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound
local notation "cover'" => allPieceSlots P' binary_neg ok lay S.pieces keyOrder colors pad

open private source_slots_fst from OAI.ThreeFlat.Diagonal.CompressorPhysicalWidth

private theorem first_of_inverse {A U Z : Type} (slots : A × Z ≃ U × Z) (number : A ≃ U)
    (read : ∀ p y, (slots.symm (p,y)).1 = number.symm p) (a : A) (y : Z) :
    (slots (a,y)).1 = number a := by
  apply number.symm.injective
  rw [number.symm_apply_apply, ← read _ (slots (a,y)).2]
  exact congrArg Prod.fst (slots.symm_apply_apply (a,y))

section
attribute [local irreducible] endpointSlots ordinalOf

/-- The physical piece-slot equivalence used by the tree has exactly the
source row found by the raw successor-key lookup. Its residual lane is
retained by the slot label. -/
theorem numbered_piece (e : CrossEdge P' lay) (copy : Fin (S.pieces (typeIndex P' binary_neg ok lay e))) :
    let z : ShrinkEdge P' S.pieces:=⟨typeIndex P' binary_neg ok lay e,normalize P' e.1,copy⟩
    (cover' (.inl ⟨e,copy⟩)).1=CompressorRefresh.leftRow (b:=pad)
      ((ordinalOf S P' (baseNat b) bound lay false colors) z) := by
  intro z
  let slots := endpointSlots P' lay (fun j => (supplyRoles lay j).1) S.pieces keyOrder colors
  let number := ordinalOf S P' (baseNat b) bound lay false colors
  let y := ((allLanes P').symm e.1).2
  change CompressorRefresh.leftRow (b:=pad) ((slots (z,y)).1) =
    CompressorRefresh.leftRow (b:=pad) (number z)
  exact congrArg (CompressorRefresh.leftRow (b:=pad))
    (first_of_inverse slots number (source_slots_fst S P' (baseNat b) bound colors lay) z y)

end

def halfOrdinal {A Z : Type} {D : ℕ} (G : LiftedSlots A D Z) (e : (A×Fin D)×Z) (side : Bool) :=
  if side then D+(G.base.target e.1).2.val else e.1.2.val

theorem half_order {A U : Type} {D l : ℕ} (G : LiftedSlots A D (BitWord l)) (chart : A×BitWord l ≃ U)
    (u : A×BitWord l) (p : (Halves.chartGraph G chart).Port (chart u)) :
    ((Halves.portOrder G chart u).symm p).val=halfOrdinal G p.val.1 p.val.2 := by
  obtain ⟨⟨e,s⟩,h⟩:=p
  cases s <;> rfl

private theorem half_at_base {U Z : Type} [AddCommGroup Z] {d : ℕ}
    (G : LiftedSlots U d Z) (p : (U × Fin d) × Z) (slot : U × Fin d)
    (same : p.1 = slot) (side : Bool) :
    halfOrdinal G p side = if side then d+(SlotImage.oriented G false slot).2.val else slot.2.val := by
  subst slot
  cases side <;> rfl

theorem numbered_half (G : LiftedSlots (B × BitWord t) (liveDegree S+pad) (BitWord l))
    (e : CrossEdge P' lay) (copy : Fin (S.pieces (typeIndex P' binary_neg ok lay e))) (side : Bool) :
    let z : ShrinkEdge P' S.pieces:=⟨typeIndex P' binary_neg ok lay e,normalize P' e.1,copy⟩
    let slot:=CompressorRefresh.leftRow (b:=pad) ((ordinalOf S P' (baseNat b) bound lay false colors) z)
    halfOrdinal G (cover' (.inl ⟨e,copy⟩)) side=
      if side then liveDegree S+pad+(SlotImage.oriented G false slot).2.val else slot.2.val := by
  intro z slot
  exact half_at_base G _ slot
    (numbered_piece (S:=S) (P':=P') (b:=b) (bound:=bound) (ok:=ok)
      (colors:=colors) (lay:=lay) (pad:=pad) e copy) side


end Native


end
end ThreeFlat.Diagonal.CompressorPacking.SupplySend

end OAI
