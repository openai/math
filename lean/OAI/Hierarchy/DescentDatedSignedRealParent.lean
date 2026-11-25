import OAI.Hierarchy.DescentDatedSignedParentValues
import OAI.Hierarchy.DescentDatedRetainedFirst

namespace OAI
/-! # Physical retained parent words at the deduplicated native ticket index -/
namespace Hierarchy.DescentDatedAddressBook.SignedDrawing
open DescentSixParty DescentOrdinarySignedRanks DescentOrdinarySignedMeta DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U]
  {d H prior degree Q O K b groups k age : ℕ} {bits : Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ} {A:GroupStage W G price ε (Fin groups) U k}
  {native:W.graph.Edge↪ℕ} {R:Fin prior→Fin degree→Option (Fin prior)}
  {symm:∀u v j,R u j=some v→∃n,R v n=some u} {host:U↪Fin H} {pitch:ℕ}
  {space:Fused.capacity degree Q K A.cap≤2^b}
  {before:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Option (Fused.Raw R Q K A.cap b)}
  {parent:Fin (2^k)→Fin O→Fin prior→Fin groups→Option (ParentFilter.Source (breadth degree) Q K A.cap)}
  {marks:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Cell 1}
variable (d₀:SignedDrawing A native R symm host pitch space before parent marks)
    (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S age)
local notation "group" => (Function.Embedding.refl (Fin groups))
local notation "home" => SignedExtent.wholeHost group host
local notation "name" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank ((group).trans Fin.valEmbedding) (host.trans Fin.valEmbedding))

local instance : Fintype d₀.edge := d₀.finiteEdge
local instance : Fintype d₀.raw := d₀.finiteRaw
local instance : Fintype d₀.ticket := d₀.finiteTicket

local notation "RR" => Measured.roster d₀.blocks R symm d₀.observed
local notation "slot" h:arg e:arg => (RR).address h e
local notation "Z₀" => Incidence.of_measured d₀.blocks R symm d₀.observed d₀.order

/-- Both polarities of the issued original face read the first common wire. The
peer is the actual neighbor at the first incident local grain on this face. -/
theorem real_parent (x : Fin (2^k)) (v : Fin H) (g : Fin groups) (h : Stage.Host (Fin groups) U k)
    (found : home x v g=some h) (edge : Local d₀.blocks h) (side : Bool)
    (face : DescentNextSignedWindow.Roster.Face A native d₀.blocks h) (ident : face.val.1=edge.val)
    (p : Fin (breadth degree)) (o : Fin O)
    (chosen : DescentHaloWalkRAM.Gather.select (DescentHaloWalkRAM.Gather.reaching R)
      (d₀.observed.venue h).1 p=some (d₀.observed.loc (d₀.observed.raw h edge)).1)
    (column : (d₀.observed.loc (d₀.observed.raw h edge)).2=o) (wireFit : A.cap ≤ 2^b)
    (peerFit : A.degree ≤ 2^b) :
    let j:=finProdFinEquiv (p,o)
    (d₀.serial S ready x j v g).val=(DescentPackedOperand.Public.endpoint A native S ready name side
      (d₀.emission.units ⟨edge.val,⟨0,edge.property.1⟩⟩)).wire.val ∧
      (d₀.peer S ready x j v g).val=(DescentResetWindowFields.neighbor A native S ready name d₀.blocks h face).val :=by
  intro j
  have atParent : slot h edge=j:=
    Measured.address_at d₀.blocks R symm d₀.observed h edge p o chosen column
  rw [←atParent]
  constructor
  · have serial:=DescentOrdinarySignedAll.first_serial_live A native S ready name d₀.blocks d₀.core d₀.emission
      Z₀ home x v g h found edge side
    change ((result d₀.blocks Z₀ home (Stage.measured A native S ready) x 1 ((Z₀).addr h edge) v g:ℕ):Cell b).val=_
    rw [serial]
    exact Fin.val_cast_of_lt ((DescentPackedOperand.Public.endpoint A native S ready name side
      (d₀.emission.units ⟨edge.val,⟨0,edge.property.1⟩⟩)).wire.isLt.trans_le wireFit)
  · change (SignedExtent.signedPeer A native S ready name d₀.blocks R symm d₀.observed home x
      (slot h edge) v g:Cell b).val=_
    simp only [SignedExtent.signedPeer,found,Option.elim_some,resident_at,peerCell]
    have bound:=(DescentResetWindowFields.neighbor A native S ready name d₀.blocks h
      (residentFace A native d₀.blocks h edge)).isLt.trans_le peerFit
    rw [Fin.val_cast_of_lt bound]
    exact congrArg Fin.val (neighbor_same_parent A native S ready name d₀.blocks h
      (residentFace A native d₀.blocks h edge) face ((residentFace_edge A native d₀.blocks h edge).trans ident.symm))

/-- A real receiver whose deduplicated candidate contains no local parent has two zero fields. -/
theorem no_resident (x : Fin (2^k)) (j : Fin (breadth degree*O)) (v : Fin H) (g : Fin groups)
    (h : Stage.Host (Fin groups) U k) (found : home x v g=some h)
    (empty : ∀edge : Local d₀.blocks h,slot h edge≠j) :
    d₀.serial S ready x j v g=0 ∧ d₀.peer S ready x j v g=0 :=by
  classical
  have hole : resident ((RR).address h) j=none:=by
    unfold resident
    split
    · next live => exact False.elim ((empty live.choose) live.choose_spec)
    · rfl
  change (((result d₀.blocks Z₀ home (Stage.measured A native S ready) x 1 j v g:ℕ):Cell b)=0) ∧
    ((SignedExtent.signedPeer A native S ready name d₀.blocks R symm d₀.observed home x j v g:Cell b)=0)
  have noAddress : resident ((Z₀).addr h) j=none := hole
  simp [result,request,found,noAddress,hole,SignedExtent.signedPeer,peerCell]

end
end Hierarchy.DescentDatedAddressBook.SignedDrawing

end OAI
