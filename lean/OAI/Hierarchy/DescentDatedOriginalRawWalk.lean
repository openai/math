import OAI.Hierarchy.DescentOrdinaryCapturePathRead
import OAI.Hierarchy.DescentDatedTicketRank

namespace OAI
/-! # True left and right physical owner paths at every raw ordinary occurrence -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z w M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (groups : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (he : 0≤ε) (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes slots : ℕ)
local notation "rank" => groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "near" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "scene" => nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m near hub lay bytes
local notation "physical" => physicalSigned A native S ready rank groups hosts
local notation "terrain₀" => terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank)
local notation "panel" => spread groups.toEmbedding hosts terrain₀
local notation "out" => DescentSharedCableNames.Stage.outgoing A native S ready
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z)))
    (named : A.SiteNamed (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)))
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=
      1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (order : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)

include coord named fit winner df order in
theorem retained_raw_path_mounted
    (roster : Fin H→Fin A.degree→Option (Fin H)) (agrees : ∀v j,roster (hosts v) j=near (hosts v) j)
    (e : Positive) (role : Fin 11) (side : Bool) :
    let v:=W.graph.src e.val
    DepotRAM.rawAtSeat fmt profile G.b slots side (nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m roster hub lay bytes (hosts (A.pos v).2) (groups (A.pos v).1)) (A.block v) (out e) role=
      ParentIncidence.pathCell A.degree side (rawParentRows (short:=short) A native S ready rank win profile lay e role) :=by
  intro v
  let z:=A.pos v
  let h:=hosts z.2
  let g:=groups z.1
  let x:=A.block v
  let raw:=nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m roster hub lay bytes h g
  let issued:=DepotRAM.seatDonor fmt profile G.b slots raw x (out e)
  have units : DescentSharedCableNames.Stage.sourceGrains (physical h g x) (out e)=A.grainCount e.val :=by
    have signs : physical h g x=fun j=>DescentSignedCableCodec.encode
        (DescentSharedCableNames.Stage.signedPanel A native S ready (cableNames k rank) (z,x) j):=by
      funext j;exact physical_signed_read A native S ready rank groups hosts z x j
    rw [signs];exact DescentSharedCableNames.Stage.source_grains A native S ready (cableNames k rank) e
  have flags : issued.live=true ∧ issued.picked=markedChoice A.cap profile (panel h g) x (out e).val :=
    (native_seat_flags (short:=short) A native S ready groups hosts win hm profile dest m hub lay bytes slots roster h g x (out e)).2
      (units.trans_ne e.property.ne')
  have picked:=marked_choice_read A native S ready rank win he coord named fit winner df order profile e
  have selected : issued.picked=(GadgetNetwork.selected W.graph (colorPick W.graph W.core home color A.cap) e.val).isSome :=by
    have here := spread_hit groups.toEmbedding hosts terrain₀ z
    exact flags.2.trans ((congrArg (fun row=>markedChoice A.cap profile row x (out e).val) here).trans picked)
  have wire : physical h g x (headSlot A native S ready e)=
      DescentSignedCableCodec.encode (Prepare.signed A native S ready groups.toEmbedding hosts x (headSlot A native S ready e) h g) :=by
    apply (physical_signed_read A native S ready rank groups hosts z x (headSlot A native S ready e)).trans
    apply congrArg DescentSignedCableCodec.encode
    apply Eq.trans _ (prior_handle A native S ready groups.toEmbedding hosts e).symm
    apply (congrArg (DescentSharedCableNames.Stage.signedPanel A native S ready (cableNames k rank) (z,x))
      (origin_position A native S ready e).symm).trans
    exact origin_stored A native S ready rank e
  change ParentIncidence.pathCell A.degree side (ParentIncidence.rawDecode profile x (out e) (Owners.register lay (panel h g))
    (encode _ _ (Owners.registers (ownerWord (short:=short) A native S ready rank win groups hosts profile lay) roster h g))
    ((encode _ _).symm (encode _ _ (fun q=>physical h g (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))
      (finProdFinEquiv (x,headSlot A native S ready e))) issued.live issued.picked role)=_
  simp only [Equiv.symm_apply_apply,wire]
  have reg:Owners.registers (ownerWord (short:=short) A native S ready rank win groups hosts profile lay) roster h g=
      Owners.registers (ownerWord (short:=short) A native S ready rank win groups hosts profile lay) near h g :=by
    funext j
    refine Fin.cases rfl (fun j=>?_) j
    simp only [Owners.registers,Fin.cases_succ]
    rw [show roster h j=near h j from agrees z.2 j]
  rw [reg]
  exact issued_raw_paths A native S ready groups.toEmbedding hosts win he coord named fit winner df order profile lay e side role
    issued flags.1 selected


open DescentSixParty.StarKeys DescentPacking
local notation "N" => W.graph
local notation "traffic" => nativeTraffic N W.core home color
local notation "pick" => colorPick N W.core home color A.cap
local notation "packs" => coloredPack N W.core home color A.cap
variable (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e))
local notation "own" => nativeKey N W.core home color A.cap addr same lay
local notation "venue" => newSite N pick lay packs
local notation "left" e => (venue (GadgetNetwork.source W.graph (e).val))
local notation "right" e => (venue (GadgetNetwork.target W.graph pick (e).val))
local notation "anchor_" e => (⟨anchor pick (e).val,(e).property⟩:Positive)
local notation "point" e => (A.pos (W.graph.src (anchor_ e).val))

include coord named fit winner df order in
theorem original_raw_walk (roster : Fin H→Fin A.degree→Option (Fin H))
    (agrees : ∀v j,roster (hosts v) j=near (hosts v) j)
    (mapped : ∀(z : J×V) j,roster (hosts z.2) j=((rotor A rank) z j).map (fun t=>hosts t.2))
    (symmetric : ∀v v' j,roster v j=some v'→∃i,roster v' i=some v)
    (e : DescentRawCablePanel.Live A pick) (side : Bool) :
    let x:=A.block (W.graph.src (anchor_ e).val)
    let t:=out (anchor_ e)
    let records:=nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m roster hub lay bytes
    let root:=hosts (point e).2
    let tgt:=hosts ((if side then own (right e) else own (left e)).1).2
    ∃p:Fin (breadth A.degree),
      DepotRAM.rawAtSeat fmt profile G.b slots side (records root (groups (point e).1)) x t (role e.val)=Packed.token (some p) ∧
      walk roster root (path p) 4=some tgt :=by
  intro x t records root tgt
  obtain ⟨pair,found,geometry⟩:=raw_parent_actual A native S ready rank win he coord named fit winner df order profile same lay e
  have geo:=ParentIncidence.received geometry (fun z : J×V=>hosts z.2) roster
    (fun z j v hit=>by rw [mapped,hit]; rfl) symmetric side
  dsimp only at geo
  refine ⟨ActorPath.index A.degree (if side then pair.2 else pair.1),?_,?_⟩
  · rw [retained_raw_path_mounted A native S ready groups hosts win he hm profile dest m hub lay bytes slots
      coord named fit winner df order roster agrees (anchor_ e) (role e.val) side,found]
    rfl
  · exact geo.1

include coord named fit winner df order in
/-- The donor coordinate reported by a captured occurrence is exactly the
public halo index at its first owner. The reverse rank is read from the real
walk produced by the captured edge itself. -/
theorem original_capture_slot (roster : Fin H→Fin A.degree→Option (Fin H))
    (listed : ∀v y,y∈A.near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees : ∀v j,roster (hosts v) j=near (hosts v) j)
    (mapped : ∀(z : J×V) j,roster (hosts z.2) j=((rotor A rank) z j).map (fun t=>hosts t.2))
    (symmetric : ∀v v' j,roster v j=some v'→∃i,roster v' i=some v)
    (e : DescentRawCablePanel.Live A pick) (pitch outBits : ℕ) (room : breadth A.degree ≤ 2^outBits) :
    let u : DepotRAM.Material.Setup:=⟨profile,G.b,A.stage.k,DescentHostDegree.gainExponent 20 A.stage.Δ,slots,pitch,outBits⟩
    let accepted:=DescentHaloCompilation.atSource A.near hosts roster listed A.pos A.block coord own
    let donor:=W.graph.src (anchor_ e).val
    let seat : DepotRAM.Material.Seat fmt:=(A.block donor,out (anchor_ e),role e.val)
    let h:=hosts (A.pos donor).2
    let g:=groups (A.pos donor).1
    let records:=nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m roster hub lay bytes h g
    let rev:=DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster h)
    let observation:=DepotRAM.Material.rawObserved fmt u records rev seat
    ∀inside : donor∈accepted.member (left e),
      (observation 4).val*2^k+(A.block donor).val=(accepted.slot (left e) ⟨donor,inside⟩).val :=by
  intro u accepted donor seat h g records rev observation inside
  obtain ⟨p,word,walk_⟩:=original_raw_walk A native S ready groups hosts win he hm profile dest m hub lay bytes slots
    coord named fit winner df order same roster agrees mapped symmetric e false
  exact DescentDatedOperandCoordinates.Ticket.capture_donor fmt u A.near hosts roster listed symmetric A.pos A.block coord own
    (left e) donor inside records seat p word walk_ room

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
