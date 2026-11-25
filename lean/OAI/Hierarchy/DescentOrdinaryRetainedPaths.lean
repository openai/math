import OAI.Hierarchy.DescentOrdinaryRawSeatWords
import OAI.Hierarchy.DescentOrdinaryDonorPathDepot
import OAI.Hierarchy.DescentDonorNativeParts

namespace OAI
/-! # Both numeric path sheets at the original outgoing seat of each retained wire -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentSixParty DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (f : Shape) (profile b slots : ℕ) (side : Bool)
def atSeat (v : Parts f) (x : Fin f.blocks) (t : Fin f.cap) (j : Fin 11) :=
  (encode (ParentIncidence.pathBits f.degree) 11).symm
    ((encode _ (f.blocks*f.cap)).symm (pathSheet f profile b slots side v) (finProdFinEquiv (x,t))) j

theorem seat_read (v : Parts f) (x : Fin f.blocks) (t : Fin f.cap) (j : Fin 11) :
    atSeat f profile b slots side v x t j=
      (encode _ 11).symm (ParentIncidence.paths profile x t side v.terrain v.owners
        ((encode _ (f.blocks*(2*f.cap))).symm v.cables (finProdFinEquiv (x,t.castLE (by omega))))
        (ParentIncidence.liveGate (seatDonor f profile b slots v x t))) j :=by
  simp only [atSeat,pathSheet,seatDonor,Equiv.symm_apply_apply]

theorem seat_flags (lay : Bool) (u : Panel f.blocks f.degree (2*f.cap) f.short)
    (sig : Fin f.blocks→Fin (2*f.cap)→Cell (DescentSignedCableCodec.width f.degree f.cap))
    (own : Fin (f.degree+1)→Owners.Register f.blocks f.degree f.short)
    (ord hubs : Fin (breadth f.degree)→Fin (breadth f.degree+1)) (fresh : Fin f.blocks→Fin f.cap→Fin 8→Cell f.widths)
    (x : Fin f.blocks) (t : Fin f.cap) :
    let donor:=seatDonor f profile b slots (operands f lay u sig own ord hubs fresh) x t
    let units:=DescentSharedCableNames.Stage.sourceGrains (sig x) t
    (units=0→donor.live=false) ∧ (units≠0→donor.live=true ∧ donor.picked=Stage.markedChoice f.cap profile u x t.val) :=by
  intro donor units
  dsimp only [donor,seatDonor]
  rw [printed_parts,unpack_pack]
  constructor
  · intro zero;simp [depot,zero,units,emptyDonor] at *
  · intro nonzero;simp [depot,nonzero,units,observedDonor] at *

end
end Hierarchy.DescentRawCablePanel.DepotRAM

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
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
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)))
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (order : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)

theorem native_seat_flags (roster : Fin H → Fin A.degree → Option (Fin H))
    (h : Fin H) (g : Fin Z) (x : Fin (2^k)) (t : Fin A.cap) :
    let v := nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m roster hub lay bytes h g
    let donor := DepotRAM.seatDonor fmt profile G.b slots v x t
    let units := DescentSharedCableNames.Stage.sourceGrains (physical h g x) t
    (units=0 → donor.live=false) ∧
      (units≠0 → donor.live=true ∧ donor.picked=markedChoice A.cap profile (panel h g) x t.val) := by
  unfold nativeParts
  exact DepotRAM.seat_flags fmt profile G.b slots lay (panel h g) (physical h g) _ _ _ _ x t

include coord named fit winner df order in
theorem retained_path_mounted (roster : Fin H→Fin A.degree→Option (Fin H))
    (agrees : ∀v j,roster (hosts v) j=near (hosts v) j) (e : Positive) (role : Fin 11) (side : Bool) :
    let v:=W.graph.src e.val
    DepotRAM.atSeat fmt profile G.b slots side (nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m roster hub lay bytes (hosts (A.pos v).2) (groups (A.pos v).1)) (A.block v) (out e) role=
      ParentIncidence.pathCell A.degree side (parentRows (short:=short) A native S ready rank win profile lay e role) :=by
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
  refine (DepotRAM.seat_read fmt profile G.b slots side raw x (out e) role).trans ?_
  change (encode _ 11).symm (ParentIncidence.paths profile x (out e) side (Owners.register lay (panel h g))
    (encode _ _ (Owners.registers (ownerWord (short:=short) A native S ready rank win groups hosts profile lay) roster h g))
    ((encode _ _).symm (encode _ _ (fun q=>physical h g (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))
      (finProdFinEquiv (x,headSlot A native S ready e))) (ParentIncidence.liveGate issued)) role=_
  simp only [Equiv.symm_apply_apply,wire]
  have reg:Owners.registers (ownerWord (short:=short) A native S ready rank win groups hosts profile lay) roster h g=
      Owners.registers (ownerWord (short:=short) A native S ready rank win groups hosts profile lay) near h g :=by
    funext j
    refine Fin.cases rfl (fun j=>?_) j
    simp only [Owners.registers,Fin.cases_succ]
    rw [show roster h j=near h j from agrees z.2 j]
  rw [reg]
  exact issued_paths A native S ready groups.toEmbedding hosts win he coord named fit winner df order profile lay e side role
    issued flags.1 selected

include coord named fit winner df order in
theorem retained_path (e : Positive) (role : Fin 11) (side : Bool) :
    let v:=W.graph.src e.val
    DepotRAM.atSeat fmt profile G.b slots side (scene (hosts (A.pos v).2) (groups (A.pos v).1)) (A.block v) (out e) role=
      ParentIncidence.pathCell A.degree side (parentRows (short:=short) A native S ready rank win profile lay e role) :=by
  exact retained_path_mounted A native S ready groups hosts win he hm profile dest m hub lay bytes slots
    coord named fit winner df order near (fun _ _=>rfl) e role side

theorem retained_path_hole (h : Fin H) (g : Fin Z) (x : Fin (2^k)) (t : Fin A.cap) (role : Fin 11) (side : Bool)
    (empty : ¬∃e : Positive,oldSlot A S ready native hosts groups e=(h,finProdFinEquiv (finProdFinEquiv (g,x),t))) :
    DepotRAM.atSeat fmt profile G.b slots side (scene h g) x t role=0 :=by
  have zero:=source_empty A native S ready rank groups hosts h g x t empty
  have blank : (DepotRAM.seatDonor fmt profile G.b slots (scene h g) x t).live=false :=
    (native_seat_flags (short:=short) A native S ready groups hosts win hm profile dest m hub lay bytes slots near h g x t).1 zero
  refine (DepotRAM.seat_read fmt profile G.b slots side (scene h g) x t role).trans ?_
  exact ParentIncidence.paths_missing _ _ _ _ _ _ _ _ blank role

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
