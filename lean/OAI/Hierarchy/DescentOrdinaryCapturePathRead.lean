import OAI.Hierarchy.DescentOrdinaryCapturePathMeaning
import OAI.Hierarchy.DescentOrdinaryRetainedPaths

namespace OAI
/-! # Recover the true rooted walks directly from the preceding native donor words -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentSIMDLookup DescentSixParty DescentHostDirectory DescentCableDonorNames DescentStageEdgeReceipt
open DescentScalarVenueMask DescentRawCablePanel DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
set_option maxHeartbeats 1200000
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z loc b c : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (groups : J↪Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
local notation "R" => 2^k
local notation "D" => A.degree
local notation "rank" => groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "next" => rotor A rank
local notation "panel" => terrain (short:=short) A native S ready (cableNames k rank) win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "prior" => DescentSharedCableNames.Stage.outgoing A native S ready
local notation "prep" => Prepare.signed A native S ready groups hosts
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed (groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)))
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (lay : Bool)

local notation "priorDir" => DescentScalarVenueMask.Stage.board (short:=short) A native S ready groups hosts win profile lay
local notation "neighbor" => hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))
local notation "dirAt" => DescentScalarVenueMask.Stage.registerRows (short:=short) A native S ready rank win profile lay
local notation "sensors" => spread groups hosts panel
local notation "pathAt" => rawParentRows (short:=short) A native S ready rank win profile lay
local notation "picker" => colorPick N W.core home color A.cap
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
variable (e : DescentSharedCableNames.Stage.Positive A)
local notation "v" => W.graph.src e.val
local notation "z" => A.pos v
local notation "x" => A.block v
local notation "s" => prior e
local notation "h" => hosts (Prod.snd z)
local notation "g" => groups (Prod.fst z)

private theorem raw_zero_fields {a r : ℕ} : (encode a r).symm 0=(fun _=>0) :=by
  apply (encode a r).symm_apply_eq.mpr;apply Fin.ext
  change 0=(finFunctionFinEquiv (fun _:Fin r=>(0:Cell a))).val
  simp


include coord named fit winner df edgeOrder in
theorem issued_raw_paths (side : Bool) (j : Fin 11) (donor : Donor loc b c)
    (live : donor.live=true) (matched : donor.picked=(GadgetNetwork.selected N picker e.val).isSome) :
    ParentIncidence.pathCell D side (ParentIncidence.rawDecode profile x s (Owners.register lay (sensors h g))
      (encode _ (D+1) (Owners.registers priorDir neighbor h g)) (DescentSignedCableCodec.encode (prep x (headSlot A native S ready e) h g))
      donor.live donor.picked j)=ParentIncidence.pathCell D side (pathAt e j) :=by
  rw [prior_handle A native S ready groups hosts e,spread_hit,DescentScalarVenueMask.Stage.rows_at,
    live,ParentIncidence.raw_decoded]
  let here:=fun z'=>resolved A.cap profile (panel z') lay
  let away:=fun z' (p : Fin D) y=>(next z' p).elim (0,0,0) (fun other=>here other y)
  have self : Owners.addressed (dirAt z 0)=here z:=funext (fun y=>Owners.addressed_read ..)
  have peers (p : Fin D) : Owners.addressed (dirAt z p.succ)=away z p:=by
    funext y;cases step:next z p with
    | some t=>simp only [away,DescentScalarVenueMask.Stage.registerRows,Fin.cases_succ,step,Option.elim_some];exact Owners.addressed_read ..
    | none=>simp [away,DescentScalarVenueMask.Stage.registerRows,step,Owners.addressed,raw_zero_fields]
  dsimp only
  rw [self,funext peers,matched,←parent_chosen A native S ready rank win he coord named fit winner df edgeOrder profile e]
  rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

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

include coord named fit winner df order in
theorem retained_raw_path (e : Positive) (role : Fin 11) (side : Bool) :
    let v:=W.graph.src e.val
    DepotRAM.rawAtSeat fmt profile G.b slots side (scene (hosts (A.pos v).2) (groups (A.pos v).1)) (A.block v) (out e) role=
      ParentIncidence.pathCell A.degree side (rawParentRows (short:=short) A native S ready rank win profile lay e role) :=by
  intro v
  let z:=A.pos v
  let h:=hosts z.2
  let g:=groups z.1
  let x:=A.block v
  let raw:=scene h g
  let issued:=DepotRAM.seatDonor fmt profile G.b slots raw x (out e)
  have units : DescentSharedCableNames.Stage.sourceGrains (physical h g x) (out e)=A.grainCount e.val :=by
    have signs : physical h g x=fun j=>DescentSignedCableCodec.encode
        (DescentSharedCableNames.Stage.signedPanel A native S ready (cableNames k rank) (z,x) j):=by
      funext j;exact physical_signed_read A native S ready rank groups hosts z x j
    rw [signs];exact DescentSharedCableNames.Stage.source_grains A native S ready (cableNames k rank) e
  have flags : issued.live=true ∧ issued.picked=markedChoice A.cap profile (panel h g) x (out e).val :=
    (native_seat_flags (short:=short) A native S ready groups hosts win hm profile dest m hub lay bytes slots near h g x (out e)).2
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
    (encode _ _ (Owners.registers (ownerWord (short:=short) A native S ready rank win groups hosts profile lay) near h g))
    ((encode _ _).symm (encode _ _ (fun q=>physical h g (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))
      (finProdFinEquiv (x,headSlot A native S ready e))) issued.live issued.picked role)=_
  simp only [Equiv.symm_apply_apply,wire]
  exact issued_raw_paths A native S ready groups.toEmbedding hosts win he coord named fit winner df order profile lay e side role
    issued flags.1 selected

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
