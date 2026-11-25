import OAI.Hierarchy.DescentOrdinaryDonorPathRAM

namespace OAI
/-! # Both published endpoint paths on each genuine old first-grain donor -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentSIMDLookup DescentSixParty DescentHostDirectory DescentCableDonorNames DescentStageEdgeReceipt
open DescentScalarVenueMask DescentRawCablePanel DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
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
local notation "pathAt" => parentRows (short:=short) A native S ready rank win profile lay
local notation "picker" => colorPick N W.core home color A.cap
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
variable (e : DescentSharedCableNames.Stage.Positive A)
local notation "v" => W.graph.src e.val
local notation "z" => A.pos v
local notation "x" => A.block v
local notation "s" => prior e
local notation "h" => hosts (Prod.snd z)
local notation "g" => groups (Prod.fst z)

private theorem zero_fields {a r : ℕ} : (encode a r).symm 0=(fun _=>0) :=by
  apply (encode a r).symm_apply_eq.mpr;apply Fin.ext
  change 0=(finFunctionFinEquiv (fun _:Fin r=>(0:Cell a))).val
  simp

/-- Signed source addresses use the zero sign and the old source's first grain. -/
theorem origin_position :
    DescentSharedCableNames.Stage.signed A native S ready z x (originPort A e)=headSlot A native S ready e := by
  apply Fin.ext
  change (finProdFinEquiv ((0 : Fin 2),s)).val= (s).val
  simp [finProdFinEquiv_apply_val]

theorem prior_handle : prep x (headSlot A native S ready e) h g=some (sourceHandle A native S ready rank e) := by
  have present : ∃u : J×V,groups u.1=g ∧ hosts u.2=h:=⟨z,rfl,rfl⟩
  have id : present.choose=z:=Prod.ext (groups.injective present.choose_spec.1) (hosts.injective present.choose_spec.2)
  simp only [Prepare.signed,Prepare.spreadField,dite_eq_left present,id]
  rw [←origin_position A native S ready e]
  exact origin_stored A native S ready rank e

include coord named fit winner df edgeOrder in
/-- At the exact old block and first-grain address, the preceding terrain, one-hop
owner register, signed record, and donor mask completely specify the two rooted paths. -/
theorem issued_paths (side : Bool) (j : Fin 11) (donor : Donor loc b c)
    (live : donor.live=true) (matched : donor.picked=(GadgetNetwork.selected N picker e.val).isSome) :
    (encode _ 11).symm (ParentIncidence.paths profile x s side (Owners.register lay (sensors h g))
      (encode _ (D+1) (Owners.registers priorDir neighbor h g)) (DescentSignedCableCodec.encode (prep x (headSlot A native S ready e) h g))
      (ParentIncidence.liveGate donor)) j=ParentIncidence.pathCell D side (pathAt e j) :=by
  rw [prior_handle A native S ready groups hosts e,spread_hit,DescentScalarVenueMask.Stage.rows_at,
    ParentIncidence.paths_read _ _ _ _ _ _ _ _ _ live]
  let here:=fun z'=>resolved A.cap profile (panel z') lay
  let away:=fun z' (p : Fin D) y=>(next z' p).elim (0,0,0) (fun other=>here other y)
  have self : Owners.addressed (dirAt z 0)=here z:=funext (fun y=>Owners.addressed_read ..)
  have peers (p : Fin D) : Owners.addressed (dirAt z p.succ)=away z p:=by
    funext y;cases step:next z p with
    | some t=>simp only [away,DescentScalarVenueMask.Stage.registerRows,Fin.cases_succ,step,Option.elim_some];exact Owners.addressed_read ..
    | none=>simp [away,DescentScalarVenueMask.Stage.registerRows,step,Owners.addressed,zero_fields]
  dsimp only
  rw [self,funext peers,matched,←parent_chosen A native S ready rank win he coord named fit winner df edgeOrder profile e]
  rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
