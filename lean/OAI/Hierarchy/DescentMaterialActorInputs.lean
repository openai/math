import OAI.Hierarchy.DescentOrdinaryVenueClipNumbers
import OAI.Hierarchy.DescentMaterialRegisterJoin
import OAI.Hierarchy.DescentSignedRoleScans
import OAI.Hierarchy.DescentScalarOwnerBoardRead
import OAI.Hierarchy.DescentDonorNativeParts

namespace OAI
/-! Print all real old and six-party actor tickets without storing any expanded owner/head word. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.ActorInputs
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPackedColony DescentSharedCableNames
open DescentSixParty.Chronology DescentHaloWalkRAM DescentScalarVenueMask
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) {H G M w : ℕ}
abbrev Label := Publisher.Label s.blocks s.cap
def count :=s.blocks*(1+s.cap*6)
def token (profile slots raw : ℕ) (v : Parts s) (active : Cell (1*s.blocks)) (l : Label s) : Ticket (breadth s.degree) raw :=
  let old:=Owners.render s.blocks s.degree (2*s.cap) s.short s.cap profile v.terrain
  let born:=Owners.report s.blocks s.degree (2*s.cap) s.short s.cap profile v.terrain v.owners
  Publisher.ticket (D:=s.degree) (d:=s.short) (slots:=slots) l active old born
def law (profile slots raw : ℕ) (side : Fin 2) (j : ℕ) (v : Cell (bits s)) :
    Cell (Packed.bits (if side=0 then breadth s.degree else raw)) :=
  if index:j<count s then
    let y:=(DescentRawCablePanel.pair (totalBits s) (1*s.blocks)).symm v
    Publisher.projection _ raw side (token s profile slots raw (separate s y.1) y.2 (finProdFinEquiv.symm ⟨j,index⟩))
  else 0

theorem decoded (profile slots raw : ℕ) (side : Fin 2) (l : Label s) (v : Parts s) (active : Cell (1*s.blocks)) :
    law s profile slots raw side (finProdFinEquiv l).val (RegisterJoin.joined (combine s v) active)=
      Publisher.projection _ raw side (token s profile slots raw v active l) :=by
  have live : (finProdFinEquiv l).val < count s := (finProdFinEquiv l).isLt
  simp only [law,dite_eq_left live,RegisterJoin.joined,Equiv.symm_apply_apply,separate_combine]
  exact congrArg (fun t => Publisher.projection _ raw side (token s profile slots raw v active t)) (finProdFinEquiv.symm_apply_apply l)

def bank (H G M base : ℕ) (j : Label s) : Bank :=
  ⟨RoleScans.home (bits s) H G M (count s) base+(finProdFinEquiv j).val*(H*chunks G M),
    Nat.clog 2 (H*chunks G M)⟩

def issued (profile slots raw H G M w base : ℕ) (joined : Bank) (side : Fin 2) : NativePhase w :=
  let f:=law s profile slots raw side
  ⟨RoleScans.cpu f H G M w base (count s) joined,RoleScans.ticks (bits s) H G M (count s),
    RoleScans.image f H G M base (count s) joined,
    cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)⟩
def afterSide (H G M base : ℕ):=RoleScans.limit (bits s) H G M base (count s)
variable (profile slots raw base : ℕ) (old : Bank) (m : Memory w) (side : Fin 2)
    (lower : old.base+old.size≤base) (space : H*chunks G M≤old.size)
    (pay : M*max (bits s) (Packed.bits (if side=0 then breadth s.degree else raw))≤w/2)
    (room : afterSide s H G M base<2^w)
include lower space pay room in
theorem any :
    let phase:=issued s profile slots raw H G M w base old side
    phase.Runs m ∧ (∀a,a<base ∨ afterSide s H G M base≤a→phase.image m a=m a) :=by
  intro phase
  have ok:=RoleScans.any_run (law s profile slots raw side) base (count s) old m lower space pay room
  exact ⟨ok.1,ok.2.1⟩
include lower space pay room in
theorem chip (v : Fin H→Fin G→Parts s) (active : Fin H→Fin G→Cell (1*s.blocks))
    (prior : Reads old (fun h g=>RegisterJoin.joined (combine s (v h g)) (active h g)) M m) (l : Label s) :
    Reads (bank s H G M base l) (fun h g=>Publisher.projection _ raw side (token s profile slots raw (v h g) (active h g) l)) M
      ((issued s profile slots raw H G M w base old side).image m) :=by
  intro p
  simpa only [decoded,issued,bank] using (RoleScans.read (law s profile slots raw side) base (count s) old m lower space pay room _
    prior (finProdFinEquiv l) p)

end
end Hierarchy.DescentRawCablePanel.DepotRAM.ActorInputs


namespace Hierarchy.DescentScalarVenueMask.Stage
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage DescentSixParty DescentStageEdgeReceipt
open DescentGroupPeerOrder DescentSharedCableNames DescentPackedColony DescentHaloWalkRAM DescentRawCablePanel
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (group : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes slots : ℕ)
local notation "grp" => group.toEmbedding
local notation "rank" => groupRank (group.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "near" => hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "state" => nativeParts (short:=short) A native S ready rank win group hosts hm profile dest m near hub lay bytes
local notation "t" => tokens (short:=short) A native S ready rank win profile lay grp hosts
theorem retained_actor (x : Fin (2^k)) (j : Fin (1+A.cap*6)) (h : Fin H) (g : Fin Z) :
    DepotRAM.ActorInputs.token fmt profile slots (2^(k+1)*slots) (state h g) (Prepare.actors A grp hosts h g) (x,j)=
      t slots x j h g :=
  published_eq (short:=short) A native S ready grp hosts win profile lay slots x j h g

end
end Hierarchy.DescentScalarVenueMask.Stage

end OAI
