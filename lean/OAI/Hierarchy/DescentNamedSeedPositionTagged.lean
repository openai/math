import OAI.Hierarchy.DescentNamedSeedPositionTaggedCore
import OAI.Hierarchy.DescentNamedPrivateArchive
import OAI.Hierarchy.DescentNormalizedSeedEntry
import OAI.Hierarchy.DescentArchivePadInputs

namespace OAI
/-! The initialized seed archive in the original uniform word and address price. -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentCompiler DescentSixParty DescentInitialHost DescentSeedRoot Catalyst
open DescentSixParty.SeedNamed DescentSixParty.Chronology DescentSixParty.Chronology.RegisterTimeline
open DescentKernelHistory DescentPrimitivePalette DescentColonies DescentRotor
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall DescentWideSeedFlags
open DescentExterior DescentExteriorShelf DescentGL Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1000000
open private oneNodeEach from OAI.Hierarchy.DescentDatedSeedOriginalCoordinates
open private positionedSeedDvd from OAI.Hierarchy.DescentNamedSeedPositionTaggedCore
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open DescentLocalArchiveOrder DescentDatedSeedStartup

variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec) (t f g drift : ℕ) (v : SeedHeader.Input F)
    (h : ℕ) {w : ℕ}
local notation "l" => v.layout G t f g drift h
local notation "s" => (l).seedWidth
local notation "header" => v.base G h-1
local notation "lo" => selectorBase v.circuit v.schedule.copies s h v.steps.length
local notation "pitch" => DescentPackedEpochShelves.grain (h/2) G.C
local notation "origin" => end_ (lo+extent pitch v.steps) G.C pitch
local notation "E" => ExteriorCount v.circuit
local notation "front" => publicFront v.circuit v.schedule.copies s h G.C v.steps v.j v.rest
local notation "extra" => v.appendix.words (E*2^(v.j+v.rest))
local notation "Z" => v.schedule.grainAt G.b v.p 0
local notation "M" => Primitive.paletteLanes G op s Z h v.k

variable (radix : v.schedule.radix=2^v.k) (hosts : Fintype.card (Vertex v.circuit)≤v.hosts)
    (seed : Select v.circuit v.schedule.copies ((v.layout G t f g drift h).seedWidth)→v.labels)
    (x : Fin (ExteriorCount v.circuit)→Plane v.j v.rest→Fin ((v.layout G t f g drift h).seedWidth)→Bool) (z : v.labels⊕Hidden (ExteriorCount v.circuit) v.j v.rest ((v.layout G t f g drift h).seedWidth)→Bool) (back : Memory w)
local notation "raw" => Root.appended (origin+17*DescentExteriorShelf.span v.j v.rest s E) extra
  (Root.widePackedImage v.circuit v.schedule.copies s h w seed lo G.C pitch v.steps origin x z) back
local notation "checked" => countedAt v.circuit v.schedule.copies s h seed (z∘Sum.inl) raw
local notation "done" => DescentDatedSeedStartup.Input.completeImage G op v.circuit (v.schedule.initialDigits radix)
  hosts l header h Z checked

local notation "flag" => DescentWideSeedFlags.endInput v.circuit v.schedule.copies s h
local notation "rows₀" => DescentPackedSeed.rows v.circuit v.schedule.copies s h
local notation "finish" => (DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts (v.schedule.groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress v.circuit l v.hosts (v.schedule.groupCount 0) v.k)
local notation "start" => (⟨DatePorts.initial G op v.circuit v.schedule.copies l v.k v.hosts (v.schedule.groupCount 0) h Z,
  Primitive.initialEnd v.circuit v.schedule.copies s h v.k v.hosts (v.schedule.groupCount 0) M finish⟩ : RegisterTimeline.Position)
local notation "pins" => Σ _ : Fin v.schedule.copies,Fin (Fintype.card (Port v.pins v.circuit.width))
local notation "portion" => (fun _ : pins=>s*1)
variable {q ε : ℝ} {wire epoch z' D' R : ℕ} {c : (initialGroup v.circuit v.schedule.copies s).Choice}
    (o : Origin v.circuit («s»:=(v.layout G t f g drift h).seedWidth) («G»:=G) (S:=v.schedule) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) c (v.schedule.initialDigits radix))
    (hp : 0<v.p) (units : 1≤R) (menu : Runnable F op)
    {lastWorld : MarkedWorld F 0 pins portion} (target : Reached lastWorld G q ε v.schedule v.k epoch z' D' wire s)
    (path : Path o.source target)

attribute [local irreducible] Origin.archiveOrder DescentDatedSeedStartup.Input.issuedSeedClaimAtFirst
local notation "claim" => @DescentDatedSeedStartup.Input.issuedSeedClaimAtFirst F _ v.schedule G op
  v.k v.arity v.pins w v.circuit radix l Z q ε wire c o menu (Origin.archiveOrder o) v.p R hp units
  (positionedSeedDvd G t f g drift v h) epoch z' D' lastWorld target path

/-- The selected width, operand pitch and actual decoded ballot start the chronological
archive. Occupied nodes use their original singleton rank, and the initialized pages also
cover every unused slot and every source site outside the paid census. -/
theorem position_tagged {n d K : ℕ} (board : NonlinearExpanders.Graph n d)
    (ready : v.Ready G board op t f g drift h w K)
    (groups : v.schedule.baseGroups=2^v.tail) (epochs : 0<v.schedule.height) (budget : G.b≤2^v.schedule.capGain)
    (positive : 0<(l).operandLanes) (decoded : decode v.circuit ((z∘Sum.inl)∘seed)=some c) :
    (start).ports.held o.source (start).floor done ∧ claim start done ∧ (start).ports.ArchiveTags done :=by
  exact v.position_tagged_words G op t f g drift h radix hosts seed x z back o hp units menu target path
    ready.digits ready.live ready.machine ready.printed ready.signed ready.«fields» ready.seedWidth ready.space
    groups epochs budget positive decoded

/-- The initially allocated role archive has enough original packed rows and a live lane
for the very first tagged predecessor retiling. -/
theorem position_role_rows {n d K : ℕ} (board : NonlinearExpanders.Graph n d)
    (ready : v.Ready G board op t f g drift h w K) :
    (start).ports.RoleRows ∧ 0<(start).ports.roleLanes :=
  ⟨DatePorts.initial_role_rows G op v.circuit v.schedule.copies l v.k v.hosts (v.schedule.groupCount 0) h Z,ready.live⟩

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
