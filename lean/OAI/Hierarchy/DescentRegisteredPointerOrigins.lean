import OAI.Hierarchy.DescentRegisteredOrdinaryHeaderWriter
import OAI.Hierarchy.DescentOrdinarySelectedMotive
import OAI.Hierarchy.DescentChronologicalBundle

namespace OAI
/-! The original physical resolver cases are indexed by the true site and its three numerical coordinates. -/
namespace Hierarchy.DescentSixParty.Reached
open Chronology DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentPacking
open DescentDatedAddressBook DescentOperandStateBanks DescentDatedPriorOperand DescentPackedOperand
open DescentLocalPrivateNames Computability.BorderVNP.Crossing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 650000
variable {F P:Type} [Field F] {dim k i z D wire hist p R:ℕ} {bits:P → ℕ} {U:MarkedWorld F dim P bits}
    {G:PoweredGadget F} {q ε:ℝ} {S:DescentCompiler.AtomSchedule}
    (r:Reached U G q ε S k i z D wire hist) (cpu:PhysicalOrdinary F P)
    (B:BitDescription U) (number:Local B) (shape:WorldShape p R B) (hp:0<p) (pin:P → ℕ)
    (jobs:Fin cpu.resolver.jobs → DescentDatedPriorOperand.Source cpu.resolver)
local notation "rcp" t:arg => (shape.sites t).recipe hp
local notation "loc" t:arg => Reached.NodeCells.coordinate r t

def PointerSites : Prop :=
  ∀(u:U.graph.Site) (bl:Fin cpu.resolver.blocks) (host:Fin cpu.resolver.hosts) (group:Fin cpu.resolver.groups),
    bl.val=(loc u).2.2.val → host.val=(loc u).1.val → group.val=(loc u).2.1.val →
    ∀(nodes:Fintype.card (B.recipe u).Node≤cpu.resolver.nodes)
      (argFit:∀nodeIndex,(rcp u).arity nodeIndex≤cpu.resolver.operands),
    let idx:=(number u).toEmbedding.trans (Fin.castLEEmb nodes)
    let mouth:=cpu.finalChart.mouths (rcp u) idx argFit
    let row :=fun (n:(B.recipe u).Node) (j:Fin ((rcp u).arity n))=>cpu.issuedFragment jobs bl host group (mouth ⟨n,j⟩)
    (∃hidden:(rcp u).UsedWord↪Key,cpu.SourceKeys jobs bl host group (rcp u) idx argFit hidden) ∧
    (∀n (j:Fin ((rcp u).arity n)) (e:Incident U.graph u) a (enough:(a+1)*p≤U.graph.width e.val),
      (rcp u).operand n j=.inl ⟨.inl e,a,enough⟩ →
      Pointer.ofKey 0 (resolve (row n j))=r.firstCable hp u e a enough) ∧
    ∀n (j:Fin ((rcp u).arity n)) (e:Attached U.graph u) a (enough:(a+1)*p≤bits e.val),
      (rcp u).operand n j=.inl ⟨.inr e,a,enough⟩ → resolve (row n j)=Key.pin (pin e.val) a

end
end Hierarchy.DescentSixParty.Reached

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentDatedPriorOperand
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P) {p R:ℕ}
local notation "T" => v.prior.placement.stage
variable (arch:Archive v.world) (number:Local arch.bit) (shape:WorldShape p R arch.bit) (hp:0<p) (one:1≤R)
    (width:∀x,p∣v.bits x) (pin:P → ℕ) (jobs:Fin v.resolver.jobs → DescentDatedPriorOperand.Source v.resolver)
    (picked:(v.prior.placement.stage.result v.nonnegative).Choice) (chosen:HEq picked v.choice)
local notation "atChosen" => atSelected v picked chosen

/-- Source fields proved on the genuine selected stage give the same fields for the
chronological target with its own local order and affine slices. -/
theorem AtSelected.recorded_headers
    (native:∀unit:p∣(T).z,Reached.PointerSites (atChosen).next v ((atChosen).link.advance arch).bit
      (advance (atChosen).link arch number) (afterOrdinary hp one width (atChosen).link arch shape unit) hp pin jobs)
    (step:p∣v.stage.z) :
    Reached.PointerSites v.target v (v.ticket.advance arch).bit (advance v.ticket arch number)
      (afterOrdinary hp one width v.ticket arch shape step) hp pin jobs :=by
  let M := fun (rate:ℝ) (t:StageInput v.world v.gadget rate v.ε)
     (c:(t.result v.nonnegative).Choice) (n:Normalize ((t.result v.nonnegative).state c))
     (r:Reached n.result v.gadget v.q v.ε v.schedule v.k (v.age+1) v.nextZ v.nextDegree v.wire v.hist)
     (link:OrdinaryLink v.prior v.nonnegative t c n r)=>
       ∀unit:p∣t.z,Reached.PointerSites r v (link.advance arch).bit (advance link arch number)
         (afterOrdinary hp one width link arch shape unit) hp pin jobs
  exact (AtSelected.on_ticket v picked chosen (atChosen) M native) step

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 650000
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ → Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "paidSources" => (v).reachedSources floor

open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette
open DescentHistoryOrder DescentDatedPriorOperand DescentOperandStateBanks DescentRetainedRangeDigits
open DescentPackedOperand DescentOrdinaryFinal DescentLocalPrivateNames Computability.BorderVNP.Crossing
variable [Fintype P]
local notation "modelWorld" => n.result
local notation "out" => ordinaryPorts prior ticket op gain tail p f drift degree payload seats root ordinary
local notation "coordsB" => (registered_blocks_groups prior ticket op gain tail p f drift degree payload seats root ordinary).1
local notation "coordsG" => (registered_blocks_groups prior ticket op gain tail p f drift degree payload seats root ordinary).2
local notation "layoutEq" => ordinary_range_layout (v) floor coordsB coordsG
local notation "ports" => out
variable (B:BitDescription modelWorld) (number:Local B) (places:RangeRoom out next B)
    {R:ℕ} (shape:WorldShape p R B) (hp:0<p) (pin:P → ℕ)
variable (jobs:Fin (v).resolver.jobs → DescentDatedPriorOperand.Source (v).resolver)
  (written:∀(u : n.result.graph.Site) nodeIndex,((shape.sites u).recipe hp).arity nodeIndex≤(v).resolver.operands)

omit [Fintype P] in
theorem printed_header_sites (active:Reached.PointerSites next (v) B number shape hp pin jobs) :
    HeaderSites prior ticket op gain tail p f drift degree payload seats root ordinary B number places
      shape hp pin jobs written:=by
  intro u
  exact active u _ _ _ rfl rfl rfl (places.capacity u) (written u)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
