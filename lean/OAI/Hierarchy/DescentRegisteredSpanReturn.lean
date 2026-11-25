import OAI.Hierarchy.DescentOrdinaryArchivedRanges
import OAI.Hierarchy.DescentRegisteredOrdinaryHeaderWriter
import OAI.Hierarchy.DescentOrdinaryArchiveSpans
import OAI.Hierarchy.DescentArchiveSpanRows

namespace OAI
/-! # The three physical range pages after the registered ordinary instruction -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "paidSources" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


local notation "digits" => (v).signedInput floor room.signed
local notation "date₀" => DonorDate.atDate G S gain k i p

variable (exec : OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "opOut" => (v).argumentsAfter floor room.result.operands
  (by rw [(v).after_end floor room.result.geometry]; exact room.result.limit)

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
variable (dates:ℕ→DateCode w) (m:Memory w)
local notation "sourceMem" => DateCode.history dates m i
local notation "work" => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec sourceMem
local notation "meter" => (date₀).counter payload (((date₀).schedule payload seats (v).bitsPerField).rotationEnd prior.io.roster floor) header

omit [Fintype P] in
theorem range_values_at_cursor
    {nextPorts:DatePorts} (posted:dates i=ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room) (point:nextPorts=out)
    (preserved:(meter).endAddr≤(v).finalChart.out ((v).metaEnd floor)) (earlier:header<(meter).endAddr)
    (bitsFit:(v).finalChart.field*(v).resolver.nodes*(v).resolver.lanes≤w)
    {jobs_:Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver} {old_:Books (v).resolver}
    (keys:∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
      (fun h g=>word ((jobs_ j).compiled h g)) (v).resolver.lanes work)
    (rows:∀x pg,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pg) (old_ x pg) (v).resolver.lanes work)
    (B₁:BitDescription n.result) (number₁:Local B₁) (where₁:RangeRoom nextPorts next B₁)
    {K:ℕ} (shape₁:WorldShape p K B₁) (hp₁:0<p)

    (arity:HeaderArity prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header
      pos room exec B₁ number₁ (point ▸ where₁) shape₁ hp₁ dates m)
    (source : ∀x n₀ h₀ g₀ (j:Fin (v).resolver.operands) (f₁:Fin 3),
      let y:=slotAt out next B₁ number₁ (point ▸ where₁) x n₀ h₀ g₀
      y.elim True (fun a=>j.val<(occurrences (shape₁.sites a.1) a.2).length ∨ f₁=2) →
        (DescentOrdinaryAtomFieldRAM.ScalarOperand.take n₀
          (old_ (x.cast coordsB) (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f₁) j)
            h₀ (g₀.cast coordsG))).val=y.elim 0 (fun a=>atSlot (shape₁.sites a.1) a.2 j.val f₁))
    (y:NodeOrder.All B₁) (j:Fin nextPorts.argumentsPerNode) (f₁:Fin 3)
    (need : j.val<(occurrences (shape₁.sites y.1) y.2).length ∨ f₁=2) :
    (rangeRegister nextPorts next B₁ number₁ where₁.capacity where₁.hosts where₁.groups where₁.radix where₁.positive
      (DateCode.history dates m (i+1))).word y j.val f₁=atSlot (shape₁.sites y.1) y.2 j.val f₁:=by
  subst nextPorts
  obtain ⟨metadataWords,printed,_,_⟩:=arity
  exact ordinary_archived_range_values (v) root shelf header prior.io prior.archive.count digits ((v).reachedSources floor)
    steps room.result date₀ pos exec dates m i posted coordsB coordsG preserved earlier next B₁ number₁ where₁
    shape₁ metadataWords old_ jobs_ printed rows keys bitsFit source y j f₁ need

omit [Fintype P] in
theorem span_return_at_cursor
    {nextPorts:DatePorts} (posted:dates i=ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room) (point:nextPorts=out)
    (preserved:(meter).endAddr≤(v).finalChart.out ((v).metaEnd floor)) (earlier:header<(meter).endAddr)
    (bitsFit:(v).finalChart.field*(v).resolver.nodes*(v).resolver.lanes≤w)
    {jobs_:Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver} {old_:Books (v).resolver}
    (keys:∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
      (fun h g=>word ((jobs_ j).compiled h g)) (v).resolver.lanes work)
    (rows:∀x pg,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pg) (old_ x pg) (v).resolver.lanes work)
    (B₁:BitDescription n.result) (number₁:Local B₁) (where₁:RangeRoom nextPorts next B₁)
    {K:ℕ} (shape₁:WorldShape p K B₁) (hp₁:0<p)

    (arity:HeaderArity prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header
      pos room exec B₁ number₁ (point ▸ where₁) shape₁ hp₁ dates m)
    (values:∀(y:NodeOrder.All B₁)(j:Fin nextPorts.argumentsPerNode)(f₁:Fin 3),
      (j.val<(occurrences (shape₁.sites y.1) y.2).length ∨ f₁=2) →
        (rangeRegister nextPorts next B₁ number₁ where₁.capacity where₁.hosts where₁.groups where₁.radix where₁.positive
          (DateCode.history dates m (i+1))).word y j.val f₁=atSlot (shape₁.sites y.1) y.2 j.val f₁) :
    SpanRows nextPorts next B₁ number₁ where₁ shape₁ (DateCode.history dates m (i+1)):=by
  subst nextPorts
  obtain ⟨metadataWords,printed,_,_⟩:=arity
  exact ordinary_archive_spans (v) root shelf header prior.io prior.archive.count digits ((v).reachedSources floor)
    steps room.result date₀ pos exec dates m i posted coordsB coordsG preserved earlier next B₁ number₁ where₁
    shape₁ metadataWords old_ jobs_ printed rows keys bitsFit values

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
