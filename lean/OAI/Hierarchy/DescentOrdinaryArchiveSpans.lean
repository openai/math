import OAI.Hierarchy.DescentDatedOrdinaryRangeExit
import OAI.Hierarchy.DescentReachedIssuedHeaders
import OAI.Hierarchy.DescentRegisterArchiveValues

namespace OAI
/-! # The three archived range digits after an ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentPackedColony DescentSIMDLookup DescentDatedPriorOperand DescentOperandStateBanks
open DescentKernelHistory DescentDatedAddressBook DescentLocalArchiveOrder DescentBundleHistory
open DescentRetainedRangeDigits DescentColonies DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000

/-- A field is consumed on its original block, register host and flattened
argument index. All intermediate casts preserve both the physical row and its
lane, including in the final partial word. -/
private theorem reindex_span {l L:Layout} (e:l=L) {b w:ℕ} {out:ℕ} {m:Memory w}
    (x:Fin l.blocks) (j:Fin l.operands) (f:Fin 3)
    (values:Fin L.hosts→Fin L.groups→Cell (b*L.nodes))
    (read:Reads (previousBank L out (x.cast (congrArg Layout.blocks e))
      (page (DescentRetainedRangeDigits.page f) (j.cast (congrArg Layout.operands e)))) values L.lanes m) :
    ∃cells:Fin l.hosts→Fin l.groups→Cell (b*l.nodes),
      Reads (previousBank l out x (page (DescentRetainedRangeDigits.page f) j)) cells l.lanes m ∧
      ∀h g n,((encode b l.nodes).symm (cells h g) n).val=
        ((encode b L.nodes).symm (values (h.cast (congrArg Layout.hosts e)) (g.cast (congrArg Layout.groups e)))
          (n.cast (congrArg Layout.nodes e))).val:=by
  subst L
  exact ⟨values,read,fun _ _ _=>rfl⟩

variable {F P:Type} [Field F] (v:PhysicalOrdinary F P) (root shelf header:ℕ)
  (input:Dated.Operands) (count:Bank) (wires:v.signed.Input) (sources:StageVenueTail.Sources)
  {w:ℕ} (steps:PhysicalOrdinary.ResultSteps w) (bank:v.ResultRoom (v.stageStart root) sources w)
  (d:DonorDate) (positive:0<d.exponent) (fit:PhysicalOrdinary.Room v root shelf header input count wires steps d)
local notation "floor" => v.stageStart root
local notation "meter" => d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster floor) header
local notation "op" => v.argumentsAfter floor bank.operands (by rw [v.after_end floor bank.geometry];exact bank.limit)
local notation "code" => v.date root shelf header input count wires sources steps bank d positive
variable (dates:ℕ→DateCode w) (initial:Memory w) (i:ℕ) (issued:dates i=(v.date root shelf header input count wires sources steps bank d positive))
local notation "snap" => DateCode.history dates initial i
local notation "work" => v.beforeArgumentWrite root shelf header input count wires sources steps d positive fit snap
local notation "written" => (op).image work
local notation "target" => DateCode.history dates initial (i+1)
local notation "ports" => ordinary v floor
local notation "base" => v.finalChart.out (v.metaEnd floor)
variable (blocks:2^v.venue.k=v.resolver.blocks) (groups:v.venue.groups=v.resolver.groups)
  (saved:((d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster (v.stageStart root)) header)).endAddr≤(v.finalChart.out (v.metaEnd (v.stageStart root)))) (away:header<((d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster (v.stageStart root)) header)).endAddr)
local notation "layoutEq" => ordinary_range_layout v floor blocks groups
variable {k age z D wire hist dim:ℕ} {bits:P→ℕ} {W:MarkedWorld F dim P bits}
  {G:PoweredGadget F} {q ε:ℝ} {S:AtomSchedule} (r:Reached W G q ε S k age z D wire hist)
  (B:BitDescription W) (number:Local B) (places:RangeRoom (ordinary v (v.stageStart root)) r B)
  {p R:ℕ} (shape:WorldShape p R B)
local notation "args" y:arg => occurrences (shape.sites (y:NodeOrder.All B).1) y.2
local notation "pg" f:arg j:arg => page (DescentRetainedRangeDigits.page f) (j:Fin v.resolver.operands)
local notation "reg" => rangeRegister ports r B number places.capacity places.hosts places.groups places.radix places.positive target

include issued blocks groups saved away in
theorem ordinary_archive_spans («meta»:v.MetaWords) (old:Books v.resolver)
    (jobs:Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
    (newRead:∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) v.resolver.lanes work)
    (spanRead:∀x p,Reads (previousBank v.resolver (v.vectorOutput floor) x p) (old x p) v.resolver.lanes work)
    (keyRead:∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((jobs j).compiled h g)) v.resolver.lanes work)
    (bitsFit:v.finalChart.field*v.resolver.nodes*v.resolver.lanes≤w)
    (values:∀(y:NodeOrder.All B)(j:Fin (ports).argumentsPerNode)(f:Fin 3),
      (j.val<(args y).length ∨ f=2) → (reg).word y j.val f=atSlot (shape.sites y.1) y.2 j.val f) :
    ∀(x:Fin (2^(ports).venue.k))(j:Fin (ports).argumentsPerNode)(f:Fin 3),
      ∃cells:Fin (ports).operandHosts→Fin (ports).venue.groups→Cell ((ports).operandBits*(ports).nodes),
        Reads (previousBank (ports).rangeLayout (ports).archive.arguments x (page (DescentRetainedRangeDigits.page f) j))
          cells (ports).operandLanes target ∧
        ∀h g n y,slotAt ports r B number places x n h g=some y → (j.val<(args y).length ∨ f=2) →
          ((encode (ports).operandBits (ports).nodes).symm (cells h g) n).val=atSlot (shape.sites y.1) y.2 j.val f:=by
  intro x j f
  let eql:(ports).rangeLayout=v.resolver:=layoutEq
  let x':=x.cast (congrArg Layout.blocks eql)
  let j':=j.cast (congrArg Layout.operands eql)
  let page₀:=pg f j'
  let buf:=previousBank v.resolver base x' page₀
  let vals:=fun h g=>v.finalChart.law page₀
    (v.finalChart.dataAt (v.numericInputs «meta» old jobs) page₀ x' h g)
  have actual:Reads buf vals v.resolver.lanes written:=
    v.argumentsAfter_issued floor bank.operands _ work «meta» old jobs newRead spanRead keyRead x' page₀
  have finish:Reads buf vals v.resolver.lanes target:=by
    apply DateCode.history_event dates initial i
    refine ⟨v.dateOutput root shelf header input count wires sources steps bank d positive fit snap,?_,?_⟩
    · rw [issued]
      exact (v.date_any root shelf header input count wires sources steps bank d positive fit snap).1
    · exact v.date_argument_rows root shelf header input count wires sources steps bank d positive fit snap x'
        page₀ vals saved away actual
  obtain ⟨cells,read,_⟩:=reindex_span (b:=(ports).operandBits) eql x j f vals finish
  exact ⟨cells,read,spans_of_range ports r B number places shape target x j f bitsFit cells read
    (fun y=>values y j f)⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
