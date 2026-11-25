import OAI.Hierarchy.DescentDatedOrdinaryRangeExit
import OAI.Hierarchy.DescentReachedArgumentHeaderRoom
import OAI.Hierarchy.DescentRegisterArchiveValues

namespace OAI
/-! # Four immutable pointer headers at the returned ordinary register -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentPackedColony DescentSIMDLookup DescentDatedPriorOperand DescentOperandStateBanks
open DescentKernelHistory DescentDatedAddressBook DescentLocalArchiveOrder DescentBundleHistory
open DescentRetainedRangeDigits DescentColonies DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false

/-- A field is consumed on its original block, register host and flattened
argument index. All intermediate casts preserve both the physical row and its
lane, including in the final partial word. -/
private theorem reindex_header {l L:Layout} (e:l=L) {b w:ℕ} {out:ℕ} {m:Memory w}
    (x:Fin l.blocks) (j:Fin l.operands) (f:Fin 4)
    (values:Fin L.hosts→Fin L.groups→Cell (b*L.nodes))
    (read:Reads (previousBank L out (x.cast (congrArg Layout.blocks e))
      (page (f.castLE (by decide:4≤7)) (j.cast (congrArg Layout.operands e)))) values L.lanes m) :
    ∃cells:Fin l.hosts→Fin l.groups→Cell (b*l.nodes),
      Reads (previousBank l out x (page (f.castLE (by decide:4≤7)) j)) cells l.lanes m ∧
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
variable (dates:ℕ→DateCode w) (initial:Memory w) (i:ℕ) (issued:dates i=code)
local notation "snap" => DateCode.history dates initial i
local notation "work" => v.beforeArgumentWrite root shelf header input count wires sources steps d positive fit snap
local notation "written" => (op).image work
local notation "target" => DateCode.history dates initial (i+1)
local notation "ports" => ordinary v floor
local notation "base" => v.finalChart.out (v.metaEnd floor)
variable (blocks:2^v.venue.k=v.resolver.blocks) (groups:v.venue.groups=v.resolver.groups)
  (saved:(meter).endAddr≤base) (away:header<(meter).endAddr)
local notation "layoutEq" => ordinary_range_layout v floor blocks groups
variable {k age z D wire hist dim:ℕ} {bits:P→ℕ} {W:MarkedWorld F dim P bits}
  {G:PoweredGadget F} {q ε:ℝ} {S:AtomSchedule} (r:Reached W G q ε S k age z D wire hist)
  (B:BitDescription W) (number:Local B) (places:RangeRoom ports r B)
  {p R:ℕ} (shape:WorldShape p R B) (pointer:NodeOrder.All B→ℕ→Pointer)
local notation "coords" y:arg => Reached.NodeCells.coordinate r (y:NodeOrder.All B).1
local notation "blockAt" y:arg => ((coords y).2.2.cast (congrArg (2^·) places.radix)).cast
  (congrArg Layout.blocks (show (ports).rangeLayout=v.resolver from layoutEq))
local notation "groupAt" y:arg => ((coords y).2.1.cast places.groups).cast
  (congrArg Layout.groups (show (ports).rangeLayout=v.resolver from layoutEq))
local notation "hostAt" y:arg => (⟨(coords y).1.val,places.hosts (y:NodeOrder.All B).1⟩:Fin (ports).operandHosts).cast
  (congrArg Layout.hosts (show (ports).rangeLayout=v.resolver from layoutEq))
local notation "nodeAt" y:arg => ((number (y:NodeOrder.All B).1 y.2).castLE (places.capacity y.1)).cast
  (congrArg Layout.nodes (show (ports).rangeLayout=v.resolver from layoutEq))
local notation "args" y:arg => occurrences (shape.sites (y:NodeOrder.All B).1) y.2
local notation "pg" f:arg j:arg => page ((f:Fin 4).castLE (by decide:4≤7)) (j:Fin v.resolver.operands)

include issued saved away in
theorem ordinary_archive_headers («meta»:v.MetaWords) (old:Books v.resolver)
    (jobs:Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
    (newRead:∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) v.resolver.lanes work)
    (spanRead:∀x p,Reads (previousBank v.resolver (v.vectorOutput floor) x p) (old x p) v.resolver.lanes work)
    (keyRead:∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((jobs j).compiled h g)) v.resolver.lanes work)
    (bitsFit:v.finalChart.field*v.resolver.nodes*v.resolver.lanes≤w)
    (active:∀(y:NodeOrder.All B)(j:Fin v.resolver.operands)(f:Fin 4),j.val<(args y).length →
      v.headerDigit (hostAt y) (groupAt y) written (previousBank v.resolver base (blockAt y) (pg f j)) (nodeAt y)=
        (pointer y j.val).header f) :
    ∀(x:Fin (2^(ports).venue.k))(j:Fin (ports).argumentsPerNode)(f:Fin 4),
      ∃cells:Fin (ports).operandHosts→Fin (ports).venue.groups→Cell ((ports).operandBits*(ports).nodes),
        Reads (previousBank (ports).rangeLayout (ports).archive.arguments x (page (f.castLE (by decide:4≤7)) j))
          cells (ports).operandLanes target ∧
        ∀h g n y,slotAt ports r B number places x n h g=some y → j.val<(args y).length →
          ((encode (ports).operandBits (ports).nodes).symm (cells h g) n).val=(pointer y j.val).header f:=by
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
  obtain ⟨cells,read,digits⟩:=reindex_header (b:=(ports).operandBits) eql x j f vals finish
  refine ⟨cells,read,?_⟩
  rintro h g n ⟨u,node⟩ hit live
  obtain ⟨rfl,rfl,rfl,rfl⟩:=slotAt_coordinates ports r B number places _ _ _ _ u node hit
  let y:NodeOrder.All B:=⟨u,node⟩
  have recv:=PackedSource.read vals written buf.base places.positive bitsFit actual (hostAt y) (groupAt y)
  have nd:=congrArg (digit v.finalChart.field (nodeAt y).val) recv
  have low:=digit_encode ((encode v.finalChart.field v.resolver.nodes).symm (vals (hostAt y) (groupAt y))) (nodeAt y)
  have encoded := (encode v.finalChart.field v.resolver.nodes).apply_symm_apply (vals (hostAt y) (groupAt y))
  have decoded := congrArg (fun data : Cell (v.finalChart.field*v.resolver.nodes) =>
    digit v.finalChart.field (nodeAt y).val data.val) encoded
  exact (digits _ _ _).trans (low.symm.trans (decoded.trans (nd.symm.trans (active y j' f live))))

open DescentPackedOperand DescentOrdinaryFinal DescentLocalPrivateNames Computability.BorderVNP.Crossing
variable (hp:0<p) (pin:P→ℕ)
local notation "rec₁" u:arg => (shape.sites u).recipe hp
local notation "sx" u:arg => ((Reached.NodeCells.coordinate r u).2.2.cast (congrArg (2^·) places.radix)).cast
  (congrArg Layout.blocks (show (ports).rangeLayout=v.resolver from layoutEq))
local notation "sh" u:arg => (⟨(Reached.NodeCells.coordinate r u).1.val,places.hosts u⟩:Fin (ports).operandHosts).cast
  (congrArg Layout.hosts (show (ports).rangeLayout=v.resolver from layoutEq))
local notation "sg" u:arg => ((Reached.NodeCells.coordinate r u).2.1.cast places.groups).cast
  (congrArg Layout.groups (show (ports).rangeLayout=v.resolver from layoutEq))
local notation "onsite" u:arg => (number u).toEmbedding.trans (Fin.castLEEmb (places.capacity u))
variable («meta»:v.MetaWords) (old:Books v.resolver) (jobs:Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
  (argFit:∀u n,(rec₁ u).arity n≤v.resolver.operands)
local notation "mouth" u:arg => v.finalChart.mouths (rec₁ u) (onsite u) (argFit u)
local notation "fragment" u:arg n:arg j:arg => v.issuedFragment jobs (sx u) (sh u) (sg u) ((mouth u) ⟨n,j⟩)
local notation "expected" => Reached.argumentPointer r B number shape hp pin v.resolver.operands

include issued saved away in
/-- Each genuine public, private and pin operand is read through the writer's
own physical result. A nonempty arity past the paid prefix is included. -/
theorem ordinary_argument_headers
    (newRead:∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) v.resolver.lanes work)
    (spanRead:∀x p,Reads (previousBank v.resolver (v.vectorOutput floor) x p) (old x p) v.resolver.lanes work)
    (keyRead:∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>word ((jobs j).compiled h g)) v.resolver.lanes work)
    (bitsFit:v.finalChart.field*v.resolver.nodes*v.resolver.lanes≤w)
    (arityRead:∀u n,digit v.finalChart.arityBits ((onsite u) n).val («meta» 1 (sx u) (sh u) (sg u)).val=(rec₁ u).arity n)
    (empty:∀u t,(∀n,(onsite u) n≠t) →
      digit v.finalChart.arityBits t.val («meta» 1 (sx u) (sh u) (sg u)).val=0)
    (names:∀u,∃hidden:(rec₁ u).UsedWord↪Key,v.SourceKeys jobs (sx u) (sh u) (sg u) (rec₁ u) (onsite u) (argFit u) hidden)
    (cable:∀u n (j:Fin ((rec₁ u).arity n)) (e:DescentKernelHistory.Incident W.graph u) z
      (enough:(z+1)*p≤W.graph.width e.val), (rec₁ u).operand n j=.inl ⟨.inl e,z,enough⟩ →
      Pointer.ofKey 0 (resolve (fragment u n j))=Reached.firstCable r hp u e z enough)
    (exterior:∀u n (j:Fin ((rec₁ u).arity n)) (e:DescentKernelHistory.Attached W.graph u) z
      (enough:(z+1)*p≤bits e.val), (rec₁ u).operand n j=.inl ⟨.inr e,z,enough⟩ →
      resolve (fragment u n j)=Key.pin (pin e.val) z)
    (capacity:r.placement.cap≤2^v.finalChart.field) (rectangle:v.finalChart.keys≤2^v.finalChart.field) :
    ∀(x:Fin (2^(ports).venue.k))(j:Fin (ports).argumentsPerNode)(f:Fin 4),
      ∃cells:Fin (ports).operandHosts→Fin (ports).venue.groups→Cell ((ports).operandBits*(ports).nodes),
        Reads (previousBank (ports).rangeLayout (ports).archive.arguments x (page (f.castLE (by decide:4≤7)) j))
          cells (ports).operandLanes target ∧
        ∀h g n y,slotAt ports r B number places x n h g=some y → j.val<(args y).length →
          ((encode (ports).operandBits (ports).nodes).symm (cells h g) n).val=(expected y j.val).header f:=by
  apply ordinary_archive_headers v root shelf header input count wires sources steps bank d positive fit dates initial i
    issued blocks groups saved away r B number places shape expected «meta» old jobs newRead spanRead keyRead bitsFit
  rintro ⟨u,n⟩ j f live
  let arg:Fin ((rec₁ u).arity n):=⟨j.val,live.trans_eq (DescentRetainedRangeDigits.length (shape.sites u) n hp)⟩
  obtain ⟨hidden,keys⟩:=names u
  exact Reached.issued_argument_header r B number shape hp pin v u (places.capacity u) (argFit u) hidden «meta» old jobs
    (sx u) (sh u) (sg u) floor bank.operands _ work newRead spanRead keyRead places.positive bitsFit
    (arityRead u) (empty u) keys n arg (cable u n arg) (exterior u n arg) f (Reached.argument_header_room r B number shape hp pin v u
      (places.capacity u) (argFit u) jobs (sx u) (sh u) (sg u) capacity rectangle n arg
      (cable u n arg) (exterior u n arg) f)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
