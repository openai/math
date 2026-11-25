import OAI.Hierarchy.DescentDatedOriginalHeaderRoom
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # The original, previous, and newborn headers on one physical operand-preparation execution -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
variable (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "rc₀" => v.resolver
local notation "vx₀" => v.vector
local notation "bn₀" => v.bornBook
local notation "g₀" => v.ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "mouth₀" => v.mouthChart mat.newBlocks
local notation "vecAt" => v.vectorStart floor
local notation "routeAt" => v.routedStart floor
local notation "portAt" => v.originPortEnd floor
local notation "mouthEnd₀" => v.originMouthEnd floor
local notation "headerStart" => v.operandOldHeaderStart floor
local notation "headerEnd" => v.operandHeaderEnd floor

local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "ps₀" => v.operandPathStart floor
theorem original_headers {w a nb mb nb' mb' sourceBits countBits} (refs : v.SourceReferences) (orig : v.SourceMasks)
    (original : v.OriginalDonors a nb mb) (donors : Fin (bn₀).args→Fin (vx₀).lows→(mouth₀).Val nb' mb')
    (chip : Fin (bn₀).hosts→Fin (bn₀).groups→Cell (bn₀).chipBits)
    (oldBooks : References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      ((rc₀).size+2) sourceBits countBits)
    (m : Memory w) (good : refs.Room w vecAt)
    (obs : ∀l,Measured (orig l) (original l) (rc₀).nodes W₀ vecAt m)
    (witness : ∀a l,Measured (v.mouthRef A mat a l) (donors a l) (rc₀).nodes W₀ vecAt m)
    (input : (A.chipBank v floor).Fits w vecAt) (span : (bn₀).rows≤(A.chipBank v floor).size)
    (read : Reads (A.chipBank v floor) chip (bn₀).lanes m)
    (home : (bn₀).hosts=(vx₀).hosts) (lane : (bn₀).lanes=W₀)
    (group : (bn₀).groups=(vx₀).groups*(vx₀).radix)
    (wide : v.vector.bookBits=((rc₀).size+2)*(rc₀).nodes)
    (pages : ∀p q,Measured (refs p q) (oldBooks p q) (rc₀).nodes W₀ vecAt m)
    (panelLow : A.venue.panel.base+A.venue.panel.size≤ mouthEnd₀)
    (panelSize : (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size)
    (panelWord : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2)
    (earlier : PriorHeader.endAddress (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree (v.donorEnd floor)≤ps₀)
    (space : headerEnd<2^w) :
    let first:=(refs.phase w vecAt).image m
    let here:=(v.originAndMouth floor w A mat v.operandShortBits orig).image first
    let last:=(v.operandEarlyPhase floor w A).image here
    (∀j f,Held g₀ headerEnd last (v.originAt floor v.operandShortBits shape j f) (v.originHeaderValue shape original j f)) ∧
    (∀j f,Held g₀ headerEnd last (v.oldHeaderAt floor j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) (v.previousHeaderValue shape oldBooks j f h k))) ∧
    ∀j f,Held g₀ headerEnd last (v.mouthAt floor A mat shape j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) (v.mouthHeaderValue floor A mat shape donors chip home group j f h k)) :=by
  let before:=(v.originAndMouth floor w A mat v.operandShortBits orig).image ((refs.phase w vecAt).image m)
  have grow : headerStart≤headerEnd:=(Nat.le_add_right _ _).trans (Nat.le_add_right ..)
  have stage_:=v.original_header_step floor A before panelLow panelSize panelWord earlier (grow.trans_lt space)
  have between : routeAt≤portAt:=by rw [v.originPort_span];exact Nat.le_add_right ..
  have atPort:= (v.vector_before floor).trans between
  have earliest (a l) : ((v.mouthRef A mat a l).expr (bn₀).hosts).inputEnd≤portAt:=by
    let c:=v.mouthRef A mat a l
    have data_:=witness a l
    have fitted : (c.expr (bn₀).hosts).Fits w vecAt:=by
      change (c.tables.emitted.read (masked c.tables c.want c.addr c.counts) (DescentPacking.PackedMatch.Local.Gather.assembly c.gates (c.read (bn₀).hosts))).Fits w vecAt
      simp [Tables.read,Expr.Fits,c,data_.emitFits.apply,data_.emitFits.shift,data_.emitFits.left]
      exact data_.emitFits.right
    exact (PrefixAgreement.inputEnd_of_fits _ fitted).trans atPort
  exact v.gathered_header_triplet floor A mat shape refs orig original donors chip oldBooks m good obs witness
    input span read home lane group earliest wide pages stage_ space

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
