import OAI.Hierarchy.DescentDatedOriginalHeaderWords

namespace OAI
/-! # The original, previous, and newborn headers on one physical operand-preparation execution -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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

def operandBeforeHeaders (floor w : ℕ) (A : v.ArgumentEntry) :=
  ((v.operandDepot floor w A).seq (v.operandPaths floor w)).seq (v.operandRankPhase floor w)

set_option maxHeartbeats 1000000 in
theorem header_triplet_at {w a nb mb nb' mb'} (refs : v.SourceReferences) (orig : v.SourceMasks)
    (original : v.OriginalDonors a nb mb) (donors : Fin (bn₀).args→Fin (vx₀).lows→(mouth₀).Val nb' mb')
    (chip : Fin (bn₀).hosts→Fin (bn₀).groups→Cell (bn₀).chipBits)
    (prior : Fin (rc₀).jobs→Fin 4→DescentDatedOperandReadPipeline.Values g₀ (((rc₀).size+2)*(rc₀).nodes))
    (m : Memory w) (good : refs.Room w vecAt)
    (obs : ∀l,Measured (orig l) (original l) (rc₀).nodes W₀ vecAt m)
    (witness : ∀a l,Measured (v.mouthRef A mat a l) (donors a l) (rc₀).nodes W₀ vecAt m)
    (input : (A.chipBank v floor).Fits w vecAt) (span : (bn₀).rows≤(A.chipBank v floor).size)
    (read : Reads (A.chipBank v floor) chip (bn₀).lanes m)
    (home : (bn₀).hosts=(vx₀).hosts) (lane : (bn₀).lanes=W₀)
    (group : (bn₀).groups=(vx₀).groups*(vx₀).radix)
    (early : ∀a l,((v.mouthRef A mat a l).expr (bn₀).hosts).inputEnd≤portAt)
    (oldW : ∀j f,let B:=v.previousAt floor j f
      B.Fits w routeAt ∧ (rc₀).rows≤B.size ∧ Reads B (prior j f) M₀ ((refs.phase w vecAt).image m))
    (stages : Step mouthEnd₀ headerStart (v.operandBeforeHeaders floor w A)
      ((v.originAndMouth floor w A mat v.operandShortBits orig).image ((refs.phase w vecAt).image m)))
    (space : headerEnd<2^w) :
    let first:=(refs.phase w vecAt).image m
    let here:=(v.originAndMouth floor w A mat v.operandShortBits orig).image first
    let last:=(v.operandEarlyPhase floor w A).image here
    (∀j f,Held g₀ headerEnd last (v.originAt floor v.operandShortBits shape j f) (v.originHeaderValue shape original j f)) ∧
    (∀j f,Held g₀ headerEnd last (v.oldHeaderAt floor j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) (prior j f h k))) ∧
    ∀j f,Held g₀ headerEnd last (v.mouthAt floor A mat shape j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) (v.mouthHeaderValue floor A mat shape donors chip home group j f h k)) :=by
  intro first here last
  let pre:=v.originPrefix floor v.operandShortBits w orig
  let between:=pre.image first
  let mouths:=v.originPrefixMouth floor w A mat
  let plain:=v.operandBeforeHeaders floor w A
  let after_:=plain.image here
  have low:routeAt≤portAt:=by rw [v.originPort_span];exact Nat.le_add_right ..
  have mouthLow:portAt≤ mouthEnd₀:=Nat.le_add_right ..
  have headerLow:headerStart≤headerEnd:=(Nat.le_add_right _ _).trans (Nat.le_add_right ..)
  have atMouth:=stages.order.trans_lt (headerLow.trans_lt space)
  have vecLe:vecAt≤routeAt:=v.vector_before floor
  have originOK:=v.originPrefix_run floor v.operandShortBits w orig first
    (fun l=>ProtocolRAMGeneratedWrite.fits_mono _ vecLe (read_mask (orig l) (original l) (obs l)).1) (mouthLow.trans_lt atMouth)
  have mouthOK:=v.originPrefixMouth_any floor (w:=w) A mat between (bank_before input (vecLe.trans low))
    group good.lanes good.radix early atMouth
  have second : Step portAt mouthEnd₀ mouths between:=⟨mouthLow,mouthOK.1,mouthOK.2⟩
  have haveOld (j f) : let B:=v.previousAt floor j f
      B.Fits w headerStart ∧ (rc₀).rows≤B.size ∧ Reads B (prior j f) M₀ after_ :=by
    intro B
    obtain ⟨fit,sz,seen⟩:=oldW j f
    refine ⟨bank_before fit (low.trans (mouthLow.trans stages.order)),sz,reads_before B (prior j f) first after_ seen ?_ fit sz⟩
    intro i lt_
    exact (stages.frame i (.inl ((lt_.trans_le low).trans_le mouthLow))).trans
      ((second.frame i (.inl (lt_.trans_le low))).trans (originOK.2 i (.inl lt_)))
  let bv:=v.mouthHeaderValue floor A mat shape donors chip home group
  have haveNew (j f) : let B:=v.mouthBankAt floor A mat shape j f
      B.Fits w headerStart ∧ (rc₀).rows≤B.size ∧ Reads B (bv j f) M₀ after_ :=by
    intro B
    obtain ⟨fit,sz,seen⟩:=v.mouth_header_three floor A mat shape refs orig original donors chip m good obs witness
      input span read home lane group atMouth j f
    exact ⟨bank_before fit stages.order,sz,reads_before B (bv j f) here after_ seen
      (fun i hi=>stages.frame i (.inl hi)) fit sz⟩
  have printed:=v.header_pair_issued floor A mat shape after_ prior bv
    (fun j f=>⟨(haveOld j f).1,(haveOld j f).2.1⟩) (fun j f=>⟨(haveNew j f).1,(haveNew j f).2.1⟩)
    (fun j f=>(haveOld j f).2.2) (fun j f=>(haveNew j f).2.2) space
  refine ⟨?_,printed.2⟩
  intro j f
  have atStart:=v.origin_header_six floor shape refs orig original m good obs (mouthLow.trans_lt atMouth) j f
  have beforeMouth := Step.keep g₀ (m:=between) (p:=mouths) second atStart
  have beforeHeader := Step.keep g₀ (m:=here) (p:=plain) stages beforeMouth
  exact Step.keep g₀ (m:=after_) (p:=v.operandHeaderPhase floor w) printed.1 beforeHeader

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
