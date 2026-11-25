import OAI.Hierarchy.ProbeFixedWideSpillBallotIssued
import OAI.Hierarchy.ProbeSparseBallotPrior
import OAI.Hierarchy.ProbeSparsePrintedRows
import OAI.Hierarchy.ProbeFixedWideSparseBallot
import OAI.Hierarchy.ProbeFixedWideForestAperture
import OAI.Hierarchy.TaggedWidePageSweep

namespace OAI
/-! # Issuing the first physical ballot on every genuine attempted calendar date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage Native CoreBoard CoreRoute StripChart
open CatalystArchive PurchaseStage StockBound ReportSockets Tagged WideCPU
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- All sites of a feed bypass the ballot. For an attempt, retain the exact
incoming auxiliary facts alongside the numerical candidate-party fields. -/
def eventBallotFact {W : ℕ} (shape : Event→WideCPU.Shape) (sites rom start : ℕ) (fields : ∀e,Fields (shape e))
    (live : ∀a,Finset (Fin (shape (.attempt a)).candidates)) (prior : Memory W→Prop) :
    (e : Event)→PageResult W ((shape e).sheet sites rom start (fields e))
  | .feed _=>PageResult.skip _
  | .attempt a=>printedWithPrior _ sites rom start (fields (.attempt a)) (live a) rfl prior

def wideSpillBallotFact (h width ell fee bits₀ rankFirst rom oldWork : ℕ) (j : Fin (events v.mesh).length)
    (live : ∀a,Finset (Fin (v.widePacketShape h width (.attempt a)).candidates))
    (prior : Memory (wordBits h (2^v.W) copies)→Prop) :
    let z:=v.wideSpillDates h width ell fee bits₀ rankFirst
    PageResult (wordBits h (2^v.W) copies) (z.ballot rom oldWork (v.wideSpillRankEnd h width bits₀ rankFirst) j) :=
  let g:=v.wideDated h width ell fee
  let z:=v.wideSpillDates h width ell fee bits₀ rankFirst
  let start:=v.wideSpillRankEnd h width bits₀ rankFirst
  let bits:=ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h)
  eventBallotFact (v.widePacketShape h width) g.sites (g.ballotROM rom j) (g.ballotStart (z.roleRoot start 2) j)
    (fun e=>v.widePacketFields h width bits e (g.siteROM rom) (g.siteStride rom) (g.roleStart oldWork j.castSucc)
      (z.dateRole start j 0)) live prior ((events v.mesh).get j)

theorem wide_spill_ballot_steps :
    ∀ᶠ h : ℕ in Filter.atTop, ∀width, width≤2^h→v.keepLimit*width+1≤2^h→
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let top:=A.endAddress v.mesh
      let W:=wordBits h (2^v.W) copies
      let stock:=v.fixedTerminalStock P h width
      let _dates:=events v.mesh
      ∀size,top≤ size→∀M (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)), M=v.radius→
      let m:=v.wideSignedMidAt h width size stock M π (wideRouteOrder h (2^v.W) k) raw
      let C:=v.wideSignedChart h width stock
      let co:=checkedOut C top m
      ∀ell fee bits₀ rankFirst rom originalWork,
      let g:=v.wideDated h width ell fee
      let z:=v.wideSpillDates h width ell fee bits₀ rankFirst
      let start:=v.wideSpillRankEnd h width bits₀ rankFirst
      let _root:=z.roleRoot start 2
      let r:=Fintype.card (Slots h (2^v.W) k)
      let page:=v.wideSignedPage h width stock
      let cnt:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A))
      let owners:=sinkBank (v.catalystStaticStart P h width) cnt r P.catalogue.rows
      let banks:=TerminalLayout.settlement page stock
      let src:=TerminalLayout.source page
      let tab:=TerminalLayout.table page
      let dst:=TerminalLayout.destination page
      ∀(transport : Fin g.rawEdges→Bool) (original : Memory W),
        (∀a,a<top → original a=co a)→top≤rom→3*g.romEnd rom+2≤originalWork → originalWork≤ start→z.endAt start<2^W→
        ∀prior : Memory W→Prop,
          let image:=g.words rom (SiteDirectory.table h (2^v.W) k) transport original
          let saved:=fun a=>v.wideBallotRows h width r banks src tab dst owners a (entryMemory C m a)
          let facts:=fun j=>v.wideSpillBallotFact h width ell fee bits₀ rankFirst rom originalWork j saved prior
          PageSteps (z.ballot rom originalWork start) (fun j=>(facts j).holds)
            (fun processing=>(∀i,i<start→processing i=image i) ∧ prior processing) := by
  filter_upwards [v.wide_spill_ballot_scatter] with h observed
  intro width small budget P A top W stock size extent M π raw nativeRadius m C co ell fee bits₀ rankFirst rom originalWork g z
    start r page cnt owners banks src tab dst transport original base late gap oldFirst range prior image saved facts
  let _dates:=events v.mesh
  let _root:=z.roleRoot start 2
  intro j processing source _
  let sh:=v.widePacketShape h width
  let bits:=ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h)
  let f:=fun e=>v.widePacketFields h width bits e (g.siteROM rom) (g.siteStride rom)
    (g.roleStart originalWork j.castSucc) (z.dateRole start j 0)
  let st:=g.ballotStart _root j
  let rr:=g.ballotROM rom j
  let px:=fun e=>(sh e).sheet g.sites rr st (f e)
  let recpt:=eventBallotFact sh g.sites rr st f saved prior
  change ∃out,((px (_dates.get j)).code W).Exec processing out (px (_dates.get j)).ticks ∧
    (recpt (_dates.get j)).holds out ∧ ∀a,a<(px (_dates.get j)).floor → out a=processing a
  cases atDate : _dates.get j with
  | attempt a=>
    have paid:=observed width small budget size extent M π raw nativeRadius ell fee bits₀ rankFirst rom originalWork transport original
      base late gap oldFirst range j a atDate processing source.1
    obtain ⟨out,exec,table,frame⟩:=paid
    have eqp : z.ballot rom originalWork start j=px (.attempt a):=congrArg px atDate
    rw [eqp] at exec frame
    exact ⟨out,exec,printedWithPrior.holds _ _ _ _ _ _ rfl prior source.2 table,frame⟩
  | feed mode=>
    have occupied : (g.ballot j).parties=0 ∧ (g.ballot j).columns=0:=by
      change (sh (_dates.get j)).parties=0 ∧ (sh (_dates.get j)).columns=0
      rw [atDate];exact ⟨rfl,rfl⟩
    have rootEq : _root=start+2*((_dates.length+1)*(3*g.roleSpan)):=rfl
    have endROM : g.controlROMStart rom≤g.romEnd rom:=by dsimp only [Dated.romEnd,Dated.maskROM,endOf];omega
    have guard : 3*g.romEnd rom+2≤_root:=by omega
    have ctrl : g.controlStart _root<2^W:=by
      change WideCPU.endOf (g.maskStart _root) _<2^W at range
      simp only [Dated.maskStart,endOf] at range;omega
    have fixed (i) (_ : rr≤ i) (hi : i<rr+(g.ballot j).advice g.sites) : processing i=image i:=by
      have chartEnd : rr+(g.ballot j).advice g.sites≤g.controlROMStart rom:=WideCPU.extent _ _ j
      exact source.1 _ (by omega)
    have exec : ((px (_dates.get j)).code W).Exec processing processing (px (_dates.get j)).ticks := by
      intro numPorts registers tape machine pc reg pub exit installed data cfg mem entry same
      exact g.empty_ballot_at rom _root j (f (_dates.get j)) _ transport original processing fixed occupied guard ctrl
        machine pc reg pub exit installed data cfg mem entry same
    rw [atDate] at exec
    exact ⟨processing,exec,trivial,fun _ _=>rfl⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
