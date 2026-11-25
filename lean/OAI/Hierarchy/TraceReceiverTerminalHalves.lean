import OAI.Hierarchy.TraceReceiverInstalledScalars

namespace OAI
/-! # The selected terminal half rows inside the independently registered receiver journal -/

namespace Hierarchy.TraceReceiverTerminalHalves
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction NavigationDirectory
open NativeNavigation NodePublication RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.HistoryStageBody.Physical RAM.HistoryInitialSeed
open HistoryStageSetup HistoryPartyBatchExec TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open GridRegisteredSetting HistorySelectedReceiverLoop TraceReceiverLeafSetup
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
private theorem along {F Pins : Type} [Field F] {W K lo hi heap fee levels peak : ℕ}
    {cur ctr : Word W} {m saved : Memory W} {allow : StaticMotif F→Prop} {b : Banks}
    (unit : 0<b.unitWork) (peakFit : peak<2^W) (heads : lo≤hi)
    {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (seed : State.HalfRows O (fun i=>lo≤ i ∧ i<heap) (numeric m))
    (words : r.WordVisits (RecordedWordStep K cur ctr hi heap m Pins allow) h J L C O p)
    (prices : r.WordVisits (Run.resourceVisit F Pins fee levels peak b (numeric saved)) h J L C O p) :
    State.HalfRows (r.endSites h C O p) (fun i=>lo≤ i ∧ i<heap) (numeric m) := by
  induction r with
  | done=>exact seed
  | step R next ih=>
    let i:=h.1
    obtain ⟨cost⟩:=prices.1
    have small (v) : (R.next i).incidentWidth v<2^W := by
      have floor:=cost.nextFloor v
      change 1+(R.next i).incidentWidth v ≤ R.push i (C.1 i) cost.prev v at floor
      exact (show (R.next i).incidentWidth v≤R.push i (C.1 i) cost.prev v by omega).trans_lt
        ((Nat.le_mul_of_pos_left _ unit).trans_lt ((cost.newCap v).trans_lt peakFit))
    have grown : State.HalfRows p.1.sites (fun k=>lo≤k ∧ k<heap) (numeric m) :=
      (words.1.halfRows small).transfer (fun _ _=>rfl) (fun _ h=>⟨heads.trans h.1,h.2⟩)
    exact ih i (Run.tailHistory R next h) (J.2 i) (J.1 L i).words (C.2 i) p.1.sites p.2 grown words.2 prices.2

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S addr fuel axes : ℕ}
variable (I : RunData F (64*w) pc regs slots S addr fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "u" => TraceAdmission.receiverAge w
local notation "W" => (64*w)
local notation "B" => I.block
local notation "M" => I.machine
local notation "ft" => I.fit
local notation "hF" => I.field
local notation "st" => I.state
local notation "hk" => I.axesFit
local notation "d" => (axes+1)+(w/2)
local notation "G" => TraceStaticRow.gateTable hF (ft).width (ft).labels addr fuel st regs slots d
local notation "O" => (GridReceiverDirectory.archive I l).cursorSeedSites B hk (w/2) (1+(d+d)) (G).cells rfl rfl
local notation "a" => GridReceiverDirectory.archive I l
local notation "dn" => GridReceiverDirectory.native I l
local notation "stop" => finish (a).K (dn).stages (a).cursor
local notation "b" => (dn).node.banks
local notation "phase" => ((B).repeat I.passes).length
local notation "P" => GridReceiverBanks.pinPlan I l
local notation "C" => I.issuedCharges
local notation "r" => I.run
local notation "K" => (B).localCoefficient*(W+1)^3
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
local notation "L" => TraceReceiverSeedWords.wordsLayout M ft hF st B hk
local notation "trees" => TraceReceiverSeedWords.forest M ft hF st B hk
local notation "J" => (TraceReceiverCofinalPrices.assembly I).steps
local notation "T" => (l.sideMinusOne+1)^(l.dimension+1)*l.copies
local notation "full" => (2^(axes+1):ℕ)
local notation "dim" => (l.dimension+1)
local notation "g" => GridPinArena.slab w
local notation "radix" => (20*(w+1)+2)^(dim+2)
local notation "table" => TraceReceiverTablesMount.output I
local notation "fees" => I.issuedUnit w l.degree l.stageRate l.rootRate

variable {geom : GridReceiverDirectory.ElectionRoom I l} {safe : GridNativeDispatch.WordRoom I}
    {z : I.trace} {sel : Fin (l.selectorCap+1)→Bool} {t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)} {input origin elected : Memory (64*w)}
    (j : TraceReceiverElectedJournal.Journal I l geom safe z sel t input origin elected)
local notation "last" => ((r).finalArchive z.1 C O j.path).1
local notation "total" => (last).first+(last).count


local notation "terminal" => (r).endSites z.1 C O j.path
local notation "span" => (fun i=>base u 20≤ i ∧ i<(stop).heap)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3200000 in
/-- Every terminal incident header and all its four-field records occur in the
original journal, with the true edge, prefix and width, also for a zero-stage branch. -/
theorem posted (ok : TraceReceiverInstalledScalars.Ready I l j) :
    State.HalfRows terminal span (numeric j.mid) := by
  have bounds:=TraceReceiverLeafSetup.archive_bounds I l (by have:=ok.big;omega) ok.held
  have heads : base u 20≤(stop).header := by rw [header_finish];exact bounds.1.trans (Nat.le_add_right ..)
  have low : base u 20≤(a).initialRecords := Nat.le_add_right ..
  have high : (a).metadataEnd≤(stop).heap := by
    rw [heap_finish];exact ok.metadata.trans (Nat.le_add_right ..)
  have seed : State.HalfRows O span (numeric j.mid) :=
    ok.rev.transfer (fun i h=>congrArg Fin.val (j.initialWords i h.1 h.2))
      (fun i h=>⟨low.trans h.1,h.2.trans_le high⟩)
  have scales:=TraceAdmission.receiverAge_chart w ok.big
  have peakVol : peak≤volume u := Nat.pow_le_pow_right (by decide) (by omega)
  have positive : 0 < w := (by decide : 0 < 64^10).trans_le ok.big
  have widthRoom : 5*w < 64*w := by omega
  have peakFit : peak<2^W := peakVol.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (scales.2.trans_lt widthRoom))
  have workBound (i) : I.work z.1 C (b).unitWork i≤peak :=
    (ok.paid i).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have cost:=TraceReceiverCofinalPrices.native I u phase peak b (numeric j.saved) z.1 O j.path rfl
    ok.unit le_rfl peakVol ok.shrink ok.refresh j.charged j.stored workBound
  exact along ok.unit peakFit heads r z.1 J L C O j.path seed (j.visits (Fin S→Bool) L) cost.1

theorem posted_registered (ok : TraceReceiverInstalledScalars.Ready I l j) :
    State.HalfRows terminal span (numeric j.reg) :=
  (posted I l j ok).transfer (fun i h=>congrArg Fin.val (j.cache.stage_cells i h.2)) (fun _ h=>h)

theorem posted_out (ok : TraceReceiverInstalledScalars.Ready I l j) :
    State.HalfRows terminal span (numeric j.out) :=
  (posted_registered I l j ok).transfer (fun i h=>
    congrArg Fin.val (j.archived i (h.2.trans_le ok.held)).symm) (fun _ h=>h)

end
end Hierarchy.TraceReceiverTerminalHalves

end OAI
