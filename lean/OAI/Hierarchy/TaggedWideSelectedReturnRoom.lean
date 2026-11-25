import OAI.Hierarchy.TaggedWideReturnSpillRoom
import OAI.Hierarchy.TaggedWireReportedPath
import OAI.Hierarchy.ProbeFixedWideCorrectedDatesRun
import OAI.Hierarchy.ProbeFixedWideSpillMiddleSheets
import OAI.Hierarchy.ProbeFixedWideSpillEvent
import OAI.Hierarchy.TaggedWideFundedGateRoom
import OAI.Hierarchy.ProbeFixedWideBallotMenu
import OAI.Hierarchy.TaggedWireFundedBallots

namespace OAI
/-! # Simultaneous bounds for the selected return on an installed wide parent -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage CoreBoard ReportSockets Tagged Filter

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A s : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short : ℕ) (u : ℝ → ℝ) (δ ξ : ℝ) (unitCost : ℕ)

def spillReadHeight (unitCost : ℕ) : ℕ :=
  let limit:=max v.menu.maximum (v.keepLimit+1)
  let bound:=max (v.wideHistoryUnit unitCost) (max limit (v.overflowFactor limit))
  let degree:=CoreBoard.HistoryRoles.stride k v.sampler.degree v.wideJobs
  max (max (2*bound) (degree*bound)) (max (2*degree) (2*v.keepLimit+2))

structure SelectedReturnRoom : Prop where
  late : v.reportHeight ≤ x.h
  words : v.ReportWordRoom x.h x.w
  operandAge : v.wideOperandHeight ≤ x.h
  activeAge : v.wideDatedSupportHeight ≤ x.h
  ballotAge : v.wideBallotHeight ≤ x.h
  large : purchaseWordHeight v.W k v.wideJobs ell ≤ x.h
  spill : ∀ _ : v.FullGateRoom x m ell short u δ ξ unitCost,
    v.ReturnSpillRoom x m ell short u δ ξ unitCost
  spillAge : v.wideSpillSheetHeight ≤ x.h
  paidAge : v.wideSpillPaidHeight ≤ x.h
  spillBallotAge : v.wideSpillBallotHeight ≤ x.h
  widthFloor : v.widthFloor ≤ x.w
  partyTags : ∀ a : Attempt,
    let K := v.menuCodes (Stages x.h (2^v.W))
    let bits := Native.wordBits x.h (2^v.W) Native.copies
    1+K ≤ 2^bits ∧ K*v.wideBallotParties x.h a+1 ≤ 2^bits
  tenderAge : v.ballotHeight ≤ x.h
  spillRead : v.spillReadHeight unitCost ≤ x.h

theorem cofinal_selected_return_room {u : ℝ → ℝ} (hu : TaggedWidthProfile.Admissible s u)
    (δ ξ : ℝ) (unitCost : ℕ) :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      v.SelectedReturnRoom x m ell short u δ ξ unitCost := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  have tall : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop := tendsto_comap
  have bound (H : ℕ) : ∀ᶠ y : WideParent κ A in WideParent.large κ A, H ≤ y.h :=
    tall.eventually (eventually_ge_atTop H)
  filter_upwards [v.cofinal_report_sources (κ:=κ) (B:=A),
      v.cofinal_funded_local_ages (κ:=κ) (A:=A),
      v.cofinal_return_spill_room (κ:=κ) (A:=A) m ell short hu δ ξ unitCost,
      bound (purchaseWordHeight v.W k v.wideJobs ell), bound v.wideSpillSheetHeight,
      bound v.wideSpillPaidHeight, bound v.wideSpillBallotHeight, bound v.widthFloor,
      tall.eventually v.wide_ballot_tag_room, bound v.ballotHeight, bound (v.spillReadHeight unitCost)] with
      y report localAges room purchase sheet paid ballot floor tags tender spillRead
  exact ⟨report.1, report.2, localAges.2.1, localAges.2.2.1, localAges.2.2.2, purchase,
    room, sheet, paid, ballot, floor.trans y.property.1.2.1,tags,tender,spillRead⟩


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
