import OAI.Hierarchy.DescentDatedOrdinaryDimensions
import OAI.Hierarchy.DescentPackedCensusReady
import OAI.Hierarchy.DescentPackedPhaseFootprint
import OAI.Hierarchy.DescentPackedMatchPrepareArrangement
import OAI.Hierarchy.DescentPackedMatchROMGeometry

namespace OAI
/-! # Consecutive addresses of the actual ordinary chooser, preparation, and matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section

namespace Ordinary
variable (a : Ordinary)
def rows := a.H*chunks a.G a.lanesAt
def bits := Prepare.bits a.H a.G a.lanesAt
def page := 2^a.bits
def sourceAt (floor : ℕ) :=
  DescentPackedColumnSum.finish (Census.beginSum floor a.H a.G a.lanesAt)
    (Census.columns (2^a.k) a.cap) a.unit a.lanesAt
def censusAt (floor : ℕ) := a.sourceAt floor+a.page
def weightsAt (floor : ℕ) :=
  Phase.CensusTables.finish (a.censusAt floor) ((1+a.b+2*(2*a.cap))*2^a.k) a.lanesAt a.H a.G
def markedAt (floor : ℕ) := a.weightsAt floor+a.page
def phaseAt (floor : ℕ) := a.markedAt floor+a.page
def chooser (old : Bank) (floor : ℕ) : Chooser.Layout :=
  ⟨⟨a.phaseAt floor,Frame.pageBits a.H a.G a.k a.b a.lanesAt,old,⟨a.weightsAt floor,a.bits⟩⟩,
    ⟨a.sourceAt floor,a.bits⟩,⟨a.markedAt floor,a.bits⟩,a.censusAt floor⟩
def phaseWidth := 2*Phase.unit a.k a.b*a.lanesAt
def winnerEnd (old : Bank) (floor : ℕ) :=
  (a.chooser old floor).last a.D a.k a.b a.H a.G a.lanesAt
def prepareAt (old : Bank) (floor : ℕ) := a.winnerEnd old floor+a.page
def sorterAt (old : Bank) (floor : ℕ) :=
  Prepare.ROM.sortBase (a.prepareAt old floor) a.k a.D a.cap (a.k+3) a.lanesAt a.H a.G
def matcherAt (old : Bank) (floor : ℕ) :=
  Prepare.next a.k a.H a.G a.lanesAt a.D a.cap (a.sorterAt old floor)
def panelBits := max (a.k+3) (Nat.clog 2 (a.D+1))
def matcher (old : Bank) (floor : ℕ) :=
  Gather.ROM.place (shape (2^a.k) a.D (2*a.cap) a.profile) a.panelBits
    (2^a.k) a.D (2*a.cap) (2^(a.k+1)) a.H a.G a.lanesAt a.unit (a.matcherAt old floor) a.seats

theorem rows_fit : a.rows≤a.page := by
  exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1<2) (a.rows+1))

theorem phase_lanes : lanes a.phaseWidth (Phase.unit a.k a.b)=a.lanesAt :=
  Nat.mul_div_cancel_left _ (by dsimp [Phase.unit];omega)

theorem origin_order (floor : ℕ) :
    floor≤a.sourceAt floor ∧ a.sourceAt floor+a.rows≤a.censusAt floor ∧
    a.censusAt floor≤a.weightsAt floor ∧ a.weightsAt floor+a.rows≤a.markedAt floor ∧
    a.markedAt floor+a.rows≤a.phaseAt floor := by
  have h:=a.rows_fit
  refine ⟨?_,Nat.add_le_add_left h _,?_,Nat.add_le_add_left h _,Nat.add_le_add_left h _⟩
  · simp only [sourceAt,DescentPackedColumnSum.finish,Census.beginSum,Nat.add_assoc]
    exact Nat.le_add_right ..
  · simp only [weightsAt,Phase.CensusTables.finish,Phase.CensusTables.maskBase,Nat.add_assoc]
    exact Nat.le_add_right ..

/-- The real winner and all the ordinary trial panels, including guard words and
all trailing per-color words. -/
theorem winner_words (old : Bank) (floor : ℕ) :
    let C:=a.chooser old floor
    a.winnerEnd old floor-a.phaseAt floor=
      (Phase.Arena.first C.chart a.D a.k a.b a.phaseWidth-C.chart.origin)+
      ((2^a.k-1)*(a.k+1)+7)*C.chart.page+
        ((2^a.k-1)+1+(2^(a.k+1)+1))+2^a.k*a.rows := by
  intro C
  have count:=Phase.Arena.total_words C.chart a.D a.k a.b a.phaseWidth a.H a.G
  rw [a.phase_lanes] at count
  exact count

theorem phase_before_winners (old : Bank) (floor : ℕ) :
    a.phaseAt floor≤a.winnerEnd old floor := by
  let C:=a.chooser old floor
  have first : C.chart.origin≤Phase.Arena.first C.chart a.D a.k a.b a.phaseWidth :=
    (show C.chart.origin≤Phase.Arena.menu C.chart a.D a.k from Nat.le_add_right ..).trans
      ((show Phase.Arena.menu C.chart a.D a.k≤Phase.Arena.names C.chart a.D a.k a.phaseWidth from Nat.le_add_right ..).trans
        (Nat.le_add_right ..))
  change C.chart.origin≤Phase.Arena.endAt C.chart a.D a.k a.b a.phaseWidth+2^a.k*a.rows
  simp only [Phase.Arena.endAt,Phase.Arena.colorWork,Phase.Arena.selected,Phase.Arena.seedWork,Nat.add_assoc]
  exact first.trans (Nat.le_add_right ..)

theorem matcher_extent (old : Bank) (floor : ℕ) :
    (a.matcher old floor).endAddr≤a.matcherAt old floor+
      ((1+«fields» (2^a.k) a.D (2*a.cap))+(2^(a.k+1)+6))*2^(a.payload/2)+
      16*(a.rows+(2^(a.k+1)*a.H)*chunks a.G a.lanesAt+
        a.seats/(a.lanesAt*(shape (2^a.k) a.D (2*a.cap) a.profile).pairs)+1) :=
  Gather.ROM.chosen_extent _ _ _ _ _ _ _ _ _ _ _ _

theorem winner_bound (old : Bank) (floor : ℕ) :
    let C:=a.chooser old floor
    a.winnerEnd old floor≤a.phaseAt floor+
      (((2^a.k-1)*(a.D+3+4*a.k))*C.chart.page+
       (Phase.Menu.pages a.k+2^a.k*((2^a.k-1)*2^(a.k+1)))*2^(a.phaseWidth/2))+
      (((2^a.k-1)*(a.k+1)+7)*C.chart.page)+
        ((2^a.k-1)+1+(2^(a.k+1)+1))+2^a.k*a.rows := by
  intro C
  have h:=Phase.Arena.header_words C.chart a.H a.G a.k a.b a.D a.phaseWidth
  have eqn:=a.winner_words old floor
  have lo:=a.phase_before_winners old floor
  change Phase.Arena.first C.chart a.D a.k a.b a.phaseWidth-C.chart.origin≤_ at h
  change a.winnerEnd old floor-a.phaseAt floor=_ at eqn
  dsimp only [C] at h ⊢
  omega

/-- Relocation translates every matcher word by the same amount. Data-dependent
census/roster values occur only in the execution, never in these addresses. -/
theorem winner_add (old : Bank) (base bump : ℕ) :
    a.winnerEnd old (bump+base)=bump+a.winnerEnd old base := by
  simp only [winnerEnd,Chooser.Layout.last,Chooser.Layout.shelves,Phase.Arena.shelves,
    Phase.Arena.endAt,Phase.Arena.colorWork,Phase.Arena.selected,Phase.Arena.seedWork,
    Phase.Arena.first,Phase.Arena.names,Phase.Arena.menu,Frame.Chart.sheetEnd,Frame.Chart.sheetSpan,
    Frame.Chart.page,chooser,phaseAt,markedAt,weightsAt,Phase.CensusTables.finish,
    Phase.CensusTables.maskBase,censusAt,sourceAt,DescentPackedColumnSum.finish,Census.beginSum,Nat.add_assoc]

theorem matcherAt_add (old : Bank) (base bump : ℕ) :
    a.matcherAt old (bump+base)=bump+a.matcherAt old base := by
  simp only [matcherAt,sorterAt,prepareAt,winner_add,Prepare.ROM.sortBase,Prepare.next,
    Prepare.stop,Prepare.fieldBase,Prepare.rosterBank,ProtocolRAM.Bank.size,Nat.add_assoc,Nat.add_max_add_left]

theorem matcher_add (old : Bank) (base bump : ℕ) :
    (a.matcher old (bump+base)).endAddr=bump+(a.matcher old base).endAddr := by
  simp only [matcher,Gather.ROM.place,Gather.ROM.column,Gather.ROM.stop,matcherAt_add,
    ProtocolRAM.Bank.size,Nat.add_assoc]

end Ordinary
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
