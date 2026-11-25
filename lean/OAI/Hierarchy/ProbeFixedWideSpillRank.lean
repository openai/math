import OAI.Hierarchy.ProbeFixedWideTerminal
import OAI.Hierarchy.ProtocolRAMDateSpillRankTape
import OAI.Hierarchy.ProtocolRAMDateSpillAmount

namespace OAI
/-! # The original fixed-format calendar's dated native spill program -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram ProtocolRAMDateSpillRank
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits : ℕ)
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "stageCount" => Stages h D
local notation "stock" => v.fixedTerminalStock P h width
local notation "fmt" => v.nativeFormats P h width
local notation "feeds" => FeedLayout.atEvent (N:=stageCount) v.mesh (v.privateArena P h width) fmt (P).joint.initial width v.keepLimit

def wideSpillOverflow : Event→Bank
  | .attempt a=>attemptBank h stageCount k ((fmt a).pricedArea)
  | .feed b=>feedBank (feeds b)

def wideSpillRanks (first : ℕ) : DateSpill.RankTape where
  first := first
  old := Fintype.card (Old h v.W k (P).catalogue.rows)
  edges := (P).catalogue.rows
  core := coreCount (wideRouteOrder h D k)
  accounts := CatalystArchive.TerminalLayout.settlement (v.wideSignedPage h width stock) stock
  overflow j := ((events v.mesh)[j]?).elim ⟨first,0⟩ (v.wideSpillOverflow h width)
  kind := (v.wideTerminalStock h width bits).kind
  index := (v.wideTerminalStock h width bits).index

def wideSpillPage (first j : ℕ) := (v.wideSpillRanks h width bits first).page j

def wideSpillRankProgram (first : ℕ) :=
  (v.wideSpillRanks h width bits first).program (Native.wordBits h D Native.copies) (events v.mesh).length
def wideSpillRankTicks (first : ℕ) := (v.wideSpillRanks h width bits first).ticks (events v.mesh).length
def wideSpillRankEnd (first : ℕ) := (v.wideSpillRanks h width bits first).stop (events v.mesh).length

theorem wide_spill_overflow (first : ℕ) (j : Fin (events v.mesh).length) :
    (v.wideSpillPage h width bits first j.val).overflow=v.wideSpillOverflow h width ((events v.mesh).get j) := by
  change ((events v.mesh)[j.val]?).elim _ _=_
  simp []

theorem wide_spill_rank_cheap (first : ℕ) : CheapCode (v.wideSpillRankProgram h width bits first) :=
  @DateSpill.RankTape.cheap (v.wideSpillRanks h width bits first)
    (Native.wordBits h D Native.copies) (events v.mesh).length


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
