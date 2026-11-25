import OAI.Hierarchy.DescentTerminalLastProgram
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Trailing addresses for the final cutoff, key histogram, and failure word -/
namespace Hierarchy.DescentTerminalLast
open DescentCensusRAM ProtocolRAM
noncomputable section

/-- The first write follows the paid instruction arena and the rounded read-only key bank. -/
def trailingCut (paidEnd keyRows : ℕ) := paidEnd+DescentDyadicSpan.span keyRows

/-- The cutoff row, two scratch columns, and one interleaved address/value column
precede the counted keys. The following word stores the terminal failure flag. -/
def trailingStop (cut rows slots choices : ℕ) := cut+rows+slots+slots+2*slots+choices

def trailingBanks (w slots choices cut rows : ℕ)
    (word : trailingStop cut rows slots choices<2^w) : Banks w slots choices where
  first := cut+rows
  second := cut+rows+slots
  tape := cut+rows+slots+slots
  bins := cut+rows+slots+slots+2*slots
  scratch := le_rfl
  beforeTape := le_rfl
  beforeBins := le_rfl
  finish := word

theorem trailing_end_bound (paidEnd keyRows rows slots choices : ℕ) :
    trailingStop (trailingCut paidEnd keyRows) rows slots choices+1 ≤
      paidEnd+2*keyRows+rows+4*slots+choices+2 := by
  have span := DescentDyadicSpan.span_le keyRows
  unfold trailingStop trailingCut
  omega

/-- All input banks are read before the first overwritten word. The same high
address bounds every native key, histogram counter, and the final flag. -/
theorem trailing_ready {w slots choices cut rows width : ℕ} (L : Tape)
    (earlier : ∀b∈L.inputs,b.base+b.size≤cut) (capacity : slots≤L.keys.size)
    (widthFit : width<2^w) (choicesPos : 0<choices)
    (last : trailingStop cut rows slots choices+1<2^w) :
    Ready L (trailingBanks w slots choices cut rows (by omega)) cut
      (trailingStop cut rows slots choices) rows width := by
  have cut_le_stop : cut≤trailingStop cut rows slots choices := by unfold trailingStop; omega
  have cutWord : cut<2^w := by omega
  refine ⟨?_,capacity,le_rfl,le_rfl,last,widthFit,choicesPos,?_⟩
  · intro b used
    have bounded := earlier b used
    exact ⟨Nat.two_pow_pos _,by omega,bounded⟩
  · unfold trailingStop at last
    omega

end
end Hierarchy.DescentTerminalLast

end OAI
