import Mathlib.Tactic.FinCases
import OAI.Hierarchy.DescentTerminalAppendixNumbers

namespace OAI
/-! # The genuine chip proposals and immutable ROM occupy at most the purchased bin capacity -/
namespace Hierarchy.DescentTerminalChipBootWords
open scoped BigOperators

theorem total_mono_bins {K K' : ℕ} (smaller : K≤K') (W q p codes : ℕ) :
    total K W q p codes≤total K' W q p codes :=by
  unfold total
  refine Finset.sum_le_sum fun i _=>Nat.pow_le_pow_right (by decide : 0<2) (Nat.clog_mono_right 2 ?_)
  have bins := Nat.mul_le_mul_right W smaller
  fin_cases i <;> first | exact bins | exact le_rfl

end Hierarchy.DescentTerminalChipBootWords

namespace Hierarchy.DescentTerminalPublicIdentity

theorem total_mono_bins {K K' : ℕ} (smaller : K≤K') (W q p codes raw publicRows : ℕ) :
    total K W q p codes raw publicRows≤total K' W q p codes raw publicRows :=by
  unfold total DescentTerminalPaidBoot.total DescentTerminalBoot.total
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (DescentTerminalChipBootWords.total_mono_bins smaller W q p codes) _) _) _

end Hierarchy.DescentTerminalPublicIdentity


namespace Hierarchy.DescentSixParty.SeedNamed

/-- The dense header immediately follows the chip proposal. Both occupy the original immutable
prefix and are already below the first free word whenever the complete public prefix is. -/
theorem original_rom_end (K W q piece codes edgeRows publicRows front : ℕ) :
    (front+DescentTerminalChipBootWords.total K W q piece codes)+DescentTerminalDenseHeaderBoot.extent q (W*piece)≤
      front+DescentTerminalPublicIdentity.total K W q piece codes edgeRows publicRows :=by
  unfold DescentTerminalPublicIdentity.total DescentTerminalPaidBoot.total DescentTerminalBoot.total
  omega

end Hierarchy.DescentSixParty.SeedNamed

end OAI
