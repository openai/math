import OAI.Hierarchy.ProbeFixedPreparedTests
import OAI.Hierarchy.TaggedWideNativeArena
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Numeric capacity of the two physical dated tests on the wide input -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart Filter
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ)

/-- A single constant covers the active arena, both accumulator scans, and
the immediately encoded local discrepancy comparison. -/
def wideTestHeight :=
  max (max v.voteHeight v.discrepancyScanHeight)
    (max (Classical.choose v.wideArena+1) ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊)

theorem wide_testWordRoom (h width : ℕ) (late : v.wideTestHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) : v.TestWordRoom (v.widePlacement h width) h width := by
  let P:=v.widePlacement h width
  let G:=v.privateArena P h width
  let factor:=Classical.choose v.wideArena
  have reach : G.endAddress v.mesh≤factor*2^h := (Classical.choose_spec v.wideArena) h width budget
  have room : factor+1≤h := (le_max_left ..).trans ((le_max_right ..).trans late)
  have range := append_room (h:=h) (d:=2^v.W) (copies:=copies) (K:=factor)
    (room.trans (Nat.lt_two_pow_self (n:=h)).le)
  have hword : h<2^wordBits h (2^v.W) copies :=
    (Nat.lt_two_pow_self (n:=h)).trans_le (Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega))
  refine ⟨reach.trans_lt ((Nat.le_add_left ..).trans_lt range),rfl,?_,?_,?_,budget,le_rfl⟩
  · exact (le_max_left ..).trans ((le_max_left ..).trans late)
  · exact (le_max_right ..).trans ((le_max_left ..).trans late)
  · exact ((le_max_right ..).trans ((le_max_right ..).trans late)).trans_lt hword

/-- The full format predicate of the concrete dated scans holds cofinitely on the
wide family. No geometric or economic output of a current event is needed. -/
theorem cofinal_testWordRoom {κ A : ℝ} :
    ∀ᶠ x : Tagged.WideParent κ A in Tagged.WideParent.large κ A,
      v.TestWordRoom (v.widePlacement x.h x.w) x.h x.w := by
  have high : Tendsto (Tagged.WideParent.h (κ:=κ) (A:=A)) (Tagged.WideParent.large κ A) atTop := tendsto_comap
  filter_upwards [high.eventually (eventually_ge_atTop v.wideTestHeight),
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit] with x late span
  exact v.wide_testWordRoom x.h x.w late span

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
