import OAI.Computability.VPVNP.PairNativeCacheProgram
import OAI.Computability.VPVNP.CursorDescriptorWords

/-!
# Clock for the native operand-cache initialization

The arithmetic prelude and all 38 store/increment pairs together use at most
one input length in native ticks at every sufficiently large length. The
threshold is uniform in the live bucket size.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeCache

open Filter LiveProgram NativeOperands

theorem eventually_work_le (c : Constants) (a b B : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ H : ℕ,
      work (args c) a b (AssemblerPublic.geometry B n H) + 76 ≤ n := by
  let K := Finset.univ.sup (fun i => fieldCost 0 (args c i))
  let A := 4*a + (a+b+109) + 38*(K*((B+10)^4+2))
  filter_upwards [BurstRAM.eventually_polylog_le A 4] with n hn
  let L := n.log2+1
  have h1 : 1 ≤ L := Nat.succ_pos _
  have hl : L ≤ L^4 := Nat.le_self_pow (by decide) _
  have hwidth : CursorBounds.wordBits B n + 1 ≤ ((B+10)^4+2)*L^4 := by
    simpa only [Nat.zero_add,Nat.clog_one_right,Nat.add_zero] using
      CompressorRecords.word_plus_clog_le B n 0 (Nat.zero_le n)
  intro H
  apply (work_le c a b (AssemblerPublic.geometry B n H)).trans
  change 4*a*L + (a+b+109) + 38*(K*(CursorBounds.wordBits B n+1)) ≤ n
  refine le_trans ?_ hn
  calc
    _ ≤ 4*a*L^4 + (a+b+109)*L^4 + 38*(K*(((B+10)^4+2)*L^4)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hl)
        (Nat.le_mul_of_pos_right _ (h1.trans hl))) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hwidth))
    _ = A*L^4 := by dsimp only [A]; ring

end PairSimulation.NativeCache

end VPVNP
end Computability
end OAI
