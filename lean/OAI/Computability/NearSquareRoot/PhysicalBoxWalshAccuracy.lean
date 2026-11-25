import OAI.Computability.NearSquareRoot.PhysicalBoxWalsh

/-! # Effective accuracy threshold at an emitted Walsh ticket

This pointwise guarantee uses only the explicit majorant of the fixed
recursion plan. It applies to its actual gathered, rounded, and restored
output on the original coordinate axes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedLayer

open IntegerMultiplication Code Strip FixedPoint FixedCandidate DigitPacking
open ShortFourier.BatchWord SynchronizedLayers.ScheduleProgram SynchronizedPadding Matrix
open PhysicalWalsh PhysicalWalsh.GatherProgram KernelPass PhysicalWalshNode

theorem walshRowOutput_accurate {a W n M : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    (correct : Correct p) (hc : recursionFactor p ≤ M) (hk : precisionCutoff M ≤ addressBits n)
    (hb : Directory n) (hd : 4 ≤ (box n).length) (dir : Bool) (stage : ℕ)
    (inside : stage < (directedPlan (dir,tally (addressBits n))).length)
    (tag : (directedPlan (dir,tally (addressBits n)))[stage].2.1 = kindCode .walsh)
    (x : FixedCandidate.Array n)
    (norm : let _ := BoxFin.modulus_neZero hb
      ‖recordArray (x ∘ index hb)‖ ≤ (2:ℝ)^(13*addressBits n)) :
    let _ := BoxFin.modulus_neZero hb
    let row := boxRow (physicalLayout hb) hd (directedPlan (dir,tally (addressBits n)))[stage]
    ‖recordArray (walshRowOutput hw p hb dir stage inside x ∘ index hb) -
      WithLp.toLp 2 (row *ᵥ (fun z => recordArray (x ∘ index hb) z))‖ ≤ 1/(2:ℝ)^(50*addressBits n) := by
  let _ := BoxFin.modulus_neZero hb
  let bits := walshBits hb dir stage inside
  have hn : ‖recordArray x‖ ≤ (2:ℝ)^(13*addressBits n) :=
    ((ProductRecovery.pull (index hb)).norm_map (recordArray x)).symm.le.trans norm
  have ok := (accurate_of_cutoff ha hw p correct hc hk bits (gatherPerm bits) (gatherPerm_low bits) x hn).2
  apply transferRow (index hb) _ x _ _ _ ok
  exact congrArg (fun A => A *ᵥ (fun j => recordArray x j))
    (flat_walshRow hb hd ⟨stage,inside⟩ tag)

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
