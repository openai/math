import OAI.Computability.VPVNP.LiveCompressedPairTerminalCharge
import OAI.Computability.VPVNP.LiveCompressedPairReportCaps
import OAI.Computability.VPVNP.CompressorDirectoryBudget
import OAI.Computability.VPVNP.PairLinkSlack

/-! # A uniform share of the live budget for the entire terminal traversal -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open Compression CursorNetwork CursorBounds NetworkKernel Filter BurstRAM
open private blocks_le_log from OAI.Computability.VPVNP.CompressorDirectoryBudget

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- A single length threshold covers every selected history and every
final vertex. The resource estimates use only the fixed program constants. -/
theorem eventually_terminal_share (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) (boot close site q : ℕ) :
    let C := terminalCoefficient S.baseDegree S.steps B.recordLimit boot close site
    ∀ᶠ n : ℕ in atTop,
      let T := blockCount (u.θ : ℝ) n
      T ≤ n.log2+1 ∧ ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : T*S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let E := B.execute f hf T hT X
        ∀ z : E.Choices,
          let Y := E.finalState z
          let chain := E.termChain (B.records f hf T hT X) z
          320*branchAccesses X Y chain C q n ≤ processorCount b n * liveCapacity u n ∧
            ∀ v, siteAccesses Y chain site q n v + 9 ≤ liveCapacity u n := by
  intro C
  filter_upwards [eventually_pairAccesses B u b hb C q (ε := 1/320) (by norm_num),
    eventually_pairBurstSlack u 9, eventually_ge_atTop 1] with n estimates margin hn
  intro T
  refine ⟨blocks_le_log B u hn,?_⟩
  intro base lanes labels hD hT A _ f hf X E z Y chain
  have result := estimates labels hD hT A f hf z
  rw [liveCapacity_eq]
  refine ⟨integer_cost_share (by decide : 0<320) result.1,?_⟩
  intro v
  have hsite : siteAccesses Y chain site q n v ≤ siteAccesses Y chain C q n v := by
    apply Nat.mul_le_mul_right
    exact Nat.le_add_left ..
  have small := (Nat.cast_le.mpr hsite : (siteAccesses Y chain site q n v : ℝ) ≤ _).trans (result.2.1 v)
  have lim : (siteAccesses Y chain site q n v : ℝ)+9 ≤ (liveBucket u.δ n : ℝ) := by
    exact (add_le_add_left small 9).trans margin
  exact_mod_cast lim

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
