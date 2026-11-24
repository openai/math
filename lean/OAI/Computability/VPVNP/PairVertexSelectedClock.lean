import OAI.Computability.VPVNP.CursorBranchBudget
import OAI.Computability.VPVNP.PairNativeCacheClock
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace
import OAI.Computability.VPVNP.CompressorLevelCounts

/-! # Private clock of a terminal vertex on a selected compressor branch -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open Compression CursorNetwork CursorBounds CursorRouting Filter LiveProgram NativeOperands

private theorem time_estimate {n degree slots g t packet occurrences maxTicks big : ℕ}
    (hn : 256 ≤ n) (deg : degree ≤ n) (slot : slots ≤ degree) (labels : g ≤ n)
    (cache : t ≤ n) (width : packet ≤ 2*slots*n) (depth : occurrences ≤ n)
    (job : maxTicks ≤ big) (large : n*n ≤ big) :
    t+degree+187+(15+21*slots+5*packet)+(15+maxTicks)*occurrences+7*g+46 ≤ big*n*n := by
  have hp : packet ≤ 2*n*n := width.trans (Nat.mul_le_mul_right n (Nat.mul_le_mul_left 2 (slot.trans deg)))
  have hj := Nat.mul_le_mul (Nat.add_le_add_left job 15) depth
  have hn' : n ≤ n*n := Nat.le_mul_of_pos_right _ (by omega)
  have hbig : big ≤ big*n := Nat.le_mul_of_pos_right _ (by omega)
  have hroom := Nat.mul_le_mul_left (big*n) (show 64 ≤ n by omega)
  nlinarith only [cache,deg,slot,labels,hp,hj,hn',large,hbig,hroom,hn]

set_option exponentiation.threshold 10000 in
/-- On the actual cursor network, uniform estimates for the field widths,
number of occurrences and cache initialization suffice for the complete
native active-site clock, including its phase-controller allowance. -/
theorem eventually_active_clock {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (c : Constants) (a b scale : ℕ)
    (hb : max S.laneBits 5 ≤ scale) (degree : ℕ) (slots : 2^(S.degreeExponent 0) ≤ degree) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ} (labels : Fin (virtualBits scale n) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits scale n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (κ : B.Entry → A) (hκ : B.IsSolution κ),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute κ hκ T hT X
      B.growthConstant^T ≤ n ∧ ∀ z : E.Choices,
        let Y := E.finalState z
        let chain := E.termChain (B.records κ hκ T hT X) z
        ∀ (v : Y.network.Site) (half : Y.network.Half v) (H t maxTicks : ℕ),
          t ≤ work (NativeCache.args c) a b (AssemblerPublic.geometry scale n H)+76 →
          maxTicks ≤ n^9000 →
          t+degree+187+(15+21*2^(S.degreeExponent 0)+5*(NodeArguments.packed Y v half).length) +
            (15+maxTicks)*chain.occurrences (fun _ => 1) v + 7*Fintype.card B.Entry+46 ≤ n^9999 := by
  filter_upwards [eventually_pairBranchBounds B u scale hb, NativeCache.eventually_work_le c a b scale,
    eventually_ge_atTop 256, eventually_ge_atTop degree, eventually_ge_atTop (Fintype.card B.Entry)]
    with n branch cache hn deg labelsCount
  intro base lanes labels hD hT A _ κ hκ X T E
  have hpow {x : ℝ} (h : x ≤ 1) : (n : ℝ)^x ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) h
  have hg := history_pow_blockCount_le
    (show (1 : ℝ) ≤ B.growthConstant by exact_mod_cast (show 1 ≤ B.growthConstant from (by decide : 1 ≤ 2).trans B.growthConstant_ge_two))
    (show (0 : ℝ) ≤ u.θ by exact_mod_cast u.theta_pos.le) (show 1 ≤ n by omega) u.growth
  have capacity : B.growthConstant^T ≤ n := by
    exact_mod_cast hg.trans (hpow (by norm_num))
  refine ⟨capacity,?_⟩
  intro z Y chain v half H t maxTicks ht hj
  have actual := branch.2.2 labels hD hT A κ hκ z
  have depth : chain.occurrences (fun _ => 1) v ≤ n :=
    Nat.cast_le.mp ((actual.2.2.1 v).trans (hpow (by norm_num)))
  have width : Y.maxWireWidth ≤ n := Nat.cast_le.mp
    ((Nat.cast_le.mpr actual.2.2.2.2.1).trans (actual.2.2.2.2.2.1.trans (hpow (by norm_num))))
  have packet := (NodeArguments.packed_length_le Y v half).trans (Nat.mul_le_mul_left _ width)
  have large : n*n ≤ n^9000 := (by rw [←pow_two]; exact Nat.pow_le_pow_right (by omega) (by decide))
  have small := time_estimate hn deg slots labelsCount (ht.trans (cache H)) packet depth hj large
  calc
    _ ≤ n^9000*n*n := small
    _ = n^9002 := by rw [show (9002:ℕ)=9000+2 by decide,pow_add,pow_two,Nat.mul_assoc]
    _ ≤ n^9999 := Nat.pow_le_pow_right (by omega) (by decide)

set_option exponentiation.threshold 10000 in
/-- Credit for all remaining vertices of one root fits in a private word.
It applies to every prefix even if a later kernel rejects its input. -/
theorem eventually_histogram_credit (b : ℕ) (hb : 1 ≤ b) :
    ∀ᶠ n : ℕ in atTop, n*n^9000 < 2^(wordBits b n) := by
  filter_upwards [BurstRAM.eventually_polynomial_lt_wordModulus 9001] with n h
  rw [← pow_succ' n 9000]
  exact h _ (BurstRAM.log2_le_addressWidth hb n)

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
