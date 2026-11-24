import OAI.Computability.VPVNP.PairVertexOrdinalReportCosts
import OAI.Computability.VPVNP.PairNativeCacheClock
import OAI.Computability.VPVNP.CursorBranchBudget

/-! # A uniform threshold for selected vertex calls in the live circuit -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open Compression CursorNetwork CursorBounds CursorRouting Filter LiveProgram NativeOperands
open BurstRAM PrivateRAM NetworkKernel

/-- All schedule, cache and history estimates needed by a selected ordinal
hold before fixing the field realization, compressed branch or vertex. -/
theorem eventually_ordinal_geometry {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (c : Constants) (a b scale degree : ℕ)
    (hb : max S.laneBits 5 ≤ scale) :
    ∀ᶠ n : ℕ in atTop, 2048 ≤ n ∧ S.baseDegree ≤ n ∧ Fintype.card B.Entry ≤ n ∧
      (∀ H t, t ≤ work (NativeCache.args c) a b (AssemblerPublic.geometry scale n H) + 76 →
        t + degree + 187 ≤ 44 + n ^ 3) ∧
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits scale n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits scale n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        ∀ z : E.Choices, let Y := E.finalState z
          let chain := E.termChain (B.records f hf T hT X) z
          Y.maxWireWidth ≤ n ∧ ∀ v, chain.occurrences (fun _ => 1) v ≤ n := by
  filter_upwards [eventually_pairBranchBounds B u scale hb, NativeCache.eventually_work_le c a b
    scale,
    eventually_ge_atTop 2048, eventually_ge_atTop S.baseDegree, eventually_ge_atTop (Fintype.card
      B.Entry),
    eventually_ge_atTop degree] with n branch cache hn hd hl hg
  refine ⟨hn,hd,hl,?_,?_⟩
  · intro H t ht
    have small := ht.trans (cache H)
    have wide : 3 * n ≤ n ^ 3 := calc
      3 * n ≤ n * n := Nat.mul_le_mul_right _ (by omega)
      _ ≤ n ^ 3 := by rw [←pow_two]; exact Nat.pow_le_pow_right (by omega) (by decide)
    omega
  · intro base lanes labels hD hT A _ f hf X T E z Y chain
    have actual := branch.2.2 labels hD hT A f hf z
    have hpow {x : ℝ} (hx : x ≤ 1) : (n : ℝ) ^ x ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) hx
    exact ⟨Nat.cast_le.mp ((Nat.cast_le.mpr actual.2.2.2.2.1).trans
      (actual.2.2.2.2.2.1.trans (hpow (by norm_num)))),
      fun v => Nat.cast_le.mp ((actual.2.2.1 v).trans (hpow (by norm_num)))⟩

/-- The bootstrap, fixed-frame header reads and gather of the physical
selected root. Its packed payload has precisely its incident wire width. -/
theorem ordinal_prefix_bounds {w ex lanes : ℕ} (Y : State ex lanes) (v : Y.network.Site)
    (half : Y.network.Half v) (es : List (Event w)) (t degree n : ℕ)
    (probes : countProbes es = 15 + (5 * 2 ^ ex + (NodeArguments.packed Y v half).length))
    (ticks : es.length = t + degree + 187 + (15 + 21 * (2 ^ ex) + 5 * (NodeArguments.packed Y v
      half).length))
    (cache : t + degree + 187 ≤ 44 + n ^ 3) :
    countProbes es ≤ 9 + 6 + 5 * 2 ^ ex + incidentBits Y v ∧
      es.length ≤ 44 + n ^ 3 + (15 + 21 * (2 ^ ex) + 5 * incidentBits Y v) := by
  have size : (NodeArguments.packed Y v half).length = incidentBits Y v :=
    NodeArguments.packed_length Y v half
  rw [size] at probes ticks
  omega

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
