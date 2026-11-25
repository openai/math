import OAI.LinearAlgebra.SpectralBooks.Limit
import OAI.LinearAlgebra.SpectralBooks.Levels
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.FiniteBound
import OAI.LinearAlgebra.SpectralBooks.MarkedRelocation

/-! # Relocating one tensor index along a spectral interval

Powers of a marked tensor factor through the neighboring exterior levels. The
transport estimates bound the difference of endpoint prices and thereby select
the exterior degree for which the two branches have equal limiting cost.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Topology Classical
open Real Filter

namespace SiteTensor

variable {I J : Type} [Fintype I] [Fintype J] [Nonempty J] [DecidableEq I] {K : Type*} [Field K]

/-- The one-index relocation inequality over any field, including degenerate
intervals, coincident sites and one-dimensional marked legs. -/
theorem rawLogPrice_relocate
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} I K) (x : I → J) (i : I) (a z b : J) (u : ℝ) (hu : u ∈ Set.Icc 0 1)
    (hza : rawWireDistance φ c z a = u * rawWireDistance φ c a b)
    (hzb : rawWireDistance φ c z b = (1 - u) * rawWireDistance φ c a b) :
    rawLogPrice φ c (T.group (Function.update x i z)) ≤
      (1 - u) * rawLogPrice φ c (T.group (Function.update x i a)) +
      u * rawLogPrice φ c (T.group (Function.update x i b)) := by
  let w (p : J) := rawLogPrice φ c (T.group (Function.update x i p))
  let d := rawWireDistance φ c a b
  let q := Fintype.card (T.Leg i)
  change w z ≤ (1 - u) * w a + u * w b
  by_cases hT : T.coeff = 0
  · have hw (p : J) : w p = 0 := rawLogPrice_zero φ c _ (funext fun _ => congrFun hT _)
    simp [hw]
  have hm (p r : J) : w p ≤ w r + rawWireDistance φ c p r * logb 2 q := by
    have h := rawLogPrice_move_le φ c hc T hT (Function.update x i r) (Function.update x i p) i
      (fun j hj => by simp [Function.update_of_ne hj])
    simpa only [Function.update_self, rawWireDistance_symm φ c r p] using h
  have ha := hm z a
  have hb := hm z b
  rw [hza] at ha
  rw [hzb] at hb
  change w z ≤ w a + (u * d) * logb 2 q at ha
  change w z ≤ w b + ((1 - u) * d) * logb 2 q at hb
  have hdeg (hdl : d * logb 2 q = 0) : w z ≤ (1 - u) * w a + u * w b := by
    rw [mul_assoc, hdl, mul_zero, add_zero] at ha hb
    linarith only [mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hu.2),
      mul_le_mul_of_nonneg_left hb hu.1]
  by_cases hd : 0 < d
  · by_cases hq : 2 ≤ q
    · apply relocation_le_of_two_bounds (d := d) (q := q) (c := c) hd hq
      · have hab := hm a b
        have hba := hm b a
        rw [rawWireDistance_symm φ c b a] at hba
        exact abs_le.mpr ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
      · intro s hs
        obtain ⟨l, hl, hp, hm⟩ := relocation_level_limits hq hs
        refine ⟨_, _, hp, hm, ?_⟩
        filter_upwards [hl] with n hn
        obtain ⟨S, hS, hw⟩ := Relocation.exists_finPower_update φ c T hT i x n
        have h := Relocation.marked_finite_price_bound φ hn S hS (x ∘ Subtype.val) a z b u d c
          hc rfl hza hzb
        dsimp only [w]
        rw [← hw z, ← hw b, ← hw a]
        exact h
    · have he : q = 0 ∨ q = 1 := by omega
      rcases he with hz | ho <;> apply hdeg <;> simp [*]
  · exact hdeg (by have hz : d = 0 := le_antisymm (le_of_not_gt hd) (rawLogPrice_nonneg φ hc _); rw [hz, zero_mul])

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
