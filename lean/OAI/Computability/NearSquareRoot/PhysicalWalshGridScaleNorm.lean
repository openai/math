import OAI.Computability.NearSquareRoot.PhysicalWalshGridMixNorm
import OAI.Computability.NearSquareRoot.KernelScaleNorm
import OAI.Computability.NearSquareRoot.PhysicalWalshStored

/-! # Headroom and error for a physical dyadic scaling pass

Every selected entry uses the dyadic coefficient at its physical address signature.
The operator gain depends only on the finite coefficient table. The local error
accounts for one fixed-point rounding per selected complex record.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshGrid

open IntegerMultiplication PhysicalWalsh KernelPass

variable {a q : ℕ} {U F J : Type} [Fintype J]
variable (L : KernelScaleBank.Layout a U F) (w : U → ℕ)

/-- Ideal scale on a row of physical addresses, including its spectator entries. -/
noncomputable def idealScaleRow (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (u : U) (select : J → F)
    (v : EuclideanSpace ℂ J) : EuclideanSpace ℂ J :=
  KernelScaleNorm.action table (KernelScaleBank.signature L test u ∘ select) v

theorem idealScaleRow_gain (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (u : U) (select : J → F)
    (v : EuclideanSpace ℂ J) :
    ‖idealScaleRow L test table u select v‖ ≤ KernelScaleNorm.gain table * ‖v‖ :=
  KernelScaleNorm.gain_bound ..

/-- The norm of the decoded row bounds the accumulator for each stored address.
The selector may repeat addresses. -/
theorem scaleFits_of_row (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (p : ℕ) (u : U) (select : J → F)
    (cover : ∀ z ∈ L.rows u, ∃ j, select j = z) (x : (layout L w).Row u) (M : ℝ)
    (hx : ‖decodeRow L w p u select x‖ ≤ M)
    (hw : (KernelScaleNorm.gain table : ℝ)*M*2^p < 2^(w u)) :
    scaleFits L w test table u x := by
  intro z hz
  obtain ⟨j, rfl⟩ := cover z hz
  exact KernelScaleNorm.fits_of_norm p (w u) table (KernelScaleBank.signature L test u ∘ select)
    (x ∘ select) M hx hw j

/-- One truncation on each selected complex record and linear propagation of
the incoming row perturbation through the fixed diagonal map. -/
theorem scale_row_error (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (p : ℕ) (u : U) (select : J → F)
    (x : (layout L w).Row u) (v : EuclideanSpace ℂ J) (M E : ℝ)
    (hx : ‖decodeRow L w p u select x‖ ≤ M)
    (herr : ‖decodeRow L w p u select x - v‖ ≤ E)
    (hw : (KernelScaleNorm.gain table : ℝ)*M*2^p < 2^(w u)) :
    ‖decodeRow L w p u select (scale L w test table u x) - idealScaleRow L test table u select v‖ ≤
      Real.sqrt (Fintype.card J) * ((2:ℝ)/2^p) + KernelScaleNorm.gain table*E := by
  have h := KernelScaleNorm.round_scale_perturbed p (w u) table
    (KernelScaleBank.signature L test u ∘ select) (x ∘ select) v M hx hw
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg _)) _)

/-- The numerical guard and bound for the actual packed row returned by the
unconditional physical command. -/
theorem scaleFits_error_of_norm (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (p : ℕ) (u : U) (select : J → F)
    (cover : ∀ z ∈ L.rows u, ∃ j, select j = z) (x : (layout L w).Row u)
    (v : EuclideanSpace ℂ J) (M E : ℝ) (hx : ‖decodeRow L w p u select x‖ ≤ M)
    (herr : ‖decodeRow L w p u select x - v‖ ≤ E)
    (hw : (KernelScaleNorm.gain table : ℝ)*M*2^p < 2^(w u)) :
    scaleFits L w test table u x ∧
    ‖decodeRow L w p u select (storedScale L w test table u x) - idealScaleRow L test table u select v‖ ≤
      Real.sqrt (Fintype.card J) * ((2:ℝ)/2^p) + KernelScaleNorm.gain table*E := by
  have guard := scaleFits_of_row L w test table p u select cover x M hx hw
  refine ⟨guard, ?_⟩
  simpa [storedScale, guard] using
    scale_row_error L w test table p u select x v M E hx herr hw

/-- Taking one index for every list entry covers the complete tape row. -/
theorem scaleFits_serial (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (p : ℕ) (u : U) (x : (layout L w).Row u) (M : ℝ)
    (hx : ‖decodeRow L w p u (L.rows u).get x‖ ≤ M)
    (hw : (KernelScaleNorm.gain table : ℝ)*M*2^p < 2^(w u)) :
    scaleFits L w test table u x :=
  scaleFits_of_row L w test table p u _ (fun _ h => List.mem_iff_get.mp h) x M hx hw

end PhysicalWalshGrid

end NearSquareRoot
end Computability
end OAI
