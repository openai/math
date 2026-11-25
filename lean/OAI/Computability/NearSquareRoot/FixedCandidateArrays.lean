import OAI.Computability.NearSquareRoot.FixedCandidateFrame
import OAI.Computability.NearSquareRoot.ProductRealization
import OAI.Computability.NearSquareRoot.PrecisionLayerReadout

/-! # Ordered stream semantics of a fixed-exponent multiplication command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code Bits DigitPacking FixedPoint ResidueFourier
open ProductRecovery

noncomputable section
set_option maxHeartbeats 1400000

abbrev box (n : ℕ) := CoprimeBox.box (addressBits n)
abbrev Axis (n : ℕ) := PaddedBox (BoxFin.modulus (box n)) (BoxFin.padding (box n))
abbrev Directory (n : ℕ) := ValidDirectory (addressBits n)
abbrev Program {n : ℕ} (h : Directory n) :=
  letI := BoxFin.modulus_neZero h
  Layers (Axis n) (addressBits n)

variable {n : ℕ} (h : Directory n)

def index : Axis n ≃ Fin (capacity n) :=
  letI := BoxFin.modulus_neZero h
  BoxFin.recordIndex h

def ideal :=
  letI := BoxFin.modulus_neZero h
  paddedIsometry (BoxFin.modulus (box n)) (BoxFin.padding (box n))

def ForwardOK (F : Program h) : Prop :=
  letI := BoxFin.modulus_neZero h
  F.Approximates (ideal h).toLinearIsometry

def InverseOK (J : Program h) : Prop :=
  letI := BoxFin.modulus_neZero h
  J.Approximates (ideal h).symm.toLinearIsometry

structure Plan {n : ℕ} (h : Directory n) where
  forward : Program h
  inverse : Program h
  fwd_ok : ForwardOK h forward
  inv_ok : InverseOK h inverse

def input (x : Word) : Array n :=
  letI := BoxFin.modulus_neZero h
  ProductRecovery.physicalInput h x

def route (v : Array n) : Array n :=
  letI := BoxFin.modulus_neZero h
  letI : NeZero (directoryVolume (addressBits n)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  v ∘ (BoxFin.crtSlotPerm h).symm

def eval (F : Program h) (v : Array n) : Array n :=
  letI := BoxFin.modulus_neZero h
  F.run (v ∘ index h) F.count ∘ (index h).symm

/-- Initial working range within which a complete physical transform operates. -/
def Admissible (v : Array n) : Prop :=
  letI := BoxFin.modulus_neZero h
  ‖recordArray (v ∘ index h)‖ ≤ (2:ℝ)^(12*addressBits n)

def pointwise (x y : Array n) : Array n := fun j => FixedPoint.multiply (addressBits n) (x j) (y j)

def rescale (n : ℕ) (u : Array n) : Array n :=
  let k := addressBits n
  fun j => FixedPoint.multiply k (sqrtRecord (fractionBits k) (componentBits k) (directoryVolume k)) (u j)

theorem records_input {x : Word} (hx : x.length = n) (hn : 2 ≤ n) :
    encodedBoxed x = records (input h x) := by
  subst n
  let _ := BoxFin.modulus_neZero h
  let _ : NeZero (directoryVolume (addressBits x.length)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  exact ProductRecovery.encoded_physicalInput x hn h

theorem eval_comp_index (F : Program h) (r : Array n) :
    letI := BoxFin.modulus_neZero h
    eval h F r ∘ index h = F.run (r ∘ index h) F.count := by
  funext i
  exact congrArg _ ((index h).symm_apply_apply i)

theorem routed_input (z : Word) :
    letI := BoxFin.modulus_neZero h
    letI : NeZero (directoryVolume (addressBits n)) := ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
    route h (input h z) ∘ index h = inputRecords _ (BoxFin.padding (box n)) (BoxFin.pairwise h) n z := by
  let _ := BoxFin.modulus_neZero h
  let _ : NeZero (directoryVolume (addressBits n)) := ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  exact ProductRecovery.route_physicalInput h z

theorem pointwise_order (r s : Array n) :
    letI := BoxFin.modulus_neZero h
    pointwise r s ∘ index h = productArray (r ∘ index h) (s ∘ index h) := rfl

/-- The flattened forward/pointwise/inverse/scale commands supply precisely the
post-transform input of the physical mask and carry readout. -/
theorem eval_output (F J : Program h) (x y : Word) :
    let fs z := eval h F (route h (input h z))
    let p := rescale n (eval h J (pointwise (fs x) (fs y)))
    letI := BoxFin.modulus_neZero h
    letI : NeZero (directoryVolume (addressBits n)) :=
      ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
    p = scaledLayerRecords h F J x y := by
  dsimp only
  let _ := BoxFin.modulus_neZero h
  let _ : NeZero (directoryVolume (addressBits n)) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  let fs z := eval h F (route h (input h z))
  change rescale n (fun j => J.run (pointwise (fs x) (fs y) ∘ index h) J.count ((index h).symm j)) = _
  rw [pointwise_order]
  dsimp only [fs]
  rw [eval_comp_index, eval_comp_index, routed_input, routed_input]
  rfl

/-- The actual synchronized factorizations and local finite-register operators
provide certified plans for every sufficiently large operand length. -/
theorem eventually_plan : ∀ᶠ n in Filter.atTop, ∃ h : Directory n, Nonempty (Plan h) := by
  filter_upwards [eventually_valid_multiplication_box, addressBits_tendsto_atTop.eventually_ge_atTop 1024]
    with n h hk
  refine ⟨h, ?_⟩
  let _ := BoxFin.modulus_neZero h
  have hw := SynchronizedBlocks.three_width_lt hk
  have hd := SynchronizedBlocks.four_le_length h hw
  obtain ⟨F,J,_,_,hf,hj⟩ := valid_box_programs h hd hk (by omega)
    (boxStage_of_flatWalsh h hd (by omega) (fun bits hu =>
      ⟨selectedWalshStep bits, selectedWalshStep_error (by omega) bits hu⟩))
  exact ⟨⟨F,J,hf,hj⟩⟩

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
