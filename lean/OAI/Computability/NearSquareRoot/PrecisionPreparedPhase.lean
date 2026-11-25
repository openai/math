import OAI.Computability.NearSquareRoot.PrecisionDilation
import OAI.Computability.NearSquareRoot.PrecisionRecordAdjoint

/-! # Common output format for polynomial-time local phase setup -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Grid Dusk Strip Staff Brief Star Carry

variable {J : Type} {s : Regime J} {bits : J → ℕ} {z : J → ℂ}

/-- A local coefficient computed from the header on the setup stacks, in a
single finite record format shared by chirps, dilation pairs and radix phases. -/
def Prepared (s : Regime J) (bits : J → ℕ) (z : J → ℂ) : Prop :=
  ∃ v : (j : J) → Grain (bits j + 5), s.Has (fun j ↦ mark (v j)) ∧
    ∀ j, ‖meaning (bits j + 2) (bits j + 5) (v j) - z j‖ ≤ 1 / (2 : ℝ) ^ bits j

/-- Re-encode a represented phase at the required working precision and width.
The output scaling and signed truncation run in the setup language. -/
theorem reencodePhase {p w goalP goalW : J → ℕ}
    (P : Realizes s p) (P' : Realizes s goalP) (W' : Realizes s goalW)
    (hp : ∀ j, bits j + 2 ≤ goalP j) (hw : ∀ j, goalP j + 3 ≤ goalW j)
    (input : (j : J) → Grain (w j)) (built : s.Has (fun j ↦ mark (input j)))
    (hz : ∀ j, ‖z j‖ = 1)
    (herr : ∀ j, ‖meaning (p j) (w j) (input j) - z j‖ ≤ 1 / (2 : ℝ) ^ (bits j + 1)) :
    ∃ output : (j : J) → Grain (goalW j), s.Has (fun j ↦ mark (output j)) ∧
      ∀ j, ‖meaning (goalP j) (goalW j) (output j) - z j‖ ≤ 1 / (2 : ℝ) ^ bits j := by
  let value j := meaning (p j) (w j) (input j)
  have hc : Curve s value := by
    have hr := grainRat_realized P input built
    have hreal : Curve s (fun j ↦ toComplex (grainRat (p j) (input j))) := hr
    simpa only [grainRat_value] using hreal
  have bound j : ‖value j‖ ≤ 2 := by
    have h := norm_add_le (value j - z j) (z j)
    rw [sub_add_cancel, hz] at h
    have h1 : 1 / (2 : ℝ) ^ (bits j + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
    linarith [show ‖value j - z j‖ ≤ _ from herr j]
  obtain ⟨out, ready, err⟩ := Star.stroke value goalP goalW P' W' hc (fun j ↦ by
    have ha : 1 ≤ (2 : ℝ) ^ goalP j := one_le_pow₀ (by norm_num)
    have hc := mul_le_mul_of_nonneg_right (bound j) (ha.trans' (by norm_num : (0:ℝ) ≤ 1))
    have hw' : (2 : ℝ) ^ (goalP j + 3) ≤ 2 ^ goalW j :=
      pow_le_pow_right₀ (by norm_num) (hw j)
    rw [pow_add] at hw'
    norm_num at hw'
    nlinarith)
  refine ⟨out, ready, fun j ↦ ?_⟩
  have small := Star.drop_le (hp j)
  have hsum := (norm_sub_le_norm_sub_add_norm_sub _ (value j) _).trans
    (add_le_add (err j) (herr j))
  refine hsum.trans ?_
  calc _ ≤ 2 * Star.drop_ (bits j + 2) + 1 / (2 : ℝ) ^ (bits j + 1) := by gcongr
       _ = _ := by simp only [Star.drop_, one_div, inv_pow, pow_add]; ring

/-- Normalize an already generated coefficient to the common phase record. -/
theorem Prepared.ofGrain {p w : J → ℕ} (P : Realizes s p) (B : Realizes s bits)
    (input : (j : J) → Grain (w j)) (built : s.Has (fun j ↦ mark (input j)))
    (hz : ∀ j, ‖z j‖ = 1)
    (herr : ∀ j, ‖meaning (p j) (w j) (input j) - z j‖ ≤ 1 / (2 : ℝ) ^ (bits j + 1)) :
    Prepared s bits z := reencodePhase P (B.plus (.fix 2)) (B.plus (.fix 5))
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) input built hz herr

/-- Roots of unity with an arbitrary signed numerator and positive binary
denominator, written immediately in the common record format. -/
theorem Prepared.root (B : Realizes s bits) {numer : J → ℤ} {denom : J → ℕ}
    (N : Signed s numer) (D : Figure s denom) (pos : ∀ j, 0 < denom j) :
    Prepared s bits (fun j ↦ Fourier.phase (denom j) (numer j)) := by
  obtain ⟨out,ready,err⟩ := computeAngleAt (fun j ↦ bits j + 2) (fun j ↦ bits j + 5)
    (B.plus (.fix 2)) (B.plus (.fix 5)) (fun j ↦ by
      rw [pow_add, pow_add]; norm_num
      linarith [show 1 ≤ (2 : ℝ) ^ bits j from one_le_pow₀ (by norm_num)])
    numer N denom D pos
  refine ⟨out, ready, fun j ↦ (err j).trans ?_⟩
  simp only [one_div, inv_pow, pow_add]
  norm_num
  nlinarith [inv_nonneg.mpr (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (bits j))]

theorem Prepared.adjoint {flag : J → Bool} (F : s.Has flag) (h : Prepared s bits z) :
    Prepared s bits (fun j ↦ adjointValue (flag j) (z j)) := by
  obtain ⟨v, h, err⟩ := h
  exact ⟨_, computeAdjoint F h, fun j ↦ (adjoint_error _ _ _ _ _).le.trans (err j)⟩

/-- Dispatch a finite tag by a branch evaluated from the setup header. -/
theorem Prepared.branch {flag : J → Bool} {x y : J → ℂ} (F : s.Has flag)
    (hx : Prepared s bits x) (hy : Prepared s bits y) :
    Prepared s bits (fun j ↦ bif flag j then x j else y j) := by
  obtain ⟨A, hA, eA⟩ := hx
  obtain ⟨B, hB, eB⟩ := hy
  refine ⟨fun j ↦ bif flag j then A j else B j, ?_, ?_⟩
  · have pair := F.pair (hA.pair hB)
    let choose (x : Bool × Dusk.Pair × Dusk.Pair) := bif x.1 then x.2.1 else x.2.2
    have hchoose : Easy choose := Grid.easy_bool _ _ _ Easy.fst (by fun_prop) (by fun_prop)
    have res := pair.ez hchoose
    have eqn j : choose (flag j, mark (A j), mark (B j)) =
        mark (bif flag j then A j else B j) := by cases h : flag j <;> rfl
    simpa only [Function.comp_def, eqn] using res
  · intro j
    cases h : flag j
    · simpa [h] using eB j
    · simpa [h] using eA j

end PhaseTable

end NearSquareRoot
end Computability
end OAI
