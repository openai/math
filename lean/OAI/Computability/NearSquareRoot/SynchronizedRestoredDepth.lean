import OAI.Computability.NearSquareRoot.SynchronizedBorrowedPhases
import OAI.Computability.NearSquareRoot.SynchronizedDilationLayer
import OAI.Computability.NearSquareRoot.SynchronizedPrimitiveHalf

/-! # Primitive-layer depth of the exact restored circuit -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedRestoration
open scoped Matrix

/-- A reflection in the image of `V E` uses one copy of `V` and its adjoint.
Both bare reflections are local phases on coordinates. -/
theorem amplifiedCircuit_word {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (E : Matrix m n ℂ) (V : Matrix m m ℂ) (j t : ℕ) (hV : V * Vᴴ = 1)
    (hw : HasShortWord V t) (hP : ShortLayer ((2 : ℝ) • (E * Eᴴ) - 1))
    (hQ : ShortLayer (1 - (2 : ℝ) • (E * Eᴴ))) :
    HasShortWord (amplifiedCircuit E V j) (j * (2*t + 2) + t) := by
  have hconj : V * ((2 : ℝ) • (E * Eᴴ) - 1) * Vᴴ =
      (2 : ℝ) • (V * (E * Eᴴ) * Vᴴ) - 1 := by
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul,
      Matrix.smul_mul, hV]
  have hr := (((hw.append (.singleton hP)).append hw.adjoint).append (.singleton hQ))
  rw [hconj] at hr
  apply ((hr.power j).append hw).mono
  rw [show t+1+t+1=2*t+2 by omega]

/-- A dyadic Fourier word on the padded length gives a linear-depth word for
the actual dilation, with three extra primitive layers. -/
theorem shortDilation_word {a r t : ℕ} (ha : 0 < a) (har : a ≤ r)
    (hF : HasShortWord (normalizedFourier r) t) :
    HasShortWord (shortDilation har) (2*t+3) := by
  have hz := (calibrated_dilation_shortLayer (r := r) ha).1
  have hp (x : ℝ) : ‖phase x‖ = 1 := by simp [phase, Complex.norm_exp]
  have hg : ShortLayer (extend (activeFiber har) (bluesteinDiagonal a)) :=
    shortLayer_extend_phase har _ (fun _ => hp _)
  have hhalf := hF.firstHalf
  have hv := (hhalf.adjoint.append (.singleton hz)).append hhalf
  exact ((HasShortWord.singleton hg).append hv |>.append (.singleton hg)).mono (by omega)

/-- Explicit linear dependence on the depth of the normalized dyadic FFT.
The coefficient includes both uses of the amplified transform and all 64
rounds of reflections. -/
theorem restoredShortTransform_word {a r t : ℕ} [NeZero a] [NeZero r]
    (har : a ≤ r) (hF : HasShortWord (normalizedFourier r) t) :
    HasShortWord (restoredShortTransform har) (516*t+1033) := by
  have hV := shortDilation_isometry (NeZero.pos a) har
  have hQ := shortLayer_reflection_pair har
  have hw := amplifiedCircuit_word _ _ 64 _ (mul_eq_one_comm.mp hV)
    (shortDilation_word (NeZero.pos a) har hF) hQ.1 hQ.2
  have h₁ := shortLayer_extend_phase har (fun i : Fin a => chirp a i.val)
    (fun i => by simp [chirp, phase, Complex.norm_exp])
  have h₂ := shortLayer_extend_phase har (chirpSpectrum a) chirpSpectrum_norm
  have h₃ := shortLayer_extend_phase har (fun i : Fin a => chirp a (-(i.val : ℤ)))
    (fun i => by simp [chirp, phase, Complex.norm_exp])
  exact (((((HasShortWord.singleton h₁).append hw.adjoint).append (.singleton h₂)).append hw).append
    (.singleton h₃)).mono (by omega)

/-- The same primitive word implements the padded active Fourier transform on
arbitrary data in the ambient doubled space. -/
theorem activeFourier_word_of_radix {a k : ℕ} [NeZero a] (hr : 2*a-1 ≤ 2^k)
    (har : a ≤ 2^k) (hF : HasShortWord (normalizedFourier (2^k)) (2*k+1)) :
    HasShortWord (extend (activeFiber har) (normalizedFourier a)) (3000*(k+1)) := by
  rw [← restoredShortTransform_eq hr har]
  exact (restoredShortTransform_word har hF).mono (by omega)

end ShortFourier

end NearSquareRoot
end Computability
end OAI
