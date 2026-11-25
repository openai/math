import OAI.Computability.IntegerMultiplication.Fourier.Phase
import OAI.Computability.NearSquareRoot.SynchronizedChirpBound
import OAI.Computability.NearSquareRoot.SynchronizedCirculant

/-! # Integer root addresses of the two chirp coefficient tables

The angle reductions use Euclidean remainders so every root index is valid
even for the negative indices in the zero-extended convolution kernel.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChirpTable

open IntegerMultiplication.Fourier Finset ComplexConjugate

def residue (d : ℕ) (x : ℤ) : ℕ := (x % (d : ℤ)).toNat

theorem residue_lt {d : ℕ} (hd : 0 < d) (x : ℤ) : residue d x < d := by
  have hpos : (0 : ℤ) < d := by exact_mod_cast hd
  have hn := Int.emod_nonneg x hpos.ne'
  have hl := Int.emod_lt_of_pos x hpos
  unfold residue
  omega

theorem phase_residue {d : ℕ} (hd : 0 < d) (x : ℤ) :
    phase d (residue d x : ℤ) = phase d x := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [phase_inj, residue, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hd.ne'))]
  refine ⟨-(x / (d : ℤ)), ?_⟩
  rw [Int.emod_def]
  ring

/-- Root address of the zero-extended chirp at displacement `h` and frequency `ξ`. -/
def bluesteinIndex (a r ξ : ℕ) (h : ℤ) : ℕ :=
  residue (2*a*r) (-h^2 * r + 2*a*ξ*h)

/-- Root address of the periodic chirp in the diagonal spectrum at frequency `ξ`. -/
def spectrumIndex (a ξ h : ℕ) : ℕ :=
  residue (2*a) (2*(ξ : ℤ)*h - (h : ℤ)^2 - (a % 2 : ℕ)*h)

theorem bluesteinIndex_lt {a r : ℕ} (ha : 0 < a) (hr : 0 < r) (ξ : ℕ) (h : ℤ) :
    bluesteinIndex a r ξ h < 2*a*r := residue_lt (by positivity) _

theorem spectrumIndex_lt {a : ℕ} (ha : 0 < a) (ξ h : ℕ) :
    spectrumIndex a ξ h < 2*a := residue_lt (by positivity) _

private theorem chirp_phase_cis (t : ℝ) : Chirp.phase t = cis t := by
  unfold Chirp.phase cis
  push_cast
  congr 1
  ring

theorem short_phase_cis (t : ℝ) : ShortFourier.phase t = cis t := by
  unfold ShortFourier.phase cis
  push_cast
  congr 1
  ring

/-- The `2a-1` samples in the Bluestein multiplier use roots of a single
order `2ar`, independently of the signs of their integer displacements. -/
theorem bluestein_ordered_sum {a r : ℕ} (ha : 0 < a) (hr : 0 < r) (ξ : ℕ) :
    Chirp.bluesteinMultiplier a ((ξ : ℝ) / r) =
      (Real.sqrt a : ℂ)⁻¹ * ∑ h ∈ Ioo (-(a : ℤ)) (a : ℤ),
        phase (2*a*r) (bluesteinIndex a r ξ h : ℤ) := by
  unfold Chirp.bluesteinMultiplier
  congr 1
  apply sum_congr rfl
  intro h _
  rw [bluesteinIndex, phase_residue (by positivity), chirp_phase_cis, phase]
  congr 1
  push_cast
  field_simp

/-- The `a` samples of the spectral phase diagonal use roots of order `2a`.
The index includes the linear parity term of the periodic chirp. -/
theorem spectrum_ordered_sum {a : ℕ} [NeZero a] (j : Fin a) :
    ShortFourier.chirpSpectrum a j =
      (Real.sqrt a : ℂ)⁻¹ * ∑ h : Fin a, phase (2*a) (spectrumIndex a j.val h.val : ℤ) := by
  have ha := NeZero.pos a
  rw [ShortFourier.chirpSpectrum, ShortFourier.circulantSpectrum, mul_sum]
  apply sum_congr rfl
  intro h _
  rw [ShortFourier.chirpKernel, mul_assoc, ShortFourier.chirp, ShortFourier.phase_conj,
    short_phase_cis, short_phase_cis, ← cis_neg, ← cis_add,
    spectrumIndex, phase_residue (by positivity), phase]
  congr 2
  unfold ShortFourier.chirpAngle
  push_cast [-Int.natCast_mod]
  field_simp
  have hm : (((a : ℤ) % 2 : ℤ) : ℝ) = ((a % 2 : ℕ) : ℝ) := by
    change (((a % 2 : ℕ) : ℤ) : ℝ) = _
    exact Int.cast_natCast _
  rw [hm]
  ring


/-- Enumerating a chirp row left to right uses unsigned loop indices. -/
theorem bluestein_fin_sum {a r : ℕ} (ha : 0 < a) (hr : 0 < r) (ξ : ℕ) :
    Chirp.bluesteinMultiplier a ((ξ : ℝ) / r) = (Real.sqrt a : ℂ)⁻¹ *
      ∑ k : Fin (2*a-1), phase (2*a*r) (bluesteinIndex a r ξ ((k.val : ℤ) + 1 - a) : ℤ) := by
  rw [bluestein_ordered_sum ha hr]
  congr 1
  symm
  apply sum_bij (fun (k : Fin (2*a-1)) _ => (k.val : ℤ) + 1 - a)
  · intro k _
    simp only [mem_Ioo]
    have := k.isLt
    omega
  · intro i _ j _ h
    apply Fin.ext
    omega
  · intro h hh
    simp only [mem_Ioo] at hh
    refine ⟨⟨(h + a - 1).toNat, by omega⟩, mem_univ _, ?_⟩
    simp only
    omega
  · intros
    rfl

end ChirpTable

end NearSquareRoot
end Computability
end OAI
