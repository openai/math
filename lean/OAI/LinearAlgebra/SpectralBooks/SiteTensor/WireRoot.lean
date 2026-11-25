import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nodes
import OAI.LinearAlgebra.SpectralBooks.MarkedRelocation
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct

/-! # The identity wire at the root of the relocation tree

Mark one end of a binary wire of width `n`, leaving the other end as the
only background index. Its value at arbitrary placements of the two ends
is exactly `n` times their wire distance.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation.WireNode

variable {K : Type*} [Field K] {J : Type}

/-- Initial node of width `n`, before any exterior splitting. -/
def root (base : J) (n : ℕ) : WireNode K J (2^n) := by
  let W := Raw.diagonal (Fin 2) K (Fin (2^n))
  let i : Fin 2 := 0
  refine ⟨{j : Fin 2 // j ≠ i}, fun j => W.Leg j.1,
    ⟨1, by decide⟩, fun _ => base, markCoeff W i, ?_, 0⟩
  intro hz
  have hW : ofRaw W = 0 := (ofRaw_eq_iff.mpr (marked_group_equivalent W i)).symm.trans
    ((ofRaw_eq_zero_iff _).mpr (funext fun x => congrFun hz (fun k => x ((placeMark Subtype.val i) k) ⟨k, rfl⟩)))
  let label : Fin (2^n) := ⟨0, pow_pos (by decide) _⟩
  have h := congrFun ((ofRaw_eq_zero_iff W).mp hW) (fun _ => label)
  change (Raw.diagonal (Fin 2) K (Fin (2^n))).coeff (fun _ => label) = 0 at h
  simp [Raw.diagonal_coeff_at i] at h

variable [Fintype J] [Nonempty J]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))

/-- The exponent table at the root consists of the pairwise distances times
the wire width, at every choice of the two marked locations. -/
theorem cost_root (c : ℝ) (base : J) (n : ℕ) (p q : J) :
    cost φ c (root base n) p q = n * rawWireDistance φ c p q := by
  let W := Raw.diagonal (Fin 2) K (Fin (2^n))
  let σ : Fin 2 → J := ![p,q]
  have hup : Function.update σ 0 p = σ := Function.update_eq_self_iff.mpr rfl
  have hg := rawLogPrice_update_eq_mark φ c W 0 σ p
  rw [hup] at hg
  let : DecidableEq {j : Fin 2 // j ≠ 0} := fun _ _ => Classical.propDecidable _
  have hb : Function.update (fun _ : {j : Fin 2 // j ≠ 0} => base) ⟨1, by decide⟩ q =
      σ ∘ Subtype.val := by
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact (hj rfl).elim
    · exact Function.update_self ..
  unfold cost root
  dsimp only
  rw [sub_zero]
  erw [hb, ← hg]
  have : Nonempty (Fin (2^n)) := ⟨⟨0, pow_pos (by decide) _⟩⟩
  rw [rawLogPrice_group_diagonal φ σ c]
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  exact mul_comm _ _

end SiteTensor.Relocation.WireNode

end

end SpectralBooks
end LinearAlgebra
end OAI
