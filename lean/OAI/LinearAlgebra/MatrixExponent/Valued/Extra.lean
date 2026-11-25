import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import OAI.LinearAlgebra.MatrixExponent.Valued.Uniform
import OAI.LinearAlgebra.MatrixExponent.Spectral.Extra

/-! # Transport of valued prices by wires over the base field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {K S T E : Type} [Field K] [Field E] [Algebra E K] {O : Subring K}
  [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T] (hO : constants E K ≤ O)

theorem transport (A : Raw K T) (f g : T → S) :
    place g (ofRaw A) ≤ place f (ofRaw A) * ∏ t, wire hO (f t) (g t) (Fintype.card (A.leg t)) := by
  refine Tensor.move_all (fun f => place f (ofRaw A))
    (fun t i j => wire hO i j (Fintype.card (A.leg t))) mul_le_mul_left ?_ f g
  intro v w t h
  rw [wire_ofRaw]
  exact Raw.integral_move A v w t h

variable [Nonempty T] (p : ITensor O S →+* ℝ) (hp : Monotone p)
include hp

theorem price_place_pos (f : T → S) {A : ITensor O T} (h : A ≠ 0) : 0 < p (place f A) := by
  let _ : Nonempty S := ⟨f (Classical.arbitrary T)⟩
  revert h
  refine Quotient.inductionOn A fun a ha => ?_
  obtain ⟨x, hx⟩ := not_forall.mp fun he => ha ((ofRaw_eq_zero a).mpr he)
  have h := hp (place_mono f (scalar_coeff a x))
  rw [place_scalar] at h
  exact (positive_scalar p hp _ hx).trans_le h

theorem price_transport (A : Raw K T) (h : ofRaw (O := O) A ≠ 0) (f g : T → S) :
    |Real.log (p (place f (ofRaw A))) - Real.log (p (place g (ofRaw A)))| ≤
      ∑ t, Tensor.dist (p.comp (fromBase hO)) (f t) (g t) * Real.log (Fintype.card (A.leg t)) := by
  have dim (t : T) : 0 < Fintype.card (A.leg t) := by
    obtain ⟨x, _⟩ := not_forall.mp (fun he => h ((ofRaw_eq_zero A).mpr he))
    exact Fintype.card_pos_iff.mpr ⟨x t⟩
  refine Tensor.log_transport (p.comp (fromBase hO)) (hp.comp (fromBase_mono hO))
    (fun v => p (place v (ofRaw A))) _ (fun v => price_place_pos p hp v h) dim ?_ f g
  intro v w
  have H := hp (transport hO A v w)
  rw [p.map_mul, map_prod] at H
  exact H

theorem price_place_eq (f g : T → S) (h : ∀ t, Tensor.dist (p.comp (fromBase hO)) (f t) (g t) = 0)
    (A : ITensor O T) : p (place f A) = p (place g A) := by
  refine Quotient.inductionOn A fun a => ?_
  change p (place f (ofRaw a)) = p (place g (ofRaw a))
  by_cases hz : ofRaw (O := O) a = 0
  · simp only [hz, place_zero]
  have he := price_transport hO p hp a hz f g
  simp only [h, zero_mul, Finset.sum_const_zero, abs_nonpos_iff, sub_eq_zero] at he
  exact Real.log_injOn_pos (price_place_pos p hp f hz) (price_place_pos p hp g hz) he

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! # Integral closures in the presence of additional trivial sites -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {K S U V : Type} [Field K] {O : Subring K} [Fintype S] [Fintype U] [Fintype V]

theorem close_extra [Nonempty S] [DecidableEq S] [DecidableEq V] [DecidableEq U]
    {A : ITensor O (S ⊕ U)} {B : ITensor O (S ⊕ V)}
    (h : pad U B ≤ place (Sum.map Sum.inl id) A) :
    ∃ C : ITensor O S, B ≤ pad V C ∧ pad U C ≤ A := by
  revert h
  refine Quotient.inductionOn A fun a h => ?_
  change pad U B ≤ ofRaw (a.group _) at h
  rw [ofRaw_eq (Raw.group_extra a), pad_le_ofRaw_iff] at h
  obtain ⟨v, hi, hv⟩ := h
  rw [ofRaw_eq (Raw.close_extra a v)] at hv
  exact ⟨ofRaw (a.close v), hv, pad_close_le U a v hi⟩

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end
