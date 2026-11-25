import OAI.Computability.IntegerMultiplication.Packed.Offset

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Dims Code Adic Loom
variable {I : Type} {r : Regime I}
variable (H L i : I→ℕ)
variable (htt : r.Has (fun v => signs (H v) (L v) (i v)))
variable (t : Turn) (hl : t.shift=1 ∨ t.shift = -1)
noncomputable def turnStamp (t : Turn) (v : Raw 2) :=
  if t.shift=(-1) then negative v else v
private theorem easy_turn : Easy (turnStamp t) := by
  unfold turnStamp
  by_cases h : t.shift=-1
  · simp_rw [h,ite_true]; exact easy_negative easy_id
  simp_rw [ite_eq_right h]
  exact easy_id
abbrev Run := fun a:I => Queue (H a) (L a) (i a)
variable (x y : (a:I) → Run H L i a)
variable (e : r.Has fun a=> badge (x a)) (m : r.Has fun a=> badge (y a))
include htt e m

noncomputable section

theorem revealed (t : Turn) (hl : t.shift=1 ∨ t.shift = -1) :
    ∃ v : I→Raw 2, r.Has v ∧ ∀ a,Holds (cap (i a) (H a) (L a)) (v a) (offsets (start t (x a) (y a))) := by
  let v a := unsigned t (signs (H a) (L a) (i a),badge (x a),badge (y a))
  have h : r.Has v := (htt.pair (e.pair m)).thenDo (poly_us _)
  refine ⟨fun a => turnStamp t (v a),h.ez (easy_turn t),fun a=>?_⟩
  obtain ⟨u,g⟩ := weight t (x a) (y a)
  let Z := Omega (H a) (L a) (i a)
  change t.shift*(code (v a):ℤ)=_ at g
  have e : Holds _ (v a) (code (v a):Z) := ⟨u,rfl⟩
  have hh := congrArg (fun i:ℤ => (i:Z)) g
  change ((t.shift*(code (v a):ℤ):ℤ):Z) = ↑(((2^(L a):ℕ):ℤ)*(sumSeq _ _ _ _)) at hh
  dsimp [Z] at hh; push_cast at hh
  rcases hl with h|h
  · simp [turnStamp,h] -- assumption reduces equality?
    unfold offsets; simp [h] at hh; push_cast; rw [← hh]; exact e
  simp only [turnStamp,h,ite_true]

  have t := neg_correct e
  simp [h] at hh
  unfold offsets
  push_cast
  rw [← hh]
  exact t

variable (z : (a:I) → Run H L i a)
include hl t in
theorem ripple (w : r.Has fun a=> badge (z a)) :
    r.Has (fun a => badge (slide (start t (x a) (y a)) (z a))) ∧
      r.Has (fun a => badge ((slide (start t (x a) (y a))).symm (z a))) := by
  obtain ⟨b,h,g⟩ := revealed H L i htt x y e m t hl
  have u (a : I) : Holds (cap (i a) (H a) (L a)) (badge (z a)) (flight (z a)) := Holds.std _
  constructor
  · suffices j : (fun a => badge (slide (start t (x a) (y a)) (z a))) =
        fun a => add 1 1 0 (by decide) (badge (z a),b a) by
      rw [j]
      exact (w.pair h).ez (easy_mix _ _ _ _ easy_id)
    ext a : 1
    apply (Holds.std _).single
    change Holds _ _ (plane _)
    -- plane _ def unfolds to index but rw?
    unfold slide; simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
    change Holds _ _ (plane (z a)+offsets _)
    simpa [flown] using sum 1 1 0 (by decide) (u a) (g a)
  suffices j : (fun a => badge ((slide (start t (x a) (y a))).symm (z a))) =
        fun a => add 1 1 0 (by decide) (badge (z a),negative (b a)) by
    rw [j]
    exact (w.pair (h.ez (easy_negative easy_id))).ez (easy_mix _ _ _ _ easy_id)
  ext a : 1
  apply (Holds.std _).single
  change Holds _ _ (plane _)
  unfold slide
  simp only [Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  change Holds _ _ (plane (z a) + -offsets _)
  simpa [flown,sub_eq_add_neg] using sum 1 1 0 (by decide) (u a) (neg_correct (g a))
end
end Packed

end IntegerMultiplication
end Computability
end OAI
