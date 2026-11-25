import OAI.LinearAlgebra.MatrixExponent.Spectral.Place

/-!
# Closing sites in the presence of additional trivial legs

A closure uses one covector on each removed leg. An additional site
with a trivial source leg remains trivial until the final restriction.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral

variable {K S U V : Type} [Field K] [Fintype S] [Fintype U] [Fintype V]

namespace Raw

/-- Insert trivial legs in the middle, preserving the last set of legs. -/
def extra (V : Type) (A : Raw K (S ⊕ U)) : Raw K ((S ⊕ V) ⊕ U) where
  leg := Sum.elim (Sum.elim (fun s => A.leg (.inl s)) (fun _ => Unit)) (fun u => A.leg (.inr u))
  fleg := Sum.rec (Sum.rec (fun s => A.fleg (.inl s)) (fun _ => inferInstanceAs (Fintype Unit)))
    (fun u => A.fleg (.inr u))
  term := A.term
  factor i := Sum.rec (Sum.rec (fun s => A.factor i (.inl s)) (fun _ _ => 1))
    (fun u => A.factor i (.inr u))

private theorem coeff_extra (A : Raw K (S ⊕ U)) (x : ∀ s, (extra V A).leg s) :
    (extra V A).coeff x =
      A.coeff (Sum.rec (fun s => x (.inl (.inl s))) (fun u => x (.inr u))) := by
  simp only [coeff, Fintype.prod_sum_type]
  change (∑ i : A.term, ((∏ s, A.factor i (.inl s) (x (.inl (.inl s)))) * ∏ _ : V, (1 : K)) *
    ∏ u, A.factor i (.inr u) (x (.inr u))) = _
  simp only [Finset.prod_const_one, mul_one]

theorem group_extra {O : Subring K} [DecidableEq S] [DecidableEq U] [DecidableEq V] (A : Raw K (S ⊕ U)) :
    (Valued.equiv O).r (A.group (Sum.map (Sum.inl : S → S ⊕ V) id)) (extra V A) := by
  let f : S ⊕ U → (S ⊕ V) ⊕ U := Sum.map Sum.inl id
  let E := extra V A
  let F (s : (S ⊕ V) ⊕ U) (x : E.leg s) : (A.group f).leg s :=
    fun t => match t with
      | ⟨.inl _, h⟩ => cast (congrArg E.leg h.symm) x
      | ⟨.inr _, h⟩ => cast (congrArg E.leg h.symm) x
  let G (s : (S ⊕ V) ⊕ U) : (A.group f).leg s → E.leg s :=
    match s with
    | .inl (.inl a) => fun x => x ⟨.inl a, rfl⟩
    | .inl (.inr _) => fun _ => ()
    | .inr u => fun x => x ⟨.inr u, rfl⟩
  constructor
  · refine .pullback F fun x => ?_
    erw [coeff_extra, coeff_group]
    exact congrArg A.coeff (funext fun t => by cases t <;> rfl)
  · refine .pullback G fun x => ?_
    erw [coeff_group, coeff_extra]
    exact congrArg A.coeff (funext fun t => by cases t <;> rfl)

variable [Nonempty S]

private theorem coeff_close (A : Raw K (S ⊕ U)) (v : A.Covectors) (x : ∀ s, (A.close v).leg s) :
    (A.close v).coeff x = ∑ i : A.term, (∏ s, A.factor i (.inl s) (x s)) * A.scalar v i := by
  classical
  change (∑ i : A.term, ∏ s, A.factor i (.inl s) (x s) * weight (A.scalar v i) s) = _
  simp only [Finset.prod_mul_distrib]
  simp [weight]

theorem close_extra {O : Subring K} (A : Raw K (S ⊕ U)) (v : (extra V A).Covectors) :
    (Valued.equiv O).r ((extra V A).close v) (pad V (A.close v)) := by
  refine Valued.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  erw [coeff_close, pad_coeff, coeff_close]
  simp only [Fintype.prod_sum_type]
  change (∑ i : A.term, ((∏ s, A.factor i (.inl s) (x (.inl s))) * ∏ _ : V, (1 : K)) *
    A.scalar v i) = _
  simp only [Finset.prod_const_one, mul_one]
  rfl

end Raw

namespace Tensor

theorem close_extra [Nonempty S] [DecidableEq S] [DecidableEq V] [DecidableEq U]
    {A : Tensor K (S ⊕ U)} {B : Tensor K (S ⊕ V)}
    (h : pad U B ≤ place (Sum.map Sum.inl id) A) :
    ∃ C : Tensor K S, B ≤ pad V C ∧ pad U C ≤ A := by
  revert h
  refine Quotient.inductionOn A fun a h => ?_
  change pad U B ≤ ofRaw (a.group _) at h
  rw [ofRaw_eq (Valued.forget_equiv (Raw.group_extra (O := ⊤) a)), pad_le_ofRaw_iff] at h
  obtain ⟨v, hv⟩ := h
  rw [ofRaw_eq (Valued.forget_equiv (Raw.close_extra (O := ⊤) a v))] at hv
  exact ⟨ofRaw (a.close v), hv, pad_close_le U a v⟩

end Tensor
end OAI.LinearAlgebra.MatrixExponent.Spectral
