import OAI.Computability.VPVNP.CircuitSize

/-!
# Shared circuit substitution

If one arithmetic program supplies all the input polynomials of a second program, the
two gate lists can be concatenated. A wire used several times always selects the same
gate in the first list. The bound is the sum of the two sizes, regardless of fan-out.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open VPVNP MvPolynomial

variable {R σ τ : Type*} {m n : ℕ}

private def spliceRef (a : σ → Ref R τ m) : Ref R σ n → Ref R τ (m + n)
  | .const r => .const r
  | .var i => (a i).reindex (Fin.castAdd n)
  | .gate i => .gate (Fin.natAdd m i)

private def spliceProgram (P : Program R τ m) (a : σ → Ref R τ m) :
    {n : ℕ} → Program R σ n → Program R τ (m + n)
  | _, .nil => P
  | _, .snoc Q op i j => .snoc (spliceProgram P a Q) op (spliceRef a i) (spliceRef a j)

private theorem splice_left {A : Type*} [Ring A] (P : Program R τ m) (a : σ → Ref R τ m)
    (Q : Program R σ n) (s : R → A) (x : τ → A) :
    (spliceProgram P a Q).run s x ∘ Fin.castAdd n = P.run s x := by
  funext i
  induction Q with
  | nil => rfl
  | snoc Q op l r ih =>
    simp only [Function.comp_apply, spliceProgram, Program.run, ← Fin.castSucc_castAdd,
      Fin.lastCases_castSucc]
    exact ih

private theorem read_splice {A : Type*} (a : σ → Ref R τ m) (r : Ref R σ n)
    (s : R → A) (x : τ → A) (w : Fin (m + n) → A) :
    (spliceRef a r).read s x w =
      r.read s (fun i => (a i).read s x (w ∘ Fin.castAdd n)) (w ∘ Fin.natAdd m) := by
  cases r with
  | var i => cases h : a i <;> simp [spliceRef, Ref.reindex, h, Ref.read]
  | const | gate => rfl

private theorem splice_right {A : Type*} [Ring A] (P : Program R τ m) (a : σ → Ref R τ m)
    (Q : Program R σ n) (s : R → A) (x : τ → A) :
    (spliceProgram P a Q).run s x ∘ Fin.natAdd m =
      Q.run s (fun i => (a i).read s x (P.run s x)) := by
  induction Q with
  | nil => funext i; exact i.elim0
  | snoc Q op l r ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, spliceProgram, Program.run, Fin.natAdd_last,
        Fin.lastCases_last, read_splice, splice_left, ih]
      exact Fin.lastCases_last
    · simpa only [Function.comp_apply, spliceProgram, Program.run, Fin.natAdd_castSucc,
        Fin.lastCases_castSucc] using congrFun ih j

/-- Substituting outputs of one common arithmetic program costs its gate count only once. -/
theorem circuitSize_aeval_shared [CommRing R] (P : Program R τ m) (a : σ → Ref R τ m)
    (p : MvPolynomial σ R) :
    circuitSize (aeval (fun i => (⟨P, a i⟩ : Circuit R τ m).polynomial) p) ≤
      m + circuitSize p := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  let D : Circuit R τ (m + circuitSize p) :=
    ⟨spliceProgram P a c.program, spliceRef a c.output⟩
  have hD : D.polynomial = c.eval C (fun i => (⟨P, a i⟩ : Circuit R τ m).polynomial) := by
    simp only [D, Circuit.polynomial, Circuit.eval, read_splice, splice_left, splice_right]
  have eval_subst (A : σ → MvPolynomial τ R) : aeval A c.polynomial = c.eval C A := by
    change (aeval A).toRingHom (c.eval C X) = _
    rw [Circuit.eval_hom]
    congr 1 <;> funext i <;> simp
  conv_lhs => rw [← hc, eval_subst, ← hD]
  exact circuitSize_le_of_circuit D

end BorderVNP
end Computability
end OAI
