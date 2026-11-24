import OAI.Computability.VPVNP.Circuits

/-! # Composition of exact arithmetic circuits

Concatenating two topologically ordered programs preserves their internal wires. A final
binary gate then computes the chosen operation on the two designated outputs.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {R σ A : Type*} {n m : ℕ}

/-- Renumber the gate references while preserving scalar and variable inputs. -/
def Ref.reindex (f : Fin n → Fin m) : Ref R σ n → Ref R σ m
  | .var x => .var x
  | .const r => .const r
  | .gate i => .gate (f i)

private theorem Ref.read_reindex (f : Fin n → Fin m) (s : R → A) (x : σ → A)
    (w : Fin m → A) (r : Ref R σ n) :
    (r.reindex f).read s x w = r.read s x (w ∘ f) := by cases r <;> rfl

/-- Append the gates of the second program after those of the first program. -/
def Program.append (p : Program R σ n) : {m : ℕ} → Program R σ m → Program R σ (n + m)
  | _, .nil => p
  | _, .snoc q op a b =>
    .snoc (p.append q) op (a.reindex (Fin.natAdd n)) (b.reindex (Fin.natAdd n))

private theorem Program.run_append_left [Ring A] (s : R → A) (x : σ → A)
    (p : Program R σ n) (q : Program R σ m) :
    (p.append q).run s x ∘ Fin.castAdd m = p.run s x := by
  funext i
  induction q with
  | nil => rfl
  | snoc q op a b ih =>
    simp only [Function.comp_apply, Program.append, Program.run, ← Fin.castSucc_castAdd,
      Fin.lastCases_castSucc]
    exact ih

private theorem Program.run_append_right [Ring A] (s : R → A) (x : σ → A)
    (p : Program R σ n) (q : Program R σ m) :
    (p.append q).run s x ∘ Fin.natAdd n = q.run s x := by
  induction q with
  | nil => funext i; exact i.elim0
  | snoc q op a b ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, Program.append, Program.run, Fin.natAdd_last,
        Fin.lastCases_last, Ref.read_reindex, ih]
      exact Fin.lastCases_last
    · simpa only [Function.comp_apply, Program.append, Program.run, Fin.natAdd_castSucc,
        Fin.lastCases_castSucc] using congrFun ih j

/-- Combine the outputs of two circuits using one additional binary gate. -/
def Circuit.combine (op : BinOp) (c : Circuit R σ n) (d : Circuit R σ m) :
    Circuit R σ (n + m + 1) where
  program := .snoc (c.program.append d.program) op
    (c.output.reindex (Fin.castAdd m)) (d.output.reindex (Fin.natAdd n))
  output := .gate (Fin.last (n + m))

theorem Circuit.eval_combine [Ring A] (op : BinOp) (c : Circuit R σ n)
    (d : Circuit R σ m) (s : R → A) (x : σ → A) :
    (Circuit.combine op c d).eval s x = op.apply (c.eval s x) (d.eval s x) := by
  change Program.run s x (.snoc (c.program.append d.program) op _ _) (Fin.last _) = _
  simp only [Program.run, Fin.lastCases_last, Ref.read_reindex, Program.run_append_left,
    Program.run_append_right, Circuit.eval]

theorem Circuit.polynomial_combine [CommRing R] (op : BinOp) (c : Circuit R σ n)
    (d : Circuit R σ m) :
    (Circuit.combine op c d).polynomial = op.apply c.polynomial d.polynomial :=
  Circuit.eval_combine op c d MvPolynomial.C MvPolynomial.X

end VPVNP
end Computability
end OAI
