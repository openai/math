import OAI.Computability.VPVNP.CircuitSize

namespace OAI
/-! # Extending a straight-line program by a weighted sum of stored values -/

namespace Hierarchy.CircuitBuilder

open Computability.VPVNP

variable {F σ : Type*} [CommRing F] {n m : ℕ}

private theorem snoc_keeps (p : Program F σ n) (op : BinOp) (a b r : Ref F σ n) :
    (Circuit.mk (p.snoc op a b) (r.reindex Fin.castSucc)).polynomial =
      (Circuit.mk p r).polynomial := by
  cases r with
  | const => rfl
  | var => rfl
  | gate i =>
    simp [Circuit.polynomial, Circuit.eval, Ref.reindex, Ref.read, Program.run]

private theorem append_keeps (p : Program F σ n) (q : Program F σ m) (r : Ref F σ n) :
    (Circuit.mk (p.append q) (r.reindex (Fin.castAdd m))).polynomial =
      (Circuit.mk p r).polynomial := by
  cases r with
  | const => rfl
  | var => rfl
  | gate i =>
    change (p.append q).run MvPolynomial.C MvPolynomial.X (Fin.castAdd m i) =
      p.run MvPolynomial.C MvPolynomial.X i
    induction q with
    | nil => rfl
    | snoc q op a b ih =>
      simpa only [Program.append,Program.run,← Fin.castSucc_castAdd,Fin.lastCases_castSucc] using ih

/-- Append a row of predecessor–label products to an existing program. Each
label is computed once and each edge adds one multiplication and one addition.
Every original reference can still be read after the extension. -/
theorem extendPaths (p : Program F σ n) (edges : List (Ref F σ n × MvPolynomial σ F))
    (price : ℕ) (hprice : ∀ e ∈ edges, circuitSize e.2 ≤ price) :
    ∃ m ≤ n + edges.length * (price + 2),
      ∃ (q : Program F σ m) (lift : Ref F σ n → Ref F σ m) (out : Ref F σ m),
        (∀ r, (Circuit.mk q (lift r)).polynomial = (Circuit.mk p r).polynomial) ∧
        (Circuit.mk q out).polynomial =
          (edges.map (fun e => (Circuit.mk p e.1).polynomial * e.2)).sum := by
  induction edges with
  | nil =>
    refine ⟨n, by simp, p, id, .const 0, fun _ => rfl, ?_⟩
    change MvPolynomial.C (0 : F) = 0
    exact map_zero _
  | cons e es ih =>
    have cost := hprice e (.head _)
    obtain ⟨l, bound, q, lift, acc, kept, accumulates⟩ := ih (fun a ha => hprice a (.tail _ ha))
    obtain ⟨label, computes⟩ := circuitSize_spec e.2
    let k := circuitSize e.2
    let term : Circuit F σ (l+k+1) := Circuit.combine .mul ⟨q,lift e.1⟩ label
    let keep (r : Ref F σ l) := (r.reindex (Fin.castAdd k)).reindex Fin.castSucc
    have keep_eq (r : Ref F σ l) :
        (Circuit.mk term.program (keep r)).polynomial = (Circuit.mk q r).polynomial :=
      (snoc_keeps _ _ _ _ _).trans (append_keeps q label.program r)
    have term_eq : term.polynomial = (Circuit.mk p e.1).polynomial * e.2 := by
      change (Circuit.combine .mul (Circuit.mk q (lift e.1)) label).polynomial = _
      rw [Circuit.polynomial_combine, kept, computes]; rfl
    let dest := term.program.snoc .add term.output (keep acc)
    refine ⟨l+k+1+1, ?_, dest, fun r => (keep (lift r)).reindex Fin.castSucc,
      .gate (Fin.last (l+k+1)), ?_, ?_⟩
    · simp only [List.length_cons,Nat.succ_mul]
      dsimp [k]
      omega
    · intro r
      exact (snoc_keeps _ _ _ _ _).trans ((keep_eq (lift r)).trans (kept r))
    · have atLast :
          (Circuit.mk dest (.gate (Fin.last (l+k+1)))).polynomial =
            term.polynomial + (Circuit.mk term.program (keep acc)).polynomial := by
        simp [Circuit.polynomial, Circuit.eval, dest, Ref.read, Program.run, BinOp.apply]
      rw [atLast,term_eq,keep_eq,accumulates]; rfl

end Hierarchy.CircuitBuilder

end OAI
