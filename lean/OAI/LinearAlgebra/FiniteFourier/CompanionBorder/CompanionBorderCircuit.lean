import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import OAI.Computability.VPVNP.CircuitComposition

/-! # Preserving arithmetic gate counts in the companion circuit model

One companion program holds all the accumulated binary gates. Each register
of the source program names a variable, a scalar, or an already computed gate.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace CompanionBorder

open MatrixMultiplication OAI.LinearAlgebra.SpectralBooks

variable {F σ : Type*} [CommRing F]

private abbrev value {n : ℕ} (q : OAI.Computability.VPVNP.Program F σ n) (v : OAI.Computability.VPVNP.Ref F σ n) :
    MvPolynomial σ F :=
  v.read MvPolynomial.C MvPolynomial.X (q.run MvPolynomial.C MvPolynomial.X)

private theorem value_reindex_snoc {n : ℕ} (q : OAI.Computability.VPVNP.Program F σ n) (op : OAI.Computability.VPVNP.BinOp)
    (a b v : OAI.Computability.VPVNP.Ref F σ n) :
    value (q.snoc op a b) (v.reindex Fin.castSucc) = value q v := by
  cases v <;> simp [value, OAI.Computability.VPVNP.Ref.reindex, OAI.Computability.VPVNP.Ref.read, OAI.Computability.VPVNP.Program.run]

private theorem append_binary {n : ℕ} (p : Arithmetic.Program F σ n)
    (q : OAI.Computability.VPVNP.Program F σ p.cost) (refs : Fin n → OAI.Computability.VPVNP.Ref F σ p.cost)
    (correct : ∀ i, value q (refs i) = registerPolynomial p i)
    (op : OAI.Computability.VPVNP.BinOp) (i j : Fin n) :
    ∃ (Q : OAI.Computability.VPVNP.Program F σ (p.cost+1)) (v : Fin (n+1) → OAI.Computability.VPVNP.Ref F σ (p.cost+1)),
      ∀ k, value Q (v k) =
        Fin.cases (op.apply (registerPolynomial p i) (registerPolynomial p j)) (registerPolynomial p) k := by
  refine ⟨q.snoc op (refs i) (refs j),
    Fin.cases (.gate (Fin.last _)) (fun t => (refs t).reindex Fin.castSucc), ?_⟩
  intro k
  refine Fin.cases ?_ (fun t => ?_) k
  · change (q.snoc op (refs i) (refs j)).run MvPolynomial.C MvPolynomial.X (Fin.last _) = _
    simp only [OAI.Computability.VPVNP.Program.run, Fin.lastCases_last, Fin.cases_zero]
    exact congrArg₂ op.apply (correct i) (correct j)
  · simpa only [Fin.cases_succ, value_reindex_snoc] using correct t

private theorem register_references {n : ℕ} (p : Arithmetic.Program F σ n) :
    ∃ (q : OAI.Computability.VPVNP.Program F σ p.cost) (refs : Fin n → OAI.Computability.VPVNP.Ref F σ p.cost),
      ∀ i, value q (refs i) = registerPolynomial p i := by
  induction p with
  | nil => exact ⟨.nil, Fin.elim0, fun i => i.elim0⟩
  | @step n p g ih =>
    obtain ⟨q, refs, correct⟩ := ih
    cases g with
    | constant a => exact ⟨q, Fin.cases (.const a) refs, fun i => Fin.cases rfl correct i⟩
    | input a => exact ⟨q, Fin.cases (.var a) refs, fun i => Fin.cases rfl correct i⟩
    | add i j => exact append_binary p q refs correct .add i j
    | sub i j => exact append_binary p q refs correct .sub i j
    | mul i j => exact append_binary p q refs correct .mul i j

/-- Any register is the output of a companion circuit with exactly the
original number of binary gates, including when this number is zero. -/
theorem exists_circuit_register {n : ℕ} (p : Arithmetic.Program F σ n) (i : Fin n) :
    ∃ c : OAI.Computability.VPVNP.Circuit F σ p.cost, c.polynomial = registerPolynomial p i := by
  obtain ⟨q, refs, correct⟩ := register_references p
  exact ⟨⟨q, refs i⟩, correct i⟩

end CompanionBorder

end

end FiniteFourier
end LinearAlgebra
end OAI
