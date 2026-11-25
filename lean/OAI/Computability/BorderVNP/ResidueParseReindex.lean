import OAI.Computability.BorderVNP.BranchParseFamily

/-!
# Numbering the variables and states of the residue coefficient table

The integral table in the branch argument has numbered input variables. The diagonal
queries use paired variables. Relabeling all terminal and binary productions transports
the entire table, including every nonsquarefree degree-component query.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseTable

open MvPolynomial VPVNP VPVNP.ParseGrammar

variable {V W H J : Type*}

/-- Relabel the variables of a degree-component monomial without changing its degree. -/
noncomputable def degreeEquiv (e : V ≃ W) (d : ℕ) : DegreeMonomial V d ≃ DegreeMonomial W d :=
  (Finsupp.equivCongrLeft e).subtypeEquiv fun a => by
    change a.degree = d ↔ (Finsupp.equivCongrLeft e a).degree = d
    rw [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]

/-- The underlying exponent vector is transported by the same variable map. -/
theorem degreeEquiv_val (e : V ≃ W) {d : ℕ} (μ : DegreeMonomial V d) :
    (degreeEquiv e d μ).val = μ.val.mapDomain e := Finsupp.equivMapDomain_eq_mapDomain e μ.val

/-- Renaming a formal polynomial transports every full degree-component coefficient. -/
theorem coefficient_reindex {K : Type*} [CommSemiring K] (e : V ≃ W) {d : ℕ}
    (P : MvPolynomial V K) (μ : DegreeMonomial V d) :
    (rename e P).coeff (degreeEquiv e d μ).val = P.coeff μ.val := by
  rw [degreeEquiv_val, coeff_rename_mapDomain e e.injective]

/-- Relabel a terminal's variable and state, and the three states of a binary production.
The degree layer and ordered split index are fixed. -/
def labelEquiv (e : V ≃ W) (h : H ≃ J) (n : ℕ) :
    GrammarLabel V H n ≃ GrammarLabel W J n :=
  (h.prodCongr e).sumCongr (Equiv.sigmaCongrRight fun d =>
    h.prodCongr ((Equiv.refl (Fin d.val)).prodCongr (h.prodCongr h)))

variable [Fintype V] [Fintype W] [Fintype H] [Fintype J]

/-- The layer polynomial of the universal grammar is equivariant in the variables and states.
Its coefficient ring is renamed by the induced equivalence of grammar labels. -/
theorem eval_reindex (e : V ≃ W) (h : H ≃ J) {n : ℕ} (d : Fin n) (i : H) :
    (universalGrammar W J n).eval d (h i) = rename e
      (map (rename (R := ℤ) (labelEquiv e h n)).toRingHom ((universalGrammar V H n).eval d i)) := by
  have ht (i : H) (v : V) :
      (rename (R := ℤ) (labelEquiv e h n)).toRingHom ((universalGrammar V H n).terminal i v) =
      (universalGrammar W J n).terminal (h i) (e v) := rename_X _ _
  have hb (d : Fin n) (i : H) (b : Fin d.val) (j k : H) :
      (rename (R := ℤ) (labelEquiv e h n)).toRingHom ((universalGrammar V H n).binary d i b j k) =
      (universalGrammar W J n).binary d (h i) b (h j) (h k) := rename_X _ _
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing i with
  | h d ih =>
    by_cases hd : d.val = 0
    · rw [(universalGrammar W J n).eval_terminal hd, (universalGrammar V H n).eval_terminal hd]
      simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, rename_C, rename_X, ht]
      exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    · rw [(universalGrammar W J n).eval_binary hd, (universalGrammar V H n).eval_binary hd]
      simp only [map_sum, map_mul, MvPolynomial.map_C, rename_C, hb]
      symm
      apply Finset.sum_congr rfl
      intro b _
      apply Fintype.sum_equiv h
      intro j
      apply Fintype.sum_equiv h
      intro k
      rw [← ih (leftDegree d b) (leftDegree_lt d b) j, ← ih (rightDegree d b) (rightDegree_lt d b) k]

/-- The state cast preserves the numerical index of every shared-circuit grammar state. -/
def stateEquiv (e : V ≃ W) (s : ℕ) : State V s ≃ State W s :=
  finCongr (by rw [Fintype.card_congr e])

/-- The state read by the universal coefficient table is preserved. -/
theorem stateEquiv_zero (e : V ≃ W) (s : ℕ) : stateEquiv e s 0 = 0 := rfl

/-- Transport the full degree-component table between any two enumerations of the input
variables, preserving each coefficient as a formal integer polynomial in the production labels. -/
theorem table_reindex (e : V ≃ W) (k s : ℕ) (μ : DegreeMonomial V (k + 1)) :
    table W k s (degreeEquiv e (k + 1) μ) =
      rename (labelEquiv e (stateEquiv e s) (k + 1)) (table V k s μ) := by
  unfold table coordinate
  rw [← stateEquiv_zero e s, eval_reindex e (stateEquiv e s), coefficient_reindex, coeff_map]
  rfl

/-- Row-major numbering of the two variables at each input position. -/
def pairedNumbering (n : ℕ) : (Fin n × Bool) ≃ Fin (2 * n) :=
  ((Equiv.refl (Fin n)).prodCongr finTwoEquiv.symm).trans (finProdFinEquiv.trans
    (finCongr (Nat.mul_comm n 2)))

/-- Carry production labels to the precise numbered chart coordinates used in §9. -/
noncomputable def numberedLabelEquiv {v : ℕ} (e : V ≃ Fin v) (k s : ℕ) :
    GrammarLabel V (State V s) (k + 1) ≃ Fin (Branch.parameterCount v k s) :=
  (labelEquiv e (stateEquiv e s) (k + 1)).trans (Fintype.equivFin _)

/-- The branch's numbered coefficient map is the label renaming of the unnumbered
integral parse table, after extension of its coefficients to the selected field. -/
theorem numberedTable_reindex (K : Type*) [Field K] {v : ℕ} (e : V ≃ Fin v)
    (k s : ℕ) (μ : DegreeMonomial V (k+1)) :
    Branch.numberedTable K v k s (degreeEquiv e (k+1) μ) =
      rename (numberedLabelEquiv e k s) (map (Int.castRingHom K) (table V k s μ)) := by
  rw [Branch.numberedTable, table_reindex e, map_rename, rename_rename]
  rfl

end ParseTable

end BorderVNP
end Computability
end OAI
