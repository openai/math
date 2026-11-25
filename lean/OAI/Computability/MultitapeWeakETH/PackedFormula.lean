import OAI.Computability.MultitapeWeakETH.FormulaLanes

/-! # Realization of the formula count on a state of the iterated compressor -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT NearSquareRoot.Benes VPVNP VPVNP.Compression
open PackedSwitches Finset
open scoped Classical
noncomputable section

private def stages (d : ℕ) (hd : 1 ≤ d) (i : Fin (2*d-2+2)) : Bool × ℕ :=
  (executionOrder d)[i.val]'(by rw [executionOrder_length]; omega)

private theorem stages_order (d : ℕ) (hd : 1 ≤ d) : List.ofFn (stages d hd) = executionOrder d := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hi'
    simp only [List.getElem_ofFn,stages]

private theorem sum_instances {J R : Type} [AddCommMonoid R] {a b : Fintype J}
    {f g : J → R} (h : ∀ j, f j = g j) :
    (@Finset.univ J a).sum f = (@Finset.univ J b).sum g := by
  cases Subsingleton.elim a b
  exact sum_congr rfl fun j _ => h j

/-- The input state depends only on degree and width parameters. For a given
volume cutoff the same slot graph serves every formula. -/
def inputState (a g r : ℕ) : State a g :=
  state (stages (g+(r+2)) (by omega)) a g (r+2)

/-- The initial factors use the switch table supplied by the caller. -/
def inputFactors {n a g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r))
    (width : SAT.WidthAtMost 3 F) (ha : 2 ≤ 2^a) (table : RawTable) (R : Type) [CommSemiring R] :
    NetworkKernel.Factors R (inputState a g r).network :=
  factors (stages (g+(r+2)) (by omega)) table ha (validator F fit width R)

set_option maxHeartbeats 1200000 in
/-- Every width-three formula fitting in the available site addresses has a
packed, bounded-width realization at the required base degree. The position
and width bounds do not depend on its literal incidence pattern. -/
theorem packed_formula_with {n a g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r))
    (width : SAT.WidthAtMost 3 F) (ha : 2 ≤ 2^a) (table : RawTable)
    (repr : RawRepresents (exchange F fit width) table) :
    let X := inputState a g r
    X.positions = (2*(g+(r+2)))*2^g ∧ X.maxWireWidth ≤ 2^(r+2) ∧
      ∀ (R : Type) [CommSemiring R], let A := inputFactors (g:=g) (r:=r) F fit width ha table R
        (∀ v b, A v b = 0 ∨ A v b = 1) ∧ NetworkKernel.contract X.network A = (SAT.count F : R) := by
  let d := g+(r+2)
  have hd : 1 ≤ d := by dsimp [d]; omega
  let s := stages d hd
  let X := state s a g (r+2)
  refine ⟨?_,width_bound s a g (r+2),?_⟩
  · change X.positions = _
    rw [show X.positions = _ from positions s a g (r+2)]
    have : 2*d-2+2 = 2*d := by omega
    rw [this]
  intro R _
  let A := factors s table ha (validator F fit width R)
  change (∀ v b, A v b = 0 ∨ A v b = 1) ∧ NetworkKernel.contract X.network A = _
  constructor
  · intro v b
    unfold A factors validator
    split <;> try exact Or.inl rfl
    split <;> try exact Or.inr rfl
    dsimp only
    split <;> try exact Or.inl rfl
    by_cases h : ∀ u, siteLane F fit u = v.2 →
        localOK F u (fun e _ => emit s table ha v b (portOffset F fit width (.inl e)),
          fun e _ => receive s table ha v b (portOffset F fit width (.inr e)))
    · right
      apply prod_eq_one
      intro u _
      split_ifs with eq
      · exact ite_eq_left (h u eq)
      · rfl
    · left
      obtain ⟨u,hu⟩ := not_forall.mp h
      have ⟨eq,bad⟩ := Classical.not_imp.mp hu
      apply prod_eq_zero (mem_univ u)
      rw [ite_eq_left eq]
      exact ite_eq_right bad
  · rw [show NetworkKernel.contract X.network A = _ from contract_state s table ha _]
    have perm : SwitchFlow.finish (switchAt (g:=g) (l:=r+2) s table) = exchange F fit width := by
      ext x : 1
      exact SwitchFlow.finish_benes table _ repr s (stages_order d hd) x
    rw [perm]
    apply Eq.trans _ (routed_count (R:=R) F (addresses F fit width) (exchange F fit width) (fun e =>
      Equiv.Perm.viaEmbedding_apply (Equiv.sumComm (Wire F) (Wire F)) (addresses F fit width) (.inl e)))
    exact sum_instances (J := Word (g+(r+2)) → Bool) (fun x =>
      validator_product (g:=g) (r:=r) F fit width R x (x ∘ (exchange F fit width).symm))

theorem packed_formula_on {n a g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r))
    (width : SAT.WidthAtMost 3 F) (ha : 2 ≤ 2^a) :
    let X := inputState a g r
    X.positions = (2*(g+(r+2)))*2^g ∧ X.maxWireWidth ≤ 2^(r+2) ∧
      ∀ (R : Type) [CommSemiring R], ∃ A : NetworkKernel.Factors R X.network,
        (∀ v b, A v b = 0 ∨ A v b = 1) ∧ NetworkKernel.contract X.network A = (SAT.count F : R) := by
  obtain ⟨table,repr,_⟩ := route_ends F fit width
  obtain ⟨pos,w,h⟩ := packed_formula_with (g:=g) (r:=r) F fit width ha table repr
  exact ⟨pos,w,fun R _ => ⟨_,h R⟩⟩

theorem packed_formula {n a g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r))
    (width : SAT.WidthAtMost 3 F) (ha : 2 ≤ 2^a) :
    ∃ X : State a g, X.positions = (2*(g+(r+2)))*2^g ∧ X.maxWireWidth ≤ 2^(r+2) ∧
      ∀ (R : Type) [CommSemiring R], ∃ A : NetworkKernel.Factors R X.network,
        (∀ v b, A v b = 0 ∨ A v b = 1) ∧ NetworkKernel.contract X.network A = (SAT.count F : R) :=
  ⟨inputState a g r,packed_formula_on F fit width ha⟩

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
