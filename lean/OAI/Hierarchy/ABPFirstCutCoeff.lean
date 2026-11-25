import OAI.Hierarchy.Models
import OAI.Hierarchy.GraphMonomials

namespace OAI
/-! # Coefficients of a branching program on selected variable slots

A squarefree monomial chooses one variable in each of a finite set of slots.
An affine edge either preserves this set or supplies the variable in a single slot.
-/

namespace Hierarchy.ABPFirstCut

open MvPolynomial
open scoped BigOperators Classical

noncomputable section

variable {V : Type} {τ : V → Type} {F : Type*} [Field F]

/-- The exponent vector with one selected variable in every slot of `S`. -/
def slotExponent (a : ∀ i, τ i) (S : Finset V) : (Σ i, τ i) →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single ⟨i, a i⟩ 1

/-- The coefficient indexed by an assignment restricted to `S`. -/
def slotCoeff (a : ∀ i, τ i) (S : Finset V) (p : MvPolynomial (Σ i, τ i) F) : F :=
  p.coeff (slotExponent a S)

theorem slotCoeff_congr {a b : ∀ i, τ i} (S : Finset V) (h : ∀ i ∈ S, a i = b i)
    (p : MvPolynomial (Σ i, τ i) F) : slotCoeff a S p = slotCoeff b S p := by
  unfold slotCoeff slotExponent
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

variable [DecidableEq V]

theorem slotExponent_apply (a : ∀ i, τ i) (S : Finset V) (i : V) (t : τ i) :
    slotExponent a S ⟨i,t⟩ = if i ∈ S ∧ a i = t then 1 else 0 := by
  classical
  rw [slotExponent, Finsupp.finsetSum_apply]
  have off (j : V) (h : j ≠ i) : (Finsupp.single (⟨j,a j⟩ : Σ i, τ i) 1 : (Σ i, τ i) →₀ ℕ) ⟨i,t⟩ = 0 := by
    apply Finsupp.single_eq_of_ne
    intro eq
    exact h (congrArg Sigma.fst eq).symm
  by_cases hi : i ∈ S
  · rw [Finset.sum_eq_single i (fun j _ h => off j h) (by simp [hi])]
    simp [hi, Finsupp.single_apply]
  · rw [Finset.sum_eq_zero (fun j hj => off j (fun e => hi (e ▸ hj)))]
    simp [hi]

@[simp] theorem slotExponent_eq_zero_iff (a : ∀ i, τ i) (S : Finset V) :
    slotExponent a S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have eq := DFunLike.congr_fun h ⟨i, a i⟩
    simp [slotExponent_apply, hi] at eq
  · rintro rfl
    simp [slotExponent]

theorem slotExponent_erase_add (a : ∀ i, τ i) (S : Finset V) {i : V} (hi : i ∈ S) :
    slotExponent a (S.erase i) + Finsupp.single ⟨i,a i⟩ 1 = slotExponent a S :=
  Finset.sum_erase_add S _ hi

variable [Fintype V] [∀ i, Fintype (τ i)]

/-- Each affine edge contributes through its constant term or one selected slot. -/
theorem slotCoeff_mul_affine (a : ∀ i, τ i) (S : Finset V)
    (p : MvPolynomial (Σ i, τ i) F) (l : Affine F (Σ i, τ i)) :
    slotCoeff a S (p * l.polynomial) = slotCoeff a S p * l.constant +
      ∑ i ∈ S, slotCoeff a (S.erase i) p * l.coeff ⟨i,a i⟩ := by
  classical
  let tag : V → (Σ i, τ i) := fun i => ⟨i,a i⟩
  have affineTerm (z : Σ i, τ i) : p * (C (l.coeff z) * X z) = C (l.coeff z) * (p * X z) := by
    ac_rfl
  simp only [slotCoeff, Affine.polynomial, mul_add, Finset.mul_sum, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_sum, affineTerm, coeff_C_mul]
  rw [mul_comm p (C l.constant), coeff_C_mul, mul_comm l.constant]
  congr 1
  let f (z : Σ i, τ i) := l.coeff z * (p * X z).coeff (slotExponent a S)
  change (∑ z, f z) = _
  calc
    (∑ z, f z) = ∑ z ∈ S.image tag, f z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      rintro ⟨i,t⟩ _ hz
      have hm : ¬ (i ∈ S ∧ a i = t) := by
        rintro ⟨hi, rfl⟩
        exact hz (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      simp [f, coeff_mul_X', Finsupp.mem_support_iff, slotExponent_apply, hm]
    _ = _ := by
      rw [Finset.sum_image (fun _ _ _ _ eq => congrArg Sigma.fst eq)]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [f, tag]
      rw [← slotExponent_erase_add a S hi, coeff_mul_X, mul_comm]

/-- The source vertex contains only the empty monomial. -/
theorem slotCoeff_source (a : ∀ i, τ i) (S : Finset V) (v : Fin 1) :
    slotCoeff a S ((Rows.source : Rows F (Σ i, τ i) 1).values v) = if S = ∅ then 1 else 0 := by
  classical
  simp [Rows.values, slotCoeff, coeff_one, eq_comm (a := (0 : (Σ i, τ i) →₀ ℕ))]

omit [DecidableEq V] in
/-- Adding a row preserves coefficients at the previous vertices. -/
@[simp] theorem slotCoeff_snoc_castSucc (a : ∀ i, τ i) (S : Finset V) {n : ℕ}
    (g : Rows F (Σ i, τ i) n) (edges : List (Fin n × Affine F (Σ i, τ i))) (v : Fin n) :
    slotCoeff a S ((g.snoc edges).values v.castSucc) = slotCoeff a S (g.values v) := by
  simp [Rows.values]

/-- The new vertex sums the coefficient contributions of all incoming edge occurrences. -/
theorem slotCoeff_snoc_last (a : ∀ i, τ i) (S : Finset V) {n : ℕ}
    (g : Rows F (Σ i, τ i) n) (edges : List (Fin n × Affine F (Σ i, τ i))) :
    slotCoeff a S ((g.snoc edges).values (Fin.last n)) =
      (edges.map fun e => slotCoeff a S (g.values e.1) * e.2.constant +
        ∑ i ∈ S, slotCoeff a (S.erase i) (g.values e.1) * e.2.coeff ⟨i,a i⟩).sum := by
  simp only [Rows.values, Fin.lastCases_last]
  induction edges with
  | nil => simp [slotCoeff]
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons]
    change (g.values e.1 * e.2.polynomial + _).coeff _ = _
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact congrArg₂ (· + ·) (slotCoeff_mul_affine a S (g.values e.1) e.2) ih

/-- Graph-label assignments give the full-slot exponent of the contraction monomial. -/
theorem slotExponent_graph_assignment (G : IncidenceGraph) {q : ℕ} (b : G.E → Fin q) :
    slotExponent (fun (v : G.V) (e : G.Incident v) => b e.val) Finset.univ =
      G.assignmentExponent b := rfl

omit [∀ i, Fintype (τ i)] in
theorem slotExponent_univ_injective :
    Function.Injective (fun a : ∀ i, τ i => slotExponent a Finset.univ) := by
  classical
  intro a b eq
  funext i
  have hi := DFunLike.congr_fun eq ⟨i,b i⟩
  simpa [slotExponent_apply] using hi

/-- The full-slot coefficient records whether the local assignments agree on every edge. -/
theorem slotCoeff_graph_contraction (G : IncidenceGraph) (q : ℕ)
    (a : ∀ v, G.Incident v → Fin q) :
    slotCoeff a Finset.univ (G.contraction F q) =
      if ∃ b : G.E → Fin q, ∀ v (e : G.Incident v), b e.val = a v e then 1 else 0 := by
  classical
  rw [slotCoeff, G.coeff_contraction]
  have heq : (∃ b, G.assignmentExponent b = slotExponent a Finset.univ) ↔
      ∃ b : G.E → Fin q, ∀ v (e : G.Incident v), b e.val = a v e := by
    refine exists_congr fun b => ?_
    rw [← slotExponent_graph_assignment, slotExponent_univ_injective.eq_iff]
    constructor
    · intro h v e
      exact congrFun (congrFun h v) e
    · intro h
      funext v e
      exact h v e
  by_cases h : ∃ b, G.assignmentExponent b = slotExponent a Finset.univ
  · rw [ite_eq_left h, ite_eq_left (heq.mp h)]
  · rw [ite_eq_right h, ite_eq_right (h ∘ heq.mpr)]

end
end Hierarchy.ABPFirstCut

end OAI
