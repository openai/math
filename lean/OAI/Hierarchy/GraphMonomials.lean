import OAI.Hierarchy.GraphContractions
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace OAI
/-! # Monomials in a graph contraction

Each vertex contributes exactly one variable from its own table. The local
state at the left endpoint of an edge recovers that edge's label. Consequently
every legal global labeling contributes a distinct monomial with coefficient one.
-/

namespace Hierarchy.IncidenceGraph

open MvPolynomial
open scoped Classical

variable (G : IncidenceGraph) {q : ℕ}

/-- The exponent vector of the term contributed by one edge labeling. -/
noncomputable def assignmentExponent (a : G.E → Fin q) : G.TableVar q →₀ ℕ :=
  ∑ v, Finsupp.single (G.tableIndex a v) 1

theorem assignmentExponent_apply (a : G.E → Fin q) (v : G.V) (t : G.Incident v → Fin q) :
    G.assignmentExponent a ⟨v,t⟩ = if (fun e : G.Incident v => a e.val) = t then 1 else 0 := by
  classical
  rw [assignmentExponent,Finsupp.finsetSum_apply,Finset.sum_eq_single v]
  · simp [tableIndex,Finsupp.single_apply]
  · intro u _ hu
    apply Finsupp.single_eq_of_ne
    intro eq
    exact hu (congrArg Sigma.fst eq).symm
  · simp

/-- A monomial contains the local assignment at every vertex, hence all edge labels. -/
theorem assignmentExponent_injective : Function.Injective (G.assignmentExponent (q:=q)) := by
  classical
  intro a b eq
  funext e
  let v := G.left e
  have localEq := congrArg (fun d : G.TableVar q →₀ ℕ => d (G.tableIndex b v)) eq
  have ht : (fun z : G.Incident v => a z.val) = fun z : G.Incident v => b z.val := by
    simpa [tableIndex,assignmentExponent_apply] using localEq
  exact congrFun ht ⟨e,Or.inl rfl⟩

theorem degree_assignmentExponent (a : G.E → Fin q) :
    (G.assignmentExponent a).degree = Fintype.card G.V := by
  classical
  simp [assignmentExponent,Finsupp.degree_single]

variable (R : Type*) [CommSemiring R]

theorem assignmentMonomial_eq_monomial (a : G.E → Fin q) :
    G.assignmentMonomial R a = monomial (G.assignmentExponent a) 1 := by
  classical
  rw [assignmentExponent,monomial_sum_one]
  rfl

theorem assignmentMonomial_injective [Nontrivial R] :
    Function.Injective (G.assignmentMonomial R (q:=q)) := by
  intro a b eq
  rw [assignmentMonomial_eq_monomial,assignmentMonomial_eq_monomial,monomial_eq_monomial_iff] at eq
  exact G.assignmentExponent_injective (by simpa using eq)

theorem coeff_contraction (d : G.TableVar q →₀ ℕ) :
    (G.contraction R q).coeff d = if ∃ a, G.assignmentExponent a = d then 1 else 0 := by
  classical
  simp only [contraction,coeff_sum,assignmentMonomial_eq_monomial,coeff_monomial]
  by_cases hit : ∃ a, G.assignmentExponent a = d
  · obtain ⟨a, rfl⟩ := hit
    have uniq (z : G.E → Fin q) : G.assignmentExponent z = G.assignmentExponent a ↔ z = a :=
      G.assignmentExponent_injective.eq_iff
    simp [uniq]
  · rw [ite_eq_right hit]
    exact Finset.sum_eq_zero (fun z _ => ite_eq_right (fun h => hit ⟨z,h⟩))

@[simp] theorem coeff_assignmentExponent (a : G.E → Fin q) :
    (G.contraction R q).coeff (G.assignmentExponent a) = 1 := by
  rw [coeff_contraction,ite_eq_left ⟨a,rfl⟩]

theorem coeff_contraction_zero_or_one (d : G.TableVar q →₀ ℕ) :
    (G.contraction R q).coeff d = 0 ∨ (G.contraction R q).coeff d = 1 := by
  rw [coeff_contraction]
  split <;> simp

theorem contraction_isHomogeneous :
    (G.contraction R q).IsHomogeneous (Fintype.card G.V) := by
  classical
  apply IsHomogeneous.sum
  intro a _
  rw [assignmentMonomial_eq_monomial]
  exact isHomogeneous_monomial 1 (G.degree_assignmentExponent a)

/-- For each supported monomial the exponents within a single vertex table sum to one. -/
theorem sum_exponents_at_vertex {d : G.TableVar q →₀ ℕ}
    (hd : d ∈ (G.contraction R q).support) (v : G.V) :
    ∑ t : G.Incident v → Fin q, d ⟨v,t⟩ = 1 := by
  classical
  have nz := mem_support_iff.mp hd
  rw [coeff_contraction] at nz
  by_cases h : ∃ a, G.assignmentExponent a = d
  · obtain ⟨a,rfl⟩ := h
    simp [assignmentExponent_apply]
  · exact False.elim (nz (ite_eq_right h))

/-- The empty labeling space can give the zero polynomial. Any single legal
labeling witnesses nonvanishing and gives exact total degree. -/
theorem totalDegree_contraction [Nontrivial R] (a : G.E → Fin q) :
    (G.contraction R q).totalDegree = Fintype.card G.V := by
  apply (G.contraction_isHomogeneous R).totalDegree
  intro h
  have c := G.coeff_assignmentExponent R a
  simp [h] at c

end Hierarchy.IncidenceGraph

end OAI
