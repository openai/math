import OAI.Computability.VPVNP.Circuits
import OAI.Computability.VPVNP.GradedComponents
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Eliminating same-degree dependencies in a circuit

For degrees at least two, every homogeneous piece of a gate lies in the linear span
of products of two positive-degree pieces of circuit nodes. Constants, additions,
subtractions and degree-zero factors can thus be absorbed into the scalar labels
of the graded grammar in Section 8.1 of *VP and VNP differ over every field*.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {R V H : Type*} [CommRing R] {n : ℕ}

private theorem positive_component_C (a : R) {k : ℕ} (hk : k ≠ 0) :
    homogeneousComponent k (C a : MvPolynomial V R) = 0 := by
  simp [homogeneousComponent_of_mem (isHomogeneous_C V a), hk]

/-- The start state, all variable inputs and one state per binary gate. -/
abbrev Circuit.GrammarSlots (V : Type*) (n : ℕ) := Option (V ⊕ Fin n)

/-- Read the polynomial at a grammar slot, returning the circuit output at the start slot, `X
v` at a variable slot, or the computed gate polynomial at a gate slot. -/
noncomputable def Circuit.slotPolynomial (c : Circuit R V n) :
    Circuit.GrammarSlots V n → MvPolynomial V R
  | none => c.polynomial
  | some (.inl v) => X v
  | some (.inr j) => c.program.run C X j

private theorem Ref.read_mem_or_constant {p : Program R V n} (r : Ref R V n)
    (v : H → MvPolynomial V R) (hX : ∀ a, X a ∈ Set.range v)
    (hp : ∀ j, p.run C X j ∈ Set.range v) :
    r.read C X (p.run C X) ∈ Set.range v ∨ ∃ a, r.read C X (p.run C X) = C a := by
  cases r with
  | const a => exact Or.inr ⟨a, rfl⟩
  | var x => exact Or.inl (hX x)
  | gate j => exact Or.inl (hp j)

private theorem Ref.component_mem {p : Program R V n} (r : Ref R V n)
    (M : Submodule R (MvPolynomial V R)) {d : ℕ} (hd : 1 < d)
    (hp : ∀ j, homogeneousComponent d (p.run C X j) ∈ M) :
    homogeneousComponent d (r.read C X (p.run C X)) ∈ M := by
  cases r with
  | const a => simp [Ref.read, positive_component_C a (by omega : d ≠ 0)]
  | var x =>
    rw [Ref.read, homogeneousComponent_of_mem (isHomogeneous_X R x)]
    split
    · omega
    · exact M.zero_mem
  | gate j => exact hp j

private theorem component_product_mem {d : ℕ} (p q : MvPolynomial V R)
    (M : Submodule R (MvPolynomial V R)) (v : H → MvPolynomial V R)
    (hp : homogeneousComponent d p ∈ M) (hq : homogeneousComponent d q ∈ M)
    (hpv : p ∈ Set.range v ∨ ∃ a, p = C a) (hqv : q ∈ Set.range v ∨ ∃ a, q = C a)
    (hprod : ∀ i j a b, 0 < a → 0 < b → a + b = d →
      homogeneousComponent a (v i) * homogeneousComponent b (v j) ∈ M) :
    homogeneousComponent d (p * q) ∈ M := by
  rw [homogeneousComponent_mul]
  apply M.sum_mem
  rintro ⟨a, b⟩ hab
  have hab' : a + b = d := Finset.mem_antidiagonal.mp hab
  by_cases ha : a = 0
  · subst a
    simp only [zero_add] at hab'
    subst b
    simpa only [homogeneousComponent_zero, smul_eq_C_mul] using M.smul_mem (p.coeff 0) hq
  by_cases hb : b = 0
  · subst b
    simp only [add_zero] at hab'
    subst a
    simpa only [homogeneousComponent_zero, smul_eq_C_mul, mul_comm] using M.smul_mem (q.coeff 0) hp
  rcases hpv with ⟨i, rfl⟩ | ⟨x, rfl⟩
  · rcases hqv with ⟨j, rfl⟩ | ⟨y, rfl⟩
    · exact hprod i j a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab'
    · simp [positive_component_C y hb]
  · simp [positive_component_C x ha]

private theorem Program.components_mem (p : Program R V n) (M : Submodule R (MvPolynomial V R))
    (v : H → MvPolynomial V R) {d : ℕ} (hd : 1 < d) (hX : ∀ a, X a ∈ Set.range v)
    (hprod : ∀ i j a b, 0 < a → 0 < b → a + b = d →
      homogeneousComponent a (v i) * homogeneousComponent b (v j) ∈ M)
    (hp : ∀ j, p.run C X j ∈ Set.range v) :
    ∀ j, homogeneousComponent d (p.run C X j) ∈ M := by
  induction p with
  | nil => exact fun j ↦ j.elim0
  | snoc p op a b ih =>
    have hprev : ∀ j, p.run C X j ∈ Set.range v := fun j ↦
      by simpa only [Program.run, Fin.lastCases_castSucc] using hp j.castSucc
    have ha := a.component_mem M hd (ih hprev)
    have hb := b.component_mem M hd (ih hprev)
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [Program.run, Fin.lastCases_last]
      cases op with
      | add => simpa only [BinOp.apply, map_add] using M.add_mem ha hb
      | sub => simpa only [BinOp.apply, map_sub] using M.sub_mem ha hb
      | mul =>
        exact component_product_mem _ _ M v ha hb (a.read_mem_or_constant v hX hprev)
          (b.read_mem_or_constant v hX hprev) hprod
    · simpa only [Program.run, Fin.lastCases_castSucc] using ih hprev i

/-- Every graded state of degree above one is in the span of lower-degree productions,
using the specified slots for this very circuit, including its output slot. -/
theorem Circuit.slot_component_mem (c : Circuit R V n) {d : ℕ} (hd : 1 < d)
    (M : Submodule R (MvPolynomial V R))
    (hprod : ∀ i j a b, 0 < a → 0 < b → a + b = d →
      homogeneousComponent a (c.slotPolynomial i) * homogeneousComponent b (c.slotPolynomial j)
        ∈ M) :
    ∀ h, homogeneousComponent d (c.slotPolynomial h) ∈ M := by
  have hX : ∀ a, X a ∈ Set.range c.slotPolynomial := fun a ↦ ⟨some (.inl a), rfl⟩
  have hp : ∀ j, c.program.run C X j ∈ Set.range c.slotPolynomial :=
    fun j ↦ ⟨some (.inr j), rfl⟩
  have hgate := c.program.components_mem M c.slotPolynomial hd hX hprod hp
  rintro (_ | (a | j))
  · exact c.output.component_mem M hd hgate
  · exact (Ref.var a : Ref R V n).component_mem M hd hgate
  · exact hgate j

end VPVNP
end Computability
end OAI
