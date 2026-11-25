import OAI.Computability.BorderVNP.CrossingIdentity
import OAI.Computability.BorderVNP.BranchSpecializationNumberField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Scalar fields of a finite shortening identity

The local arrays of a fixed shortening use only finitely many constants.
The network identity is a finite collection of integral polynomial relations
in these entries. Thus it descends to their field of definition, and good
reductions of a number-field tuple preserve its original widths and sites.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.PaidIdentity

open MvPolynomial
open scoped Classical BigOperators

variable {D m : ℕ} {K : Type*} [Field K]

/-- A local table address, comprising a term, a site, and the visible bit words. -/
abbrev Entry (e : PaidIdentity K D m) :=
  Σ a : Fin e.count, Σ v : (e.net a).Site,
    (∀ c : {c : (e.net a).Edge // (e.net a).src c = v ∨ (e.net a).dst c = v},
      Fin ((e.net a).width c.val) → Bool) ×
    (∀ _ : {p : Fin D × Bool // (e.net a).attach p = v}, Fin m → Bool)

/-- Look up the old field entry at a local address. -/
def entry (e : PaidIdentity K D m) (i : e.Entry) : K :=
  e.table i.1 i.2.1 i.2.2.1 i.2.2.2

/-- Substitute indeterminates for all local table entries. -/
private noncomputable def symbols (e : PaidIdentity K D m) (a : Fin e.count) :
    (e.net a).Tables (MvPolynomial e.Entry ℤ) :=
  fun v y x => X ⟨a, v, y, x⟩

private theorem eval_symbols (e : PaidIdentity K D m) {L : Type*} [Field L]
    (y : e.Entry → L) (a : Fin e.count) (x : Ports (fun _ : Fin D × Bool => m)) :
    eval₂Hom (Int.castRingHom L) y ((e.net a).value (e.symbols a) x) =
      (e.net a).value (fun v c p => y ⟨a, v, c, p⟩) x := by
  simp only [Network.value, Network.read, symbols, map_sum, map_prod, eval₂Hom_X']

/-- Any tuple preserving the integral relations of the table entries gives an
exact shortening with the same placements, widths and selector cost. -/
noncomputable def specialize {L : Type*} [Field L] (e : PaidIdentity K D m) (y : e.Entry → L)
    (h : ∀ q : MvPolynomial e.Entry ℤ,
      eval₂Hom (Int.castRingHom K) e.entry q = 0 → eval₂Hom (Int.castRingHom L) y q = 0) :
    PaidIdentity L D m where
  count := e.count
  net := e.net
  table a v c p := y ⟨a, v, c, p⟩
  placed := e.placed
  cap := e.cap
  cost_le := e.cost_le
  strict := e.strict
  identity x := by
    let b : ℤ := if ∀ i : Fin D, x (i, false) = x (i, true) then 1 else 0
    have hbK : (Int.castRingHom K) b = antipodalTensor K D m x := by
      simp [b, antipodalTensor, apply_ite]
    have hbL : (Int.castRingHom L) b = antipodalTensor L D m x := by
      simp [b, antipodalTensor, apply_ite]
    let q := C b - ∑ a, (e.net a).value (e.symbols a) x
    have hq : eval₂Hom (Int.castRingHom K) e.entry q = 0 := by
      rw [show q = _ from rfl, map_sub, eval₂Hom_C, map_sum, hbK]
      simp_rw [e.eval_symbols]
      exact sub_eq_zero.mpr (e.identity x)
    have hr := h q hq
    rw [show q = _ from rfl, map_sub, eval₂Hom_C, map_sum, hbL] at hr
    simp_rw [e.eval_symbols] at hr
    exact sub_eq_zero.mp hr

/-- The field generated over the chosen base by the finitely many table entries. -/
noncomputable def entryField (k : Type*) [Field k] [Algebra k K] (e : PaidIdentity K D m) :
    IntermediateField k K := IntermediateField.adjoin k (Set.range e.entry)

/-- For an algebraic extension, the field of the local tables has finite degree. -/
theorem finite_entryField (k : Type*) [Field k] [Algebra k K] [Algebra.IsAlgebraic k K]
    (e : PaidIdentity K D m) : FiniteDimensional k (e.entryField k) :=
  IntermediateField.finiteDimensional_adjoin
    (fun z _ => Algebra.IsIntegral.isIntegral (R := k) z)

/-- The exact finite identity is already defined over its field of entries. -/
noncomputable def descend (k : Type*) [Field k] [Algebra k K] (e : PaidIdentity K D m) :
    PaidIdentity (e.entryField k) D m := by
  let y (i : e.Entry) : e.entryField k :=
    ⟨e.entry i, IntermediateField.subset_adjoin k _ (Set.mem_range_self i)⟩
  refine e.specialize y fun q hq => ?_
  apply Subtype.val_injective
  let f := (e.entryField k).subtype
  change f (eval₂Hom (Int.castRingHom _) y q) = f 0
  rw [map_zero, map_eval₂Hom]
  exact hq

/-- In positive characteristic all the shortening entries lie in one finite field. -/
theorem finiteField_identity (k : Type*) [Field k] [Finite k] [Algebra k K]
    [Algebra.IsAlgebraic k K] (e : PaidIdentity K D m) :
    Finite (e.entryField k) ∧ Nonempty (PaidIdentity (e.entryField k) D m) := by
  let := e.finite_entryField k
  exact ⟨Module.finite_of_finite k, ⟨e.descend k⟩⟩

universe u

/-- For a fixed characteristic-zero shortening, all but finitely many rational
primes admit an exact shortening on the same terminal dimensions over a finite
field whose degree is bounded independently of the prime. -/
theorem goodReduction {K : Type u} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    (e : PaidIdentity K D m) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ B : ℕ, ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ d →
      ∃ (E : Type u) (_ : Field E) (_ : CharP E p) (_ : Finite E),
        Nat.card E ≤ p ^ B ∧ Nonempty (PaidIdentity E D m) := by
  let F := e.entryField ℚ
  let : FiniteDimensional ℚ F := e.finite_entryField ℚ
  let : NumberField F := {}
  let f := e.descend ℚ
  obtain ⟨d, hd, hr⟩ := Specialization.exists_good_reduction F f.entry ∅ (by simp)
  refine ⟨d, hd, Module.finrank ℚ F, ?_⟩
  intro p hp hpd
  obtain ⟨E, _, _, _, y, hcard, hrel, _⟩ := hr p hp hpd
  exact ⟨E, inferInstance, inferInstance, inferInstance, hcard, ⟨f.specialize y hrel⟩⟩

end Crossing.PaidIdentity

end BorderVNP
end Computability
end OAI
