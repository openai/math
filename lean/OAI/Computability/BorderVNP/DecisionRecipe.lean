import OAI.Computability.BorderVNP.Model
import OAI.Computability.BorderVNP.DecisionTests
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The affine recipes of Section 15

A recipe starts from affine space, takes products, chooses irreducible
components of cuts by equations, and takes closures of rational images.
Circuit systems share gates across their outputs. All geometric operations
are on affine points with the Zariski image closure.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision

open VPVNP MvPolynomial
open scoped Classical

universe u
variable {K : Type u} [Field K] {I J : Type}

/-- A family of polynomial outputs computed by one shared straight-line program. -/
structure System (K : Type u) (I O : Type) where
  /-- Number of binary gates. -/
  gates : ℕ
  /-- The program shared by every equation or map coordinate. -/
  program : Program K I gates
  /-- The reference read by each output. -/
  output : O → Ref K I gates

/-- Evaluate all outputs of a circuit system at a point. -/
def System.values {O : Type} (s : System K I O) (x : I → K) (j : O) : K :=
  (Circuit.mk s.program (s.output j)).eval id x

/-- Charge binary gates once, distinct inputs once, and each requested output. -/
noncomputable def System.size {O : Type} [Fintype O] (s : System K I O) : ℕ :=
  s.gates + ((programInputs s.program).toFinset ∪
    Finset.univ.biUnion (fun j => (inputOf (s.output j)).toFinset)).card + Fintype.card O

/-- A polynomial vanishes at every point of a set. -/
def VanishesOn (V : Set (I → K)) (p : MvPolynomial I K) : Prop := ∀ x ∈ V, eval x p = 0

/-- Affine irreducibility, using primality of the vanishing ideal. -/
def Irreducible (V : Set (I → K)) : Prop :=
  V.Nonempty ∧ ∀ p q : MvPolynomial I K, VanishesOn V (p * q) → VanishesOn V p ∨ VanishesOn V q

/-- The polynomial definition agrees with primality of the actual vanishing ideal. -/
theorem irreducible_iff_prime (V : Set (I → K)) :
    Irreducible V ↔ (vanishingIdeal K V).IsPrime := by
  constructor
  · rintro ⟨⟨x, hx⟩, hp⟩
    refine ⟨?_, fun {p q} => hp p q⟩
    intro h
    have h1 : (1 : MvPolynomial I K) ∈ vanishingIdeal K V := h ▸ Submodule.mem_top
    exact one_ne_zero (by simpa using h1 x hx : (1 : K) = 0)
  · intro h
    refine ⟨?_, fun _ _ => h.mem_or_mem⟩
    by_contra! he
    rw [he, vanishingIdeal_empty] at h
    exact h.ne_top rfl

/-- Components are maximal nonempty irreducible closed subsets of the given cut. -/
def IsComponent (C V : Set (I → K)) : Prop :=
  C ⊆ V ∧ imageClosure C = C ∧ Irreducible C ∧
    ∀ D, D ⊆ V → imageClosure D = D → Irreducible D → C ⊆ D → D ⊆ C

/-- A polynomial numerator and denominator for every output, sharing one circuit. -/
abbrev RationalSystem (K : Type u) (I J : Type) := System K I (J ⊕ J)

/-- Common regular domain of a rational map. -/
def rationalDomain (f : RationalSystem K I J) : Set (I → K) :=
  {x | ∀ j, f.values x (.inr j) ≠ 0}

/-- Affine output coordinates on the regular domain. -/
def rationalValue (f : RationalSystem K I J) (x : I → K) (j : J) : K :=
  f.values x (.inl j) / f.values x (.inr j)

/-- A recipe with its precise affine output set and charged construction-tree size.
Free choice of a component appears only at an equation-cut node. -/
inductive Recipe (K : Type u) [Field K] : (I : Type) → Set (I → K) → ℕ → Prop
  | affine (I : Type) [Fintype I] : Recipe K I Set.univ (1 + Fintype.card I)
  | product {I J : Type} [Fintype I] [Fintype J] {V : Set (I → K)} {W : Set (J → K)} {v w : ℕ}
      (left : Recipe K I V v) (right : Recipe K J W w) :
      Recipe K (I ⊕ J) {z | z ∘ Sum.inl ∈ V ∧ z ∘ Sum.inr ∈ W}
        (v + w + 1 + Fintype.card (I ⊕ J))
  | cut {I O : Type} [Fintype I] [Fintype O] {V C : Set (I → K)} {v : ℕ}
      (parent : Recipe K I V v) (eqns : System K I O)
      (component : IsComponent C (V ∩ {x | ∀ j, eqns.values x j = 0})) :
      Recipe K I C (v + 1 + Fintype.card I + eqns.size)
  | image {I J : Type} [Fintype J] {V : Set (I → K)} {v : ℕ}
      (parent : Recipe K I V v) (f : RationalSystem K I J)
      (regular : (V ∩ rationalDomain f).Nonempty) :
      Recipe K J (imageClosure (rationalValue f '' (V ∩ rationalDomain f)))
        (v + 1 + Fintype.card J + f.size)

/-- Each output coordinate of a polynomial map is a formal polynomial in the input coordinates. -/
def polynomialImage (f : J → MvPolynomial I K) : Set (J → K) :=
  Set.range (fun (x : I → K) j => eval x (f j))

/-- Polynomially parametrized sets over an infinite field have irreducible image closure. -/
theorem irreducible_polynomialImage [Infinite K] (f : J → MvPolynomial I K) :
    Irreducible (imageClosure (polynomialImage f)) := by
  have pull (p : MvPolynomial J K) (x : I → K) :
      eval x (eval₂Hom C f p) = eval (fun j => eval x (f j)) p := by
    change eval x (eval₂ C f p) = _
    rw [eval_eval₂, show (eval x).comp C = RingHom.id K by ext; simp, eval₂_id]
  refine ⟨⟨_, subset_imageClosure _ ⟨(fun _ : I => (0 : K)), rfl⟩⟩, ?_⟩
  intro p q hpq
  have hz : eval₂Hom C f (p * q) = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [pull, map_zero]
    exact hpq _ (subset_imageClosure _ ⟨x, rfl⟩)
  rw [map_mul, mul_eq_zero] at hz
  have lift (r : MvPolynomial J K) (hr : eval₂Hom C f r = 0) :
      VanishesOn (imageClosure (polynomialImage f)) r := by
    intro y hy
    apply hy
    rintro _ ⟨x, rfl⟩
    rw [← pull, hr, map_zero]
  exact hz.imp (lift p) (lift q)

/-- The product criterion forces an irreducible set into a single member of
any finite closed cover. No bound on the cardinality of the cover is needed. -/
theorem subset_member_of_finite_closed_cover {V : Set (I → K)} (hirr : Irreducible V)
    (cover : Finset (Set (I → K))) (hclosed : ∀ W ∈ cover, imageClosure W = W)
    (hcover : V ⊆ ⋃₀ (cover : Set (Set (I → K)))) :
    ∃ W ∈ cover, V ⊆ W := by
  classical
  by_contra! hn
  have sep (W : Set (I → K)) (hW : W ∈ cover) :
      ∃ p : MvPolynomial I K, VanishesOn W p ∧ ¬ VanishesOn V p := by
    obtain ⟨x, hx, hxW⟩ := Set.not_subset.mp (hn W hW)
    rw [← hclosed W hW] at hxW
    change ¬ ∀ q : MvPolynomial I K, VanishesOn W q → eval x q = 0 at hxW
    push Not at hxW
    obtain ⟨p, hp, hx'⟩ := hxW
    exact ⟨p, hp, fun h => hx' (h _ hx)⟩
  choose p hp hbad using sep
  let factors (w : cover) := p w.val w.property
  have allzero : VanishesOn V (∏ w : cover, factors w) := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := hcover hx
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨W, hW⟩ : cover)) (hp W hW x hxW)
  have prime := (irreducible_iff_prime V).mp hirr
  change (∏ w : cover, factors w) ∈ vanishingIdeal K V at allzero
  obtain ⟨w, _, hw⟩ := prime.prod_mem_iff.mp allzero
  exact hbad w.val w.property hw

end Decision

end BorderVNP
end Computability
end OAI
