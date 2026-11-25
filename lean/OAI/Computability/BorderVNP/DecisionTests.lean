import OAI.Computability.VPVNP.ProjectionClosure

/-! # Prenex algebraic tests with unrestricted Boolean combinations

Each quantifier block binds one tuple over the entire coefficient field.
An atomic test evaluates a division-free circuit at a point and asks whether
the result is zero. Size counts its distinct inputs, including constants, and
its binary gates. Only the largest individual test size enters the bounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision

open VPVNP
open scoped Classical

universe u
variable {K : Type u} [Field K] {I J : Type}

/-- List the inputs read directly by a reference, omitting internal gates. -/
def inputOf {s : ℕ} : Ref K I s → List (I ⊕ K)
  | .var i => [.inl i]
  | .const k => [.inr k]
  | .gate _ => []

/-- All input occurrences in the two operand slots of every binary gate. -/
def programInputs : {s : ℕ} → Program K I s → List (I ⊕ K)
  | _, .nil => []
  | _, .snoc p _ a b => programInputs p ++ inputOf a ++ inputOf b

/-- Binary gates plus distinct scalar and variable input nodes of an atomic test. -/
noncomputable def testSize {s : ℕ} (c : Circuit K I s) : ℕ :=
  s + (programInputs c.program ++ inputOf c.output).toFinset.card

omit [Field K] in
private theorem inputOf_subst {s : ℕ} (r : Ref K I s) (φ : Projection K I J) :
    inputOf (r.subst φ id) = (inputOf r).map (Sum.elim φ Sum.inr) := by
  cases r with
  | var i => cases hi : φ i <;> simp [Ref.subst, inputOf, hi]
  | const | gate => rfl

omit [Field K] in
private theorem programInputs_subst {s : ℕ} (p : Program K I s) (φ : Projection K I J) :
    programInputs (p.subst φ id) = (programInputs p).map (Sum.elim φ Sum.inr) := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp [Program.subst, programInputs, ih, inputOf_subst]

omit [Field K] in
/-- Substituting variables or constants can only identify input nodes. -/
theorem testSize_subst_le {s : ℕ} (c : Circuit K I s) (φ : Projection K I J) :
    testSize (c.subst φ id) ≤ testSize c := by
  classical
  simp only [testSize, Circuit.subst, programInputs_subst, inputOf_subst, ← List.map_append,
    Nat.add_le_add_iff_left]
  have hmap (l : List (I ⊕ K)) :
      (l.map (Sum.elim φ Sum.inr)).toFinset = l.toFinset.image (Sum.elim φ Sum.inr) := by
    ext i
    simp
  rw [hmap]
  exact Finset.card_image_le

/-- Finite Boolean combinations of circuit zero tests. No bound is imposed on
the number of occurrences of atomic tests. -/
inductive BooleanTests (K : Type u) (I : Type) where
  | zero {s : ℕ} (c : Circuit K I s)
  | neg (a : BooleanTests K I)
  | conj (a b : BooleanTests K I)
  | disj (a b : BooleanTests K I)

/-- Truth of a Boolean combination at an assignment of its free coordinates. -/
def BooleanTests.Holds : BooleanTests K I → (I → K) → Prop
  | .zero c, x => c.eval id x = 0
  | .neg a, x => ¬ a.Holds x
  | .conj a b, x => a.Holds x ∧ b.Holds x
  | .disj a b, x => a.Holds x ∨ b.Holds x

/-- The largest individual circuit size. -/
noncomputable def BooleanTests.maxTest : BooleanTests K I → ℕ
  | .zero c => testSize c
  | .neg a => a.maxTest
  | .conj a b | .disj a b => max a.maxTest b.maxTest

/-- Substitution of the free variables inside the atomic test circuits. -/
def BooleanTests.pull (φ : Projection K I J) : BooleanTests K I → BooleanTests K J
  | .zero c => .zero (c.subst φ id)
  | .neg a => .neg (a.pull φ)
  | .conj a b => .conj (a.pull φ) (b.pull φ)
  | .disj a b => .disj (a.pull φ) (b.pull φ)

/-- The pulled-back Boolean combination describes the set-theoretic inverse image. -/
theorem BooleanTests.holds_pull (a : BooleanTests K I) (φ : Projection K I J) (x : J → K) :
    (a.pull φ).Holds x ↔ a.Holds (fun i => (φ i).elim x id) := by
  induction a with
  | zero c => simp only [pull, Holds, Circuit.eval_subst, Function.comp_id]
  | neg a ih => exact not_congr ih
  | conj a b ih ih' => exact and_congr ih ih'
  | disj a b ih ih' => exact or_congr ih ih'

omit [Field K] in
/-- A pullback cannot increase the maximum atomic cost. -/
theorem BooleanTests.maxTest_pull_le (a : BooleanTests K I) (φ : Projection K I J) :
    (a.pull φ).maxTest ≤ a.maxTest := by
  induction a with
  | zero c => exact testSize_subst_le c φ
  | neg a ih => exact ih
  | conj a b ih ih' | disj a b ih ih' => exact max_le_max ih ih'

/-- A prenex prefix followed by a finite Boolean combination of tests. -/
inductive Prenex (K : Type u) : Type → Type (max u 1) where
  | body {I : Type} (tests : BooleanTests K I) : Prenex K I
  | ex {I : Type} (a : ℕ) (next : Prenex K (I ⊕ Fin a)) : Prenex K I
  | all {I : Type} (a : ℕ) (next : Prenex K (I ⊕ Fin a)) : Prenex K I

/-- Semantics of a formula with tuple quantification over the full field. -/
def Prenex.Holds : {I : Type} → Prenex K I → (I → K) → Prop
  | _, .body a, x => a.Holds x
  | _, .ex a f, x => ∃ t : Fin a → K, f.Holds (Sum.elim x t)
  | _, .all a f, x => ∀ t : Fin a → K, f.Holds (Sum.elim x t)

/-- Number of tuple quantifiers in the prefix. -/
def Prenex.blocks : {I : Type} → Prenex K I → ℕ
  | _, .body _ => 0
  | _, .ex _ f | _, .all _ f => f.blocks + 1

/-- Total number of bound field variables. -/
def Prenex.boundVars : {I : Type} → Prenex K I → ℕ
  | _, .body _ => 0
  | _, .ex a f | _, .all a f => a + f.boundVars

/-- Maximum size of an individual atomic test in the Boolean matrix. -/
noncomputable def Prenex.maxTest : {I : Type} → Prenex K I → ℕ
  | _, .body a => a.maxTest
  | _, .ex _ f | _, .all _ f => f.maxTest

/-- Complement a formula by dualizing its quantifiers and negating the matrix. -/
def Prenex.dual : {I : Type} → Prenex K I → Prenex K I
  | _, .body a => .body (.neg a)
  | _, .ex a f => .all a f.dual
  | _, .all a f => .ex a f.dual

/-- Dualization complements the defined set. -/
theorem Prenex.holds_dual (f : Prenex K I) (x : I → K) : f.dual.Holds x ↔ ¬ f.Holds x := by
  induction f with
  | body a => rfl
  | ex a f ih => simp only [dual, Holds, ih, not_exists]
  | all a f ih => simp only [dual, Holds, ih, not_forall]

omit [Field K] in
/-- The three resources monitored in Section 15 are preserved by negation. -/
theorem Prenex.resources_dual (f : Prenex K I) :
    f.dual.blocks = f.blocks ∧ f.dual.boundVars = f.boundVars ∧ f.dual.maxTest = f.maxTest := by
  induction f with
  | body => exact ⟨rfl, rfl, rfl⟩
  | ex a f ih | all a f ih => simp [dual, blocks, boundVars, maxTest, ih.1, ih.2.1, ih.2.2]

/-- Pull back only the free coordinates, preserving each tuple of quantified variables. -/
def Prenex.pull : {I J : Type} → Prenex K I → Projection K I J → Prenex K J
  | _, _, .body a, φ => .body (a.pull φ)
  | _, _, .ex a f, φ => .ex a (f.pull φ.withWitness)
  | _, _, .all a f, φ => .all a (f.pull φ.withWitness)

omit [Field K] in
private theorem assignment_withWitness {a : ℕ} (φ : Projection K I J) (x : J → K) (t : Fin a → K) :
    (fun i => (φ.withWitness i).elim (Sum.elim x t) id) =
      Sum.elim (fun i => (φ i).elim x id) t := by
  funext i
  rcases i with i | j
  · cases h : φ i <;> simp [Projection.withWitness, h]
  · rfl

/-- Prenex formulas commute with arbitrary variable-or-scalar pullbacks. -/
theorem Prenex.holds_pull (f : Prenex K I) (φ : Projection K I J) (x : J → K) :
    (f.pull φ).Holds x ↔ f.Holds (fun i => (φ i).elim x id) := by
  induction f generalizing J with
  | body a => exact a.holds_pull φ x
  | ex a f ih => simp only [pull, Holds, ih, assignment_withWitness]
  | all a f ih => simp only [pull, Holds, ih, assignment_withWitness]

omit [Field K] in
/-- Pullback retains the prefix and its variable count and cannot increase atomic cost. -/
theorem Prenex.resources_pull (f : Prenex K I) (φ : Projection K I J) :
    (f.pull φ).blocks = f.blocks ∧ (f.pull φ).boundVars = f.boundVars ∧
      (f.pull φ).maxTest ≤ f.maxTest := by
  induction f generalizing J with
  | body a => exact ⟨rfl, rfl, a.maxTest_pull_le φ⟩
  | ex a f ih | all a f ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih φ.withWitness
    simp only [pull, blocks, boundVars, maxTest, h₁, h₂, h₃, and_self]

end Decision

end BorderVNP
end Computability
end OAI
