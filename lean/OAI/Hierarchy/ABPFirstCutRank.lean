import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI
/-! # Matrix rank at a cut of the slots -/

namespace Hierarchy.ABPFirstCut

open scoped BigOperators

variable {V : Type*} {τ : V → Type*} {F : Type*} [DecidableEq V]

/-- Assignments of variables on the two sides of a cut. -/
abbrev Inside (τ : V → Type*) (U : Finset V) := (i : U) → τ i.val
abbrev Outside (τ : V → Type*) (U : Finset V) := (i : {i : V // i ∉ U}) → τ i.val

def restrictIn (U : Finset V) (a : ∀ i, τ i) : Inside τ U := fun i => a i.val
def restrictOut (U : Finset V) (a : ∀ i, τ i) : Outside τ U := fun i => a i.val

def join (U : Finset V) (x : Inside τ U) (y : Outside τ U) (i : V) : τ i :=
  if hi : i ∈ U then x ⟨i, hi⟩ else y ⟨i, hi⟩

@[simp] theorem restrictIn_join (U : Finset V) (x : Inside τ U) (y : Outside τ U) :
    restrictIn U (join U x y) = x := by
  funext i
  simp [restrictIn, join, i.property]

@[simp] theorem restrictOut_join (U : Finset V) (x : Inside τ U) (y : Outside τ U) :
    restrictOut U (join U x y) = y := by
  funext i
  simp [restrictOut, join, i.property]

/-- Flatten the coefficient tensor with the slots of `U` indexing the rows. -/
def flatten (U : Finset V) (T : (∀ i, τ i) → F) : Matrix (Inside τ U) (Outside τ U) F :=
  fun x y => T (join U x y)

/-- Each allowed cut contributes a sum of products indexed by the cut vertex. -/
def CutFactorization [Semiring F] (family : Finset (Finset V)) (n : ℕ)
    (T : (∀ i, τ i) → F) : Prop :=
  ∃ (L : (U : family) → Fin n → Inside τ U.val → F)
    (R : (U : family) → Fin n → Outside τ U.val → F),
    ∀ a, T a = ∑ U : family, ∑ v : Fin n, L U v (restrictIn U.val a) * R U v (restrictOut U.val a)

/-- A function constant on the fibers of a restriction descends to the partial
assignments. An assignment with no extension receives value zero. -/
private noncomputable def descend {X Y : Type*} [Zero F] (r : X → Y) (f : X → F) (y : Y) : F := by
  classical
  exact if h : ∃ x, r x = y then f h.choose else 0

private theorem descend_apply {X Y : Type*} [Zero F] (r : X → Y) (f : X → F)
    (hf : ∀ a b, r a = r b → f a = f b) (a : X) : descend r f (r a) = f a := by
  classical
  have h : ∃ x, r x = r a := ⟨a, rfl⟩
  rw [descend, dite_eq_left h]
  exact hf _ _ h.choose_spec

omit [DecidableEq V] in
theorem cutFactorization_of_local [Semiring F] (family : Finset (Finset V)) (n : ℕ)
    (T : (∀ i, τ i) → F) (L R : family → Fin n → (∀ i, τ i) → F)
    (hL : ∀ (U : family) (v : Fin n) (a b : ∀ i, τ i),
      (∀ i ∈ U.val, a i = b i) → L U v a = L U v b)
    (hR : ∀ (U : family) (v : Fin n) (a b : ∀ i, τ i),
      (∀ i ∉ U.val, a i = b i) → R U v a = R U v b)
    (hsum : ∀ a, T a = ∑ U : family, ∑ v : Fin n, L U v a * R U v a) :
    CutFactorization family n T := by
  refine ⟨fun U v => descend (restrictIn U.val) (L U v),
    fun U v => descend (restrictOut U.val) (R U v), ?_⟩
  intro a
  rw [hsum]
  apply Finset.sum_congr rfl
  intro U _
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg₂ (· * ·)
    (descend_apply (restrictIn (τ := τ) U.val) (L U v)
      (fun b c h => hL U v b c (fun i hi => congrFun h ⟨i, hi⟩)) a).symm
    (descend_apply (restrictOut (τ := τ) U.val) (R U v)
      (fun b c h => hR U v b c (fun i hi => congrFun h ⟨i, hi⟩)) a).symm

/-- A product through a finite set of cut vertices has matrix rank at most its size. -/
theorem CutFactorization.exists_summands [Field F] [Fintype V] [∀ i, Fintype (τ i)]
    {family : Finset (Finset V)} {n : ℕ} {T : (∀ i, τ i) → F}
    (h : CutFactorization family n T) :
    ∃ t : family → (∀ i, τ i) → F, (∀ a, T a = ∑ U : family, t U a) ∧
      ∀ U, (flatten U.val (t U)).rank ≤ n := by
  classical
  obtain ⟨L, R, hsum⟩ := h
  let t (U : family) (a : ∀ i, τ i) :=
    ∑ v : Fin n, L U v (restrictIn U.val a) * R U v (restrictOut U.val a)
  refine ⟨t, hsum, fun U => ?_⟩
  let A : Matrix (Inside τ U.val) (Fin n) F := fun x v => L U v x
  let B : Matrix (Fin n) (Outside τ U.val) F := fun v y => R U v y
  have heq : flatten U.val (t U) = A * B := by
    ext x y
    rw [Matrix.mul_apply]
    simp [flatten, t, A, B]
  rw [heq]
  exact (Matrix.rank_mul_le_left A B).trans
    (A.rank_le_card_width.trans (Fintype.card_fin n).le)

end Hierarchy.ABPFirstCut

end OAI
