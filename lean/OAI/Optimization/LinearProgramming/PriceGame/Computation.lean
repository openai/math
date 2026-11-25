import OAI.Optimization.LinearProgramming.PriceGame.Model
import Mathlib.Data.List.Forall2

/-! Finite computations with designated, history-dependent queries. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

universe u v w

/-- A finite adaptive computation with values of any result type. Each query asks for
one coordinate of a single rational price vector. -/
inductive Computation (N : ℕ) (α : Type u) : Type u where
  | pure (value : α)
  | ask (query : Query N) (next : Bool → Computation N α)

namespace Computation

variable {N R : ℕ} {anchor : Fin N} {α : Type u} {β : Type v} {γ : Type w}

/-- Sequential composition, retaining both possible continuations of every query. -/
def bind (p : Computation N α) (f : α → Computation N β) : Computation N β :=
  match p with
  | .pure a => f a
  | .ask q next => .ask q fun b => (next b).bind f

@[simp] theorem bind_pure (a : α) (f : α → Computation N β) : (pure a).bind f = f a := rfl

@[simp] theorem bind_ask (q : Query N) (next : Bool → Computation N α)
    (f : α → Computation N β) :
    (ask q next).bind f = .ask q fun b => (next b).bind f := rfl

@[simp] theorem bind_pure_right (p : Computation N α) : p.bind pure = p := by
  induction p with
  | pure => rfl
  | ask q next ih => simp [ih]

theorem bind_assoc (p : Computation N α) (f : α → Computation N β) (g : β → Computation N γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | pure => rfl
  | ask q next ih => simp [ih]

def map (p : Computation N α) (f : α → β) : Computation N β := p.bind fun a => .pure (f a)

/-- A program can ask the same question repeatedly without imposing equality on
unforced replies. This permits arbitrary dependence on the observed history. -/
inductive Reaches (h : Hidden N R anchor) : Computation N α → α → Prop where
  | pure (a : α) : Reaches h (.pure a) a
  | ask {q : Query N} {next : Bool → Computation N α} {reply : Bool} {a : α}
      (allowed : h.Forced q → reply = h.positive) (rest : Reaches h (next reply) a) :
      Reaches h (.ask q next) a

@[simp] theorem reaches_pure_iff (h : Hidden N R anchor) (a b : α) :
    Reaches h (.pure a) b ↔ b = a := by
  constructor
  · intro hr
    cases hr
    rfl
  · rintro rfl
    exact .pure _

theorem reaches_ask_iff (h : Hidden N R anchor) (q : Query N)
    (next : Bool → Computation N α) (a : α) :
    Reaches h (.ask q next) a ↔ ∃ b, (h.Forced q → b = h.positive) ∧ Reaches h (next b) a := by
  constructor
  · rintro ⟨_, _⟩
    exact ⟨_, ‹h.Forced q → _›, ‹Reaches h _ _›⟩
  · rintro ⟨b, hb, hr⟩
    exact .ask hb hr

theorem reaches_bind_iff (h : Hidden N R anchor) (p : Computation N α)
    (f : α → Computation N β) (b : β) :
    Reaches h (p.bind f) b ↔ ∃ a, Reaches h p a ∧ Reaches h (f a) b := by
  induction p with
  | pure a => simp
  | ask q next ih =>
    rw [bind_ask, reaches_ask_iff]
    constructor
    · rintro ⟨reply, allowed, rest⟩
      obtain ⟨a, ha, hret⟩ := (ih reply).mp rest
      exact ⟨a, .ask allowed ha, hret⟩
    · rintro ⟨a, hr, hret⟩
      obtain ⟨reply, allowed, rest⟩ := (reaches_ask_iff h q next a).mp hr
      exact ⟨reply, allowed, (ih reply).mpr ⟨a, rest, hret⟩⟩

theorem reaches_map_iff (h : Hidden N R anchor) (p : Computation N α) (f : α → β) (b : β) :
    Reaches h (p.map f) b ↔ ∃ a, Reaches h p a ∧ f a = b := by
  simp [map, reaches_bind_iff, eq_comm]

/-- Worst-case number of queries, including arbitrary inconsistent replies. -/
def height : Computation N α → ℕ
  | .pure _ => 0
  | .ask _ next => max (next false).height (next true).height + 1

/-- Composition bound for the worst case. The continuation may depend on the result. -/
theorem height_bind_le (p : Computation N α) (f : α → Computation N β) (K : ℕ)
    (hf : ∀ a, (f a).height ≤ K) : (p.bind f).height ≤ p.height + K := by
  induction p with
  | pure a => simpa [height] using hf a
  | ask q next ih =>
    simp only [bind_ask, height]
    have hfalse := ih false
    have htrue := ih true
    omega

@[simp] theorem height_map (p : Computation N α) (f : α → β) : (p.map f).height = p.height := by
  induction p with
  | pure a => rfl
  | ask q next ih =>
    change max ((next false).map f).height ((next true).map f).height + 1 = _
    rw [ih, ih]
    rfl

/-- Interpret the complete transcript dynamically. -/
def run (reply : List (Query N × Bool) → Query N → Bool) (p : Computation N α)
    (history : List (Query N × Bool) := []) : α :=
  match p with
  | .pure a => a
  | .ask q next =>
    let b := reply history q
    (next b).run reply ((q, b) :: history)

theorem reaches_run (h : Hidden N R anchor) (reply : List (Query N × Bool) → Query N → Bool)
    (valid : ∀ history q, h.Forced q → reply history q = h.positive)
    (p : Computation N α) (history : List (Query N × Bool)) :
    Reaches h p (p.run reply history) := by
  induction p generalizing history with
  | pure a => exact .pure _
  | ask q next ih => exact .ask (valid history q) (ih (reply history q) _)

/-- Specialize a general interactive computation to the principal binary-output tree. -/
def toTree : Computation N Bool → Tree N
  | .pure b => .result b
  | .ask q next => .ask q fun b => (next b).toTree

/-- Existing binary-output programs can be composed with arbitrary result types. -/
def ofTree : Tree N → Computation N Bool
  | .result b => .pure b
  | .ask q next => .ask q fun b => ofTree (next b)

@[simp] theorem toTree_ofTree (t : Tree N) : (ofTree t).toTree = t := by
  induction t with
  | result => rfl
  | ask q next ih => simp [ofTree, toTree, ih]

@[simp] theorem height_toTree (p : Computation N Bool) : p.toTree.height = p.height := by
  induction p with
  | pure => rfl
  | ask q next ih => simp [toTree, height, Tree.height, ih]

theorem reaches_toTree_iff (h : Hidden N R anchor) (p : Computation N Bool) (b : Bool) :
    Tree.Reaches h p.toTree b ↔ Reaches h p b := by
  induction p with
  | pure a =>
    constructor
    · intro hr
      cases hr
      exact .pure _
    · intro hr
      cases hr
      exact .result _
  | ask q next ih =>
    constructor
    · intro hr
      cases hr with
      | ask allowed rest => exact .ask allowed ((ih _).mp rest)
    · intro hr
      cases hr with
      | ask allowed rest => exact .ask allowed ((ih _).mpr rest)

/-- Use standard `do` notation for finite adaptive computations. -/
instance : Monad (Computation N) where
  pure := Computation.pure
  bind := Computation.bind

/-- Run an ordered sequence of finite computations, preserving the order of replies. -/
def traverse (f : α → Computation N β) : List α → Computation N (List β)
  | [] => .pure []
  | a :: as => (f a).bind fun b => (traverse f as).map (b :: ·)

theorem reaches_traverse_iff (h : Hidden N R anchor) (f : α → Computation N β) (xs : List α)
    (ys : List β) :
    Reaches h (traverse f xs) ys ↔ List.Forall₂ (fun x y => Reaches h (f x) y) xs ys := by
  induction xs generalizing ys with
  | nil => simp [traverse]
  | cons x xs ih =>
    rw [traverse, reaches_bind_iff]
    constructor
    · rintro ⟨b, hb, hrest⟩
      obtain ⟨ys', hy, rfl⟩ := (reaches_map_iff _ _ _ _).mp hrest
      exact .cons hb ((ih _).mp hy)
    · intro hy
      cases hy with
      | cons hb htail =>
        exact ⟨_, hb, (reaches_map_iff _ _ _ _).mpr ⟨_, (ih _).mpr htail, rfl⟩⟩

theorem height_traverse_le (f : α → Computation N β) (xs : List α) :
    (traverse f xs).height ≤ (xs.map fun x => (f x).height).sum := by
  induction xs with
  | nil => simp [traverse, height]
  | cons a xs ih =>
    rw [traverse]
    exact (height_bind_le _ _ (traverse f xs).height (fun _ => (height_map _ _).le)).trans
      (by simpa using Nat.add_le_add_left ih (f a).height)

/-- Repeat a sequential update. Each step sees the value returned by its predecessor. -/
def iterate (step : α → Computation N α) : ℕ → α → Computation N α
  | 0, a => .pure a
  | k + 1, a => (step a).bind (iterate step k)

theorem height_iterate_le (step : α → Computation N α) (K : ℕ) (bound : ∀ a, (step a).height ≤ K)
    (k : ℕ) (a : α) : (iterate step k a).height ≤ k * K := by
  induction k generalizing a with
  | zero => simp [iterate, height]
  | succ k ih =>
    rw [iterate, Nat.succ_mul]
    exact (height_bind_le _ _ _ ih).trans (by simpa [Nat.add_comm] using Nat.add_le_add_left (bound a) (k * K))

/-- Every execution of an iteration preserves a stepwise invariant, including one
whose statement depends on the number of elapsed updates. -/
theorem iterate_invariant (h : Hidden N R anchor) (step : α → Computation N α)
    (inv : ℕ → α → Prop)
    (keep : ∀ t a, inv t a → ∀ b, Reaches h (step a) b → inv (t + 1) b)
    (k t : ℕ) (a b : α) (ha : inv t a) (hb : Reaches h (iterate step k a) b) :
    inv (t + k) b := by
  induction k generalizing t a with
  | zero =>
    obtain rfl := (reaches_pure_iff h _ _).mp hb
    simpa using ha
  | succ k ih =>
    obtain ⟨a', hstep, hrest⟩ := (reaches_bind_iff h _ _ _).mp hb
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using ih (t + 1) a' (keep t a ha a' hstep) hrest

end Computation
end PriceGame
end LinearProgramming
end Optimization
end OAI
