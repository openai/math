import OAI.Computability.VPVNP.CompressionHistory

/-!
# Composition of bounded compressor histories

When each branch of one compressor execution continues with a second execution,
the records of the combined execution consist of the original records of both
stages. Uniform local bounds are preserved and the selected chain lengths add.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open NetworkKernel

variable {R : Type*} [CommSemiring R] {a b g n b' n' : ℕ} {X : State a g}

/-- A bound on a single pass may be enlarged without changing any records. -/
theorem StatePass.bounded_mono (p : StatePass R X b n) (rec : p.Records) {C D : ℕ}
    (hCD : C ≤ D) (h : p.Bounded rec C) : p.Bounded rec D := by
  intro i
  obtain ⟨hcount, hwidth, hnext⟩ := h i
  exact ⟨fun v ↦ (hcount v).trans hCD, hwidth.trans (Nat.mul_le_mul_right _ hCD), hnext⟩

namespace StateExecution

/-- Enlarge the uniform bound throughout an execution tree. -/
theorem bounded_mono (E : StateExecution R b n X) (rec : E.Records) {C D : ℕ}
    (hCD : C ≤ D) (h : E.Bounded C rec) : E.Bounded D rec := by
  induction E with
  | done => trivial
  | more p tail ih => exact ⟨p.bounded_mono rec.1 hCD h.1, fun i ↦ ih i (rec.2 i) (h.2 i)⟩

/-- Append the actual continuation records at each leaf of an execution. -/
def bindRecords {a g : ℕ} {X : State a g} (E : StateExecution R b n X)
    : (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z)) →
      E.Records → ((z : E.Choices) → (f z).Records) → (E.bind f).Records :=
  match E with
  | .done _ => fun _ _ after ↦ after ()
  | .more _ tail => fun f rec after ↦ (rec.1, fun i ↦ (tail i).bindRecords
      (fun z ↦ f ⟨i, z⟩) (rec.2 i) (fun z ↦ after ⟨i, z⟩))

/-- A common bound on all elementary passes holds on every combined branch. -/
theorem bounded_bindRecords (E : StateExecution R b n X)
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (rec : E.Records) (after : ∀ z, (f z).Records) {C : ℕ}
    (hE : E.Bounded C rec) (hAfter : ∀ z, (f z).Bounded C (after z)) :
    (E.bind f).Bounded C (E.bindRecords f rec after) := by
  induction E with
  | done => exact hAfter ()
  | more p tail ih =>
    exact ⟨hE.1, fun i ↦ ih i (fun z ↦ f ⟨i, z⟩) (rec.2 i) (fun z ↦ after ⟨i, z⟩)
      (hE.2 i) (fun z ↦ hAfter ⟨i, z⟩)⟩

omit [CommSemiring R] in
private theorem length_cast {N Y Z : Network} (h : N = Y) (chain : TermChain R Y Z) :
    (h.symm ▸ chain : TermChain R N Z).length = chain.length := by cases h; rfl

/-- Passing through one kernel adds one to the selected continuation length. -/
theorem length_more {c r : ℕ} (p : StatePass R X c r)
    (tail : ∀ i, StateExecution R b n (p.next i))
    (rec : (.more p tail : StateExecution R b n X).Records)
    (z : (.more p tail : StateExecution R b n X).Choices) :
    ((.more p tail : StateExecution R b n X).termChain rec z).length =
      ((tail z.1).termChain (rec.2 z.1) z.2).length + 1 := by
  exact congrArg (· + 1) (length_cast (p.output_eq z.1) _)

/-- Each selected chain has the sum of the lengths of its actual prefix and suffix. -/
theorem exists_length_bindRecords (E : StateExecution R b n X)
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (rec : E.Records) (after : ∀ z, (f z).Records) (w : (E.bind f).Choices) :
    ∃ (z : E.Choices) (y : (f z).Choices),
      ((E.bind f).termChain (E.bindRecords f rec after) w).length =
        (E.termChain rec z).length + ((f z).termChain (after z) y).length := by
  induction E with
  | done => exact ⟨(), w, (Nat.zero_add _).symm⟩
  | more p tail ih =>
    obtain ⟨z, y, h⟩ := ih w.1 (fun z ↦ f ⟨w.1,z⟩) (rec.2 w.1) (fun z ↦ after ⟨w.1,z⟩) w.2
    refine ⟨⟨w.1,z⟩, y, ?_⟩
    refine (length_more p (fun i ↦ (tail i).bind (fun z ↦ f ⟨i,z⟩))
      ((more p tail).bindRecords f rec after) w).trans ?_
    refine (congrArg (· + 1) h).trans ((Nat.add_right_comm _ _ 1).trans ?_)
    exact congrArg (· + _) (length_more p tail rec ⟨w.1, z⟩).symm

/-- Uniform bounds on the lengths of the two stages add after dependent continuation. -/
theorem length_bindRecords_le (E : StateExecution R b n X)
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (rec : E.Records) (after : ∀ z, (f z).Records) {m₁ m₂ : ℕ}
    (hE : ∀ z, (E.termChain rec z).length ≤ m₁)
    (hAfter : ∀ z y, ((f z).termChain (after z) y).length ≤ m₂)
    (w : (E.bind f).Choices) :
    ((E.bind f).termChain (E.bindRecords f rec after) w).length ≤ m₁ + m₂ := by
  obtain ⟨z, y, h⟩ := E.exists_length_bindRecords f rec after w
  exact h.trans_le (Nat.add_le_add (hE z) (hAfter z y))

end StateExecution
end Compression

end VPVNP
end Computability
end OAI
