import OAI.Computability.NearSquareRoot.BoxMaskStep
import OAI.Computability.NearSquareRoot.BoxOrder

/-! # Building the dense validity mask in linear output time

The table for a slower axis repeats the mask of the faster axes. Each nontrivial
axis at least doubles the size, so summing over all intermediate tables costs
a constant times the final mask. The input directory contains unary counts of
valid and invalid slots on each axis, slowest first.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxMask
open IntegerMultiplication Code BoxOrder

abbrev Counts := ℕ × ℕ

def encodeCounts (p : Counts) := (tally p.1, tally p.2)

def header (xs : List Counts) := xs.map encodeCounts

private def legal (xs : List Counts) : Prop := ∀ p ∈ xs, 2 ≤ total p

private def stepCost (p : Counts) (xs : List Counts) : ℕ :=
  BoxMaskStep.budget (encodeCounts p, expand xs)

private theorem step_cost_eq (p : Counts) (xs : List Counts) :
    stepCost p xs = (total p + 1) * ((expand xs).length + 1) := by
  simp [stepCost, BoxMaskStep.budget, encodeCounts, total]

private theorem count_size (p : Counts) : size (encodeCounts p) = 2 * total p + 3 := by
  simp [encodeCounts, size_tally, total]
  omega

private theorem positive {xs : List Counts} (h : legal xs) : 0 < (expand xs).length := by
  rw [length_expand]
  exact List.prod_pos (by simpa only [List.forall_mem_map] using fun p hp => lt_of_lt_of_le (by decide : 0 < 2) (h p hp))

private theorem cost_fold (xs : List Counts) (h : legal xs) :
    Task.foldCost (fun p tail => stepCost p tail + size (encodeCounts p)) xs ≤ 20 * (expand xs).length := by
  induction xs with
  | nil => decide
  | cons p xs ih =>
    have hc : legal xs := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hp := h p List.mem_cons_self
    have ht := positive hc
    specialize ih hc
    rw [Task.foldCost, step_cost_eq, count_size]
    have he : (expand (p :: xs)).length = total p * (expand xs).length := by simp
    rw [he]
    nlinarith [Nat.mul_le_mul_right (expand xs).length hp,
      Nat.mul_le_mul_left (total p) (show 1 ≤ (expand xs).length from ht)]

private theorem size_header (xs : List Counts) (h : legal xs) :
    size (header xs) ≤ 20 * (expand xs).length := by
  induction xs with
  | nil => decide
  | cons p xs ih =>
    have hc : legal xs := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hp := h p List.mem_cons_self
    have ht := positive hc
    specialize ih hc
    change size (encodeCounts p :: header xs) ≤ _
    rw [size_cons, count_size]
    have he : (expand (p :: xs)).length = total p * (expand xs).length := by simp
    rw [he]
    nlinarith [Nat.mul_le_mul_right (expand xs).length hp,
      Nat.mul_le_mul_left (total p) (show 1 ≤ (expand xs).length from ht)]

/-- Starting with the axis directory, generate one validity bit for each physical
record in tape order, in time linear in the length of that output bit stream. -/
theorem task : Task (fun x : {xs : List Counts // ∀ p ∈ xs, 2 ≤ total p} => (expand x.val).length)
    (fun x => send (header x.val)) (fun x => send (expand x.val)) := by
  let D (xs : List Counts) (_ : Unit) := legal xs
  let tag (_ : Unit) (p : Counts) := send (encodeCounts p)
  let out (xs : List Counts) (_ : Unit) := send (expand xs)
  let StepInput := {s : Counts × List Counts × Unit // D (s.1::s.2.1) s.2.2}
  have hs := BoxMaskStep.task.on (fun i : StepInput => (encodeCounts i.val.1, expand i.val.2.1))
  have next (i : StepInput) : BoxMaskStep.applyAxis (encodeCounts i.val.1, expand i.val.2.1) = expand (i.val.1::i.val.2.1) := by
    obtain ⟨⟨⟨a,b⟩, xs, u⟩, h⟩ := i
    simp [BoxMaskStep.applyAxis, encodeCounts, expand]
  have fold := Task.foldRight (D := D) (p := tag) (f := out)
    (seed := fun _ => send ([true] : List Bool)) (b := fun _ => 0)
    (a := fun p xs _ => stepCost p xs)
    (fun _ _ _ hd a ha => hd a (List.mem_cons_of_mem _ ha)) Task.self
    (hs.conform (fun _ => rfl) (fun _ => rfl) (fun i => congrArg send (next i)))
  let Input := {xs : List Counts // ∀ p ∈ xs, 2 ≤ total p}
  let lift (x : Input) : {s : List Counts × Unit // D s.1 s.2} := ⟨(x.val, ()), x.property⟩
  have push : Easy (fun t : List (Tally × Tally) => (t, [true])) := by fun_prop
  have eq (xs : List Counts) : Task.forest (tag ()) xs = send (header xs) := by
    rw [← Task.forest_send (header xs), header, Task.forest_map]
  have apply := fold.on lift
  simp only [lift, tag, out, Nat.zero_add] at apply
  have input (xs : List Counts) : Task.forest (fun p => send (encodeCounts p)) xs = send (header xs) := eq xs
  simp only [input] at apply
  refine ((push.on fun x : Input => header x.val).compose apply).bound 41 (fun x => ?_)
  change size (header x.val) + Task.foldCost (fun p xs => stepCost p xs + size (encodeCounts p)) x.val + 1 ≤ _
  have h₁ := size_header _ x.property
  have h₂ := cost_fold _ x.property
  omega

theorem shape_legal {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box) :
    ∀ p ∈ shape box, 2 ≤ total p := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp)
  have h := (hb.axisBounds a ha).2.2
  exact h.1.trans (Nat.le_add_right ..)

theorem of_valid {X : Type} (k l : X → ℕ) (box : X → List (ℕ × ℕ))
    (hb : ∀ x, BoxShape.Valid (k x) (l x) (box x)) :
    Task (fun x => 2 ^ k x) (fun x => send (header (shape (box x))))
      (fun x => send (expand (shape (box x)))) := by
  have h := task.on fun x : X => ⟨shape (box x), shape_legal (hb x)⟩
  exact h.conform (fun x => length_shape (hb x)) (fun _ => rfl) (fun _ => rfl)

end BoxMask

end NearSquareRoot
end Computability
end OAI
