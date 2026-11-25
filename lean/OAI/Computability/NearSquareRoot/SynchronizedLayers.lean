import OAI.Computability.NearSquareRoot.SynchronizedLayerTensor
import Mathlib.Tactic

/-! # Synchronized layers for independent address blocks

A round takes one pending operation from each local program. It reserves a
permutation, a phase diagonal, and a Walsh slot, so the round has the same
shape regardless of which of these operations each block needs next.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedLayers

inductive Kind where
  | permutation
  | diagonal
  | walsh
  deriving DecidableEq

variable {ι : Type*} {Op : ι → Type*}

/-- All non-idle blocks of a layer perform the same kind of operation. -/
structure Layer (Op : ι → Type*) (kind : ∀ i, Op i → Kind) where
  slot : Kind
  action : ∀ i, Option (Op i)
  compatible : ∀ i a, action i = some a → kind i a = slot

variable (kind : ∀ i, Op i → Kind)

private def slotAction (s : Kind) (i : ι) (a : Option (Op i)) : Option (Op i) :=
  a.bind fun x => if kind i x = s then some x else none

/-- A scheduled block either runs its head operation or idles for this slot. -/
def slotLayer (s : Kind) (word : ∀ i, List (Op i)) : Layer Op kind where
  slot := s
  action i := slotAction kind s i (word i).head?
  compatible i a he := by
    generalize hh : (word i).head? = o at he
    cases o with
    | none => simp [slotAction] at he
    | some b =>
      dsimp [slotAction] at he
      split at he <;> simp_all

/-- Use three slots for each step of a longest local program. -/
def schedule : ℕ → (∀ i, List (Op i)) → List (Layer Op kind)
  | 0, _ => []
  | n + 1, word =>
    slotLayer kind .permutation word :: slotLayer kind .diagonal word ::
    slotLayer kind .walsh word :: schedule n (fun i => (word i).tail)

@[simp] theorem schedule_length (n : ℕ) (word : ∀ i, List (Op i)) :
    (schedule kind n word).length = 3 * n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih => simp [schedule, ih, Nat.mul_succ]

/-- Removing idles recovers precisely the local input program, in its original order. -/
theorem schedule_filterMap (n : ℕ) (word : ∀ i, List (Op i)) (i : ι) :
    (schedule kind n word).filterMap (fun l => l.action i) = (word i).take n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih =>
    simp only [schedule, List.filterMap_cons, ih]
    cases he : word i with
    | nil => simp [slotLayer, slotAction, he]
    | cons a as =>
      cases hk : kind i a <;> simp [slotLayer, slotAction, he, hk]

theorem schedule_executes {n : ℕ} (word : ∀ i, List (Op i)) (hn : ∀ i, (word i).length ≤ n)
    (i : ι) : (schedule kind n word).filterMap (fun l => l.action i) = word i := by
  rw [schedule_filterMap, List.take_of_length_le (hn i)]

/-- Identity on an idle block, and the given local action on an active block. -/
def applyLayer {M : ι → Type*} [∀ i, One (M i)] (eval : ∀ i, Op i → M i)
    (l : Layer Op kind) (i : ι) : M i := ((l.action i).map (eval i)).getD 1

private theorem prod_with_idles {M : ι → Type*} [∀ i, Monoid (M i)] (eval : ∀ i, Op i → M i)
    (layers : List (Layer Op kind)) (i : ι) :
    (layers.map (fun l => applyLayer kind eval l i)).prod =
      ((layers.filterMap (fun l => l.action i)).map (eval i)).prod := by
  induction layers with
  | nil => rfl
  | cons l layers ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    cases he : l.action i <;> simp [applyLayer, he]

/-- Matrix products (or any monoid products) in every block survive scheduling. -/
theorem schedule_prod {M : ι → Type*} [∀ i, Monoid (M i)] (eval : ∀ i, Op i → M i)
    {n : ℕ} (word : ∀ i, List (Op i)) (hn : ∀ i, (word i).length ≤ n) (i : ι) :
    ((schedule kind n word).map (fun l => applyLayer kind eval l i)).prod =
      ((word i).map (eval i)).prod := by
  rw [prod_with_idles, schedule_executes kind word hn]

/-- Multiplying the scheduled global layers gives precisely the tensor of the
requested local transforms. The words here use matrix multiplication order. -/
theorem schedule_tensor {A : ι → Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [CommSemiring R]
    (eval : ∀ i, Op i → Matrix (A i) (A i) R)
    {n : ℕ} (word : ∀ i, List (Op i)) (hn : ∀ i, (word i).length ≤ n) :
    ((schedule kind n word).map (fun l =>
        SynchronizedPadding.tensorMatrix (applyLayer kind eval l))).prod =
      SynchronizedPadding.tensorMatrix (fun i => ((word i).map (eval i)).prod) := by
  simp_rw [← schedule_prod kind eval word hn]
  have h := SynchronizedPadding.tensorMatrix_list_prod
    ((schedule kind n word).map (applyLayer kind eval))
  simpa only [List.map_map, Function.comp_def] using h.symm

end SynchronizedLayers

end NearSquareRoot
end Computability
end OAI
