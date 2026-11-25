import OAI.Computability.NearSquareRoot.CommonRegisters
import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.IntegerMultiplication.Strip.Rails

/-!
# Fixed-register selection in a P192 finite series

The selected rank changes the control sequence. Each step consumes and discards
one preceding tree, and the final step copies the selected tree across the
remaining suffix. The three registers and the linear clock are independent
of the rank, number of fields, and field shapes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space

theorem split_within {R i : ℕ} (hi : i < R) {leaf : Bool → Cmd} {pair : Cmd}
    (hl : ∀ b, Within R (leaf b)) (hp : Within R pair) :
    Within R (splitRoot i leaf pair) := by
  refine ⟨hi, fun x => ⟨hi, ?_⟩⟩
  cases x with
  | none => trivial
  | some x =>
    cases x with
    | bit b => exact hl b
    | node => exact hp
    | sep => trivial

theorem flood_within {R : ℕ} (indices : List ℕ) (op : ℕ → Cmd)
    (h : ∀ i ∈ indices, Within R (op i)) : Within R (flood indices op) := by
  induction indices with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨h x List.mem_cons_self, ih fun i hi => h i (List.mem_cons_of_mem _ hi)⟩

theorem forward_within {R i : ℕ} (hi : i < R) {indices : List ℕ}
    (hs : ∀ a ∈ indices, a < R) : Within R (forward i indices) :=
  split_within hi (fun _ => flood_within _ _ hs) ⟨trivial, trivial, flood_within _ _ hs⟩

theorem discard_within {R i : ℕ} (hi : i < R) : Within R (discard i) :=
  forward_within hi (by simp)

theorem move_within {R i j u : ℕ} (hi : i < R) (hj : j < R) (hu : u < R) :
    Within R (move i j u) :=
  ⟨forward_within hi (by simpa using hu), forward_within hu (by simpa using hj)⟩

theorem clone_within {R i j u : ℕ} (hi : i < R) (hj : j < R) (hu : u < R) :
    Within R (clone i j u) := by
  refine ⟨forward_within hi (by simpa using hu), forward_within hu ?_⟩
  simpa using And.intro hi hj

/-- At rank zero, park the selected head on register one while freeing the tail.
For positive ranks, drop one head and continue directly on the tail. -/
def cellCommand : ℕ → Cmd
  | 0 => splitRoot 0 (fun _ => .pass)
      ((move 0 1 2).join ((discard 0).join (move 1 0 2)))
  | n + 1 => splitRoot 0 (fun _ => .pass) ((discard 0).join (cellCommand n))

theorem cell_within (n : ℕ) : Within 3 (cellCommand n) := by
  induction n with
  | zero =>
    exact split_within (by decide) (fun _ => trivial)
      ⟨move_within (by decide) (by decide) (by decide),
       discard_within (by decide), move_within (by decide) (by decide) (by decide)⟩
  | succ n ih =>
    exact split_within (by decide) (fun _ => trivial) ⟨discard_within (by decide), ih⟩

/-- A single absolute linear clock works for the whole family of projections. -/
theorem cell_fits {K : Type} (v : K → Tree) (xs : List K) (n : ℕ) (k : K)
    (hk : xs[n]? = some k) (env : Env) (r : Deck) :
    Fits env (cellCommand n) (pile 0 (Task.forest v xs) r) (pile 0 (v k) r)
      (90 * (Task.forest v xs).count) := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => contradiction
    | cons a xs =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst a
      let tail := Task.forest v xs
      have a := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide)
        (v k) env (pile 0 tail r)
      rw [pile_comm 1 _ r 0 _ (by decide)] at a
      have b := fits_discard 0 tail env (pile 1 (v k) r)
      have c := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (v k) env r
      apply (fits_pair (a.join (b.join c))).mono
      simp only [Task.forest_cons, Tree.count, Nat.mul_add, Nat.mul_one, tail]
      omega
  | succ n ih =>
    cases xs with
    | nil => contradiction
    | cons a xs =>
      have rem := ih xs (by simpa using hk)
      have drop := fits_discard 0 (v a) env (pile 0 (Task.forest v xs) r)
      apply (fits_pair (drop.join rem)).mono
      simp only [Task.forest_cons, Tree.count, Nat.mul_add, Nat.mul_one]
      omega

/-- The witnessed P192 program for a finite field selection, with bounded
execution on top of any pre-existing deck. -/
theorem finite_cell_bounded {K : Type} [DecidableEq K] (s : Series K) (v : K → Tree)
    (k : K) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (cellCommand (s.explore.idxOf k)) (pile 0 (stripe s v) r)
      (pile 0 (v k) r) (90 * (stripe s v).count)
      (base + 91 * (stripe s v).count) (90 * (stripe s v).count) := by
  have h := cell_fits v s.explore _ k (List.getElem?_idxOf (s.complete k)) env r
  rw [stripe_simple]
  refine BoundedFits.of_fits h (fun i => ?_) le_rfl
  have hx := hr.pile 0 (Task.forest v s.explore) i
  omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
