import OAI.Computability.NearSquareRoot.PrecisionPairRows
import OAI.Computability.NearSquareRoot.KernelPassMixPhysical

/-! # A direct two-bit normalized Walsh pass on consecutive records

Each four-record group is one two-bit fiber. The columns and rows are in
ascending binary order, with the low bit first. The four signed accumulators
are shifted once, and every output returns to its slot in the flat stream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshBase

open IntegerMultiplication Code KernelPass KernelPassMix

/-- The binary digits of a local address, in increasing place value. -/
def bits (x : Fin 4) : Fin 2 → ZMod 2 := finFunctionFinEquiv.symm x

def coeff (y x : Fin 4) : Coefficient :=
  (if bits y 0 * bits x 0 + bits y 1 * bits x 1 = 0 then 1 else -1, 1)

@[simp] theorem coefficient_value (y x : Fin 4) : value (coeff y x) = pairEntry (bits y) (bits x) := by
  unfold value coeff pairEntry
  split <;> norm_num

/-- One result at the target record width. -/
def transform {w : ℕ} (x : Fin 4 → Dusk.Grain w) (b : Fin 4) := rounded (coeff b) x

def FitsGroup {w : ℕ} (x : Fin 4 → Dusk.Grain w) : Prop :=
  ∀ b, ‖Grid.toC (accum (coeff b) (Grid.aspect ∘ x)) / (2 : ℂ)^denom (coeff b)‖ < (2 : ℝ)^w

/-- Each output is within two grid units of its exact normalized two-bit row. -/
theorem entry_error {w : ℕ} (p : ℕ) (x : Fin 4 → Dusk.Grain w) (h : FitsGroup x) (b : Fin 4) :
    ‖Grid.meaning p w (transform x b) - ∑ a, (pairEntry (bits b) (bits a) : ℂ) * Grid.meaning p w (x a)‖
      ≤ 2 / (2 : ℝ)^p := by
  simpa only [transform, rounded, accum_meaning, coefficient_value] using
    round_error p (denom (coeff b)) w (accum (coeff b) (Grid.aspect ∘ x)) (h b)

private abbrev Quad (α : Type*) := (α × α) × (α × α)

private def quad {w : ℕ} (x : Fin 4 → Dusk.Grain w) : Quad Dusk.Pair :=
  ((Dusk.mark (x 0), Dusk.mark (x 1)), (Dusk.mark (x 2), Dusk.mark (x 3)))

private def runGroup (q : Quad Dusk.Pair) : List Dusk.Pair :=
  mixMarked coeff (ruler q.1.1.1, [q.1.1, q.1.2, q.2.1, q.2.2])

private theorem easy_group : Easy runGroup := by
  have e : Easy (fun q : Quad Dusk.Pair => (ruler q.1.1.1, [q.1.1, q.1.2, q.2.1, q.2.2])) := by fun_prop
  exact e.compose (mixMarked_easy coeff)

private theorem of_four {α : Type*} (f : Fin 4 → α) : List.ofFn f = [f 0, f 1, f 2, f 3] := rfl

private theorem run_group {w : ℕ} (x : Fin 4 → Dusk.Grain w) (h : FitsGroup x) :
    runGroup (quad x) = List.ofFn (Dusk.mark ∘ transform x) := by
  have hw : ruler (Dusk.mark (x 0)).1 = tally (w+1) := by simp [ruler,tally,Dusk.mark]
  simpa only [quad, runGroup, hw, of_four, Function.comp_apply, transform] using
    mixMarked_exact coeff x (fun b => divA_fits _ _ _ (h b))

/-- Serialized stream of consecutive groups, each with its four record markers. -/
def stream {w : ℕ} (xs : List (Fin 4 → Dusk.Grain w)) : List Dusk.Pair :=
  xs.flatMap fun x => List.ofFn (Dusk.mark ∘ x)

private theorem twice_pack {w : ℕ} (xs : List (Fin 4 → Dusk.Grain w)) :
    PairRows.consecutive (PairRows.consecutive (xs.map quad)) = stream xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [quad, stream, ih] at *

/-- Total size of all the paired records, including list delimiters. -/
private theorem size_packed {w : ℕ} (xs : List (Fin 4 → Dusk.Grain w)) :
    size (xs.map quad) = xs.length * (16*(w+1)+16) + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have sq : size (quad x) = 16*(w+1)+15 := by
      change (size (Dusk.mark (x 0))+size (Dusk.mark (x 1))+1) +
        (size (Dusk.mark (x 2))+size (Dusk.mark (x 3))+1)+1 = _
      simp only [Dusk.volume]; omega
    rw [List.map_cons, size_cons, sq, ih, List.length_cons]; ring

theorem size_stream {w : ℕ} (xs : List (Fin 4 → Dusk.Grain w)) :
    size (stream xs) = xs.length * (16*(w+1)+16) + 1 := by
  rw [← twice_pack, PairRows.size_consecutive, PairRows.size_consecutive, size_packed]

variable {I : Type} (w : I → ℕ) (rows : (t : I) → List (Fin 4 → Dusk.Grain (w t)))

/-- The machine obtains its one width ruler from the first record of each group.
The empty stream executes the same command. -/
theorem task (h : ∀ t, ∀ x ∈ rows t, FitsGroup x) :
    Task (fun t => ((rows t).length+1) * (w t+1)) (fun t => send (stream (rows t)))
      (fun t => send (stream ((rows t).map transform))) := by
  let q (t : I) := (rows t).map quad
  have initial := PairRows.packPairs.on (fun t => PairRows.consecutive (q t))
  have second := PairRows.packPairs.on q
  have finish := (easy_group.mapping.compose Easy.flatten).on q
  have run := (initial.compose second).compose finish
  have out (t : I) : ((q t).map runGroup).flatten = stream ((rows t).map transform) := by
    simp only [q, List.map_map, stream, List.flatMap_def]
    apply congrArg List.flatten
    exact List.map_congr_left (fun a ha => run_group a (h t a ha))
  simp only [out, q, twice_pack, PairRows.size_consecutive, size_packed] at run
  apply run.bound 100
  intro t
  ring_nf
  omega

/-- Actual stack time and additional live space for the entire contiguous stream. -/
theorem bounded (h : ∀ t, ∀ x ∈ rows t, FitsGroup x) :
    Space.BoundedTask (fun t => ((rows t).length+1) * (w t+1))
      (fun t => ((rows t).length+1) * (w t+1)) (fun t => send (stream (rows t)))
      (fun t => send (stream ((rows t).map transform))) := by
  apply (Space.BoundedTask.of_time (task w rows h)).bound 1 36
  · simp
  · intro t
    change size (stream (rows t)) + _ + 1 ≤ _
    rw [size_stream]; ring_nf; omega

end PhysicalWalshBase

end NearSquareRoot
end Computability
end OAI
