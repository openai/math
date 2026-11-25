import OAI.Computability.NearSquareRoot.PrecisionGridPassFold
import OAI.Computability.NearSquareRoot.BoundedBranch

/-! # Space of the phase-table sweep

The rightmost recursive call is in tail position. Each step sees the unprocessed
table forest parked on register 1 and returns its new prefix stream on register 0.
The space bound charges the largest prefix stream and workspace and the total
size of the tables. The sum of the times of the passes only enters the time bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication IntegerMultiplication.Code
open IntegerMultiplication.Code.Task (forest foldCost sweepBody)

private theorem forest_range_suffix (f : ℕ → Tree) (j n : ℕ) :
    (forest f (List.range' j n)).count ≤ (forest f (List.range (j+n))).count := by
  have eq : List.range (j+n) = List.range j ++ List.range' j n := by
    simp only [List.range_eq_range']
    simpa only [Nat.zero_add] using
      (List.range'_append_1 (s := 0) (m := j) (n := n)).symm
  rw [eq, Task.forest_count, Task.forest_count, costSum_cat, List.length_append]
  omega

/-- The same bounded command handles every table, including tables on different
inputs. The indexed sweep preserves a common bound on all live prefix streams,
the entire table forest, and the per-pass scratch and return stacks. -/
theorem BoundedTask.indexedPasses {I : Type*} (d : I → ℕ) (table state : I → ℕ → Tree)
    (cost space : I → ℕ → ℕ) (volume : I → ℕ)
    (step : BoundedTask (fun x : (i : I) × Fin (d i) => cost x.1 x.2.val)
      (fun x => space x.1 x.2.val)
      (fun x => .fork (table x.1 x.2.val) (state x.1 x.2.val))
      (fun x => state x.1 (x.2.val + 1)))
    (hforest : ∀ i, (forest (table i) (List.range (d i))).count ≤ volume i)
    (hstate : ∀ i j, j ≤ d i → (state i j).count ≤ volume i)
    (hspace : ∀ i j, j < d i → space i j ≤ volume i) :
    BoundedTask (fun i => (∑ j ∈ Finset.range (d i), (cost i j + (table i j).count + 1)) + 1)
      volume (fun i => .fork (forest (table i) (List.range (d i))) (state i 0))
      (fun i => state i (d i)) := by
  obtain ⟨cmd, C, H⟩ := step
  let m := sweepBody cmd
  refine ⟨splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (.tie m)), 120+C, ?_⟩
  intro i E r base hr
  have baseCap : DeckCap base r := hr
  let V := volume i
  let depth := (120+C)*(V+1)
  let cap := base + depth
  let wc := fun j (_ : List ℕ) => cost i j + (table i j).count
  have roomy : 100 * (V+1) + C * (V+1) + 1 ≤ depth := by
    dsimp [depth]; rw [Nat.add_mul]; omega
  have suffix (j n : ℕ) (eq : j + n = d i) :
      (forest (table i) (List.range' j n)).count ≤ V := by
    exact (forest_range_suffix (table i) j n).trans (eq ▸ hforest i)
  have loop (n j : ℕ) (eq : j+n = d i) :
      BoundedFits (m :: E) m
        (pile 1 (forest (table i) (List.range' j n)) (pile 0 (state i j) r))
        (pile 0 (state i (d i)) r)
        ((60+C) * foldCost wc (List.range' j n)) cap depth := by
    induction n generalizing j with
    | zero =>
      simp only [Nat.add_zero] at eq
      subst j
      simp only [List.range'_zero, Task.forest_nil, foldCost]
      have hs := hstate i (d i) le_rfl
      have f := fits_bit (b := false) (c := fun _ => Prog.pass)
        (d := (move 1 0 2).join ((pack 0).join (cmd.join (.again 0))))
        (i := 1) (Fits.pass (env := m :: E) (pile 0 (state i (d i)) r))
      apply (BoundedFits.of_fits f (cap := cap) (depth := depth) ?_ ?_).mono _ le_rfl le_rfl
      · intro a
        have h := ((baseCap.pile 0 (state i (d i))).pile 1 (.atom false)) a
        change (letters _ a).length ≤ base + (state i (d i)).count + 1 at h
        dsimp only [cap, V] at *; omega
      · omega
      · omega
    | succ n ih =>
      have lt : j < d i := by omega
      have next : j+1+n = d i := by omega
      let tail := forest (table i) (List.range' (j+1) n)
      have ft := suffix j (n+1) eq
      rw [List.range'_succ, Task.forest_cons] at ft
      change (table i j).count + tail.count + 1 ≤ V at ft
      have hs : (state i j).count ≤ V := hstate i j lt.le
      have ht : space i j ≤ V := hspace i j lt
      have parked := baseCap.pile 1 tail
      have primary := baseCap.pile 0 (state i j)
      have initial := primary.pile 1 (.fork (table i j) tail)
      have moved := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide)
        (table i j) (m :: E) (pile 1 tail (pile 0 (state i j) r))
      have mv : BoundedFits _ _ _ _ _ cap (depth-1) := BoundedFits.of_fits moved
        (fun a => by
          have h := ((primary.pile 1 tail).pile 1 (table i j)) a
          dsimp only [cap]
          omega) (by omega)
      rw [pile_comm 1 tail r 0 (state i j) (by decide)] at mv
      have packFit := fits_pack (table i j) (state i j) (pile 1 tail r) 0 (m :: E)
      have pk : BoundedFits _ _ _ _ _ cap (depth-1) := BoundedFits.of_fits packFit
        (fun a => by
          have h := ((parked.pile 0 (state i j)).pile 0 (table i j)) a
          dsimp only [cap]
          omega) (by omega)
      have cb := H ⟨i,⟨j,lt⟩⟩ (m :: E) (pile 1 tail r) (base+tail.count) parked
      change BoundedFits _ _ _ _ (C*(cost i j+1))
        (base + tail.count + C*(space i j+1)) (C*(space i j+1)) at cb
      have sc : C*(space i j+1) ≤ C*(V+1) := Nat.mul_le_mul_left C (by omega)
      have child := cb.mono le_rfl (show _ ≤ cap by dsimp only [cap]; omega)
        (show _ ≤ depth-1 by omega)
      have tailRun := (ih (j+1) next).again0
      change BoundedFits _ _ (pile 1 tail (pile 0 (state i (j+1)) r)) _ _ _ _ at tailRun
      rw [pile_comm 1 tail r 0 (state i (j+1)) (by decide)] at tailRun
      have reserve : depth-1+1 ≤ depth := by omega
      have pass := mv.join (pk.join (child.join tailRun reserve) reserve) reserve
      rw [← pile_comm 1 tail r 0 (state i j) (by decide)] at pass
      have inside := BoundedFits.pair (c := fun _ => .pass) pass
        (show DeckCap cap (pile 1 (.fork (table i j) tail) (pile 0 (state i j) r)) from
          fun a => by
            have h := initial a
            change _ ≤ base + (state i j).count + ((table i j).count + tail.count + 1) at h
            dsimp only [cap]; omega)
        (show 1 ≤ depth by omega)
      rw [List.range'_succ, Task.forest_cons]
      refine inside.mono ?_ le_rfl le_rfl
      simp only [foldCost, wc, Nat.add_mul, Nat.mul_add, Nat.mul_one]
      omega
  let full := forest (table i) (List.range (d i))
  have sf : full.count ≤ V := hforest i
  have ss : (state i 0).count ≤ V := hstate i 0 (Nat.zero_le _)
  have primary := baseCap.pile 0 (state i 0)
  have outer := BoundedFits.of_fits
    (fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) full E (pile 0 (state i 0) r))
    (cap := cap) (depth := depth-1)
    (fun a => by have h := (primary.pile 0 full) a; dsimp only [cap]; omega)
    (by omega)
  have go := (loop (d i) 0 (by omega)).tie
  rw [← List.range_eq_range'] at go
  have final := BoundedFits.pair (c := fun _ => .pass) (outer.join go (by omega))
    (show DeckCap cap (pile 0 (.fork full (state i 0)) r) from fun a => by
      have h := (baseCap.pile 0 (.fork full (state i 0))) a
      dsimp only [Tree.count] at h; dsimp only [cap]; omega)
    (show 1 ≤ depth by omega)
  refine final.mono ?_ le_rfl le_rfl
  have fc := Task.foldCost_add (table i) (cost i) (List.range (d i))
  change foldCost wc _ = _ + full.count at fc
  dsimp only
  rw [← FixedPoint.indexedFoldCost (fun j => cost i j + (table i j).count)]
  change _ ≤ (120+C)*(foldCost wc _ + 1)
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

end Space

end NearSquareRoot
end Computability
end OAI
