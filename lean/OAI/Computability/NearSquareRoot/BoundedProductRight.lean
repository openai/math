import OAI.Computability.NearSquareRoot.BoundedProduct

/-!
# Space-certified operations on two encoded fields

A call on the second field parks the first on a work register, runs on the
exposed second field, then restores the first. The two moves scan only the
first field. The caller can have parked data on all the work registers.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication IntegerMultiplication.Code

/-- Removing the top tree preserves the absolute data cap. -/
theorem DeckCap.unpile {cap i : ℕ} {x : Tree} {r : Deck}
    (h : DeckCap cap (Code.pile i x r)) : DeckCap cap r := by
  intro j
  have hj := h j
  by_cases eq : j = i
  · subst j
    rw [letters_here, List.length_append] at hj
    omega
  · rwa [pile_far _ _ (Ne.symm eq)] at hj

/-- A move has a clock bounded solely by the size of the tree transferred.
The surrounding data remains available on its own registers. -/
theorem BoundedFits.move {i j u base cap depth : ℕ} (hi : i ≠ u) (hj : u ≠ j)
    (x : Tree) (env : Env) (r : Deck) (start : DeckCap base (pile i x r))
    (room : base + 42 * x.count ≤ cap) (ret : 42 * x.count ≤ depth) :
    BoundedFits env (Code.move i j u) (pile i x r) (pile j x r) (42 * x.count) cap depth :=
  BoundedFits.of_fits (fits_move hi hj x env r)
    (fun l => (Nat.add_le_add_right (start l) _).trans room) ret

/-- Apply a bounded task to the second field. Only the parked first field is
scanned during the two moves at the call boundary. -/
theorem BoundedTask.right {I : Type*} {time space : I → ℕ} {input output : I → Tree}
    (h : BoundedTask time space input output) (spectator : I → Tree) :
    BoundedTask (fun i => (spectator i).count + time i) (fun i => space i + (spectator i).count)
      (fun i => .fork (spectator i) (input i)) (fun i => .fork (spectator i) (output i)) := by
  obtain ⟨cmd, C, hc⟩ := h
  refine ⟨splitRoot 0 (fun _ => .pass)
    ((Code.move 0 1 2).join (cmd.join ((Code.move 1 0 2).join (pack 0)))), C + 100, ?_⟩
  intro i env r base hr
  let z := spectator i
  let subcap := base + z.count + C * (space i + 1)
  let depth := (C + 100) * (space i + z.count + 1)
  let cap := base + depth
  have sub := hc i env (pile 1 z r) _ ((show DeckCap base r from hr).pile 1 z)
  change BoundedFits env cmd _ _ _ subcap _ at sub
  have run := sub.choose_spec.2
  have initial : DeckCap subcap (pile 0 (input i) (pile 1 z r)) := run.start
  have finalCap : DeckCap subcap (pile 0 (output i) (pile 1 z r)) := run.finish
  have inputCap := initial
  rw [pile_comm 0 _ r 1 _ (by decide)] at inputCap
  have outputCap := finalCap
  rw [pile_comm 0 _ r 1 _ (by decide)] at outputCap
  have movedCap := inputCap.unpile.pile 0 z
  have backCap := outputCap.unpile.pile 0 z
  have room : subcap + z.count + 42 * z.count + 1 ≤ cap := by
    dsimp only [cap, depth, subcap]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have hrmove : 42 * z.count + 1 ≤ depth := by
    dsimp only [depth]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have hrsub : C * (space i + 1) + 1 ≤ depth := by
    dsimp only [depth]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have out := BoundedFits.move (i := 0) (j := 1) (u := 2) (by decide) (by decide) z env
    (pile 0 (input i) r) movedCap (cap := cap) (by omega) (depth := 42*z.count) le_rfl
  have back := BoundedFits.move (i := 1) (j := 0) (u := 2) (by decide) (by decide) z env
    (pile 0 (output i) r) outputCap (cap := cap) (by omega) (depth := 42*z.count) le_rfl
  rw [pile_comm 1 _ r 0 _ (by decide)] at out back
  have last := BoundedFits.pack z (output i) r 0 env (depth := depth) (backCap.coverFork.mono (by omega : _ ≤ cap))
  have first := sub.mono le_rfl (by omega : subcap ≤ cap) le_rfl
  have joined := out.join (first.join (back.join last hrmove) hrsub) hrmove
  have all := BoundedFits.pair (c := fun _ => .pass) joined
    (movedCap.coverFork.mono (by omega)) (by omega)
  apply all.mono _ le_rfl le_rfl
  dsimp only [z]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

namespace BoundedTask

/-- Exchange the two subtrees, with linear time and live space in their combined
size. The P192 program moves both subtrees through its work registers. -/
theorem swap {I : Type*} (f g : I → Tree) :
    BoundedTask (fun i => (f i).count + (g i).count) (fun i => (f i).count + (g i).count)
      (fun i => .fork (f i) (g i)) (fun i => .fork (g i) (f i)) := by
  apply (of_time (Task.exchange f g)).bound 1 2
  · intro i
    simp
  · intro i
    simp [Tree.count]
    omega

end BoundedTask

end Space

end NearSquareRoot
end Computability
end OAI
