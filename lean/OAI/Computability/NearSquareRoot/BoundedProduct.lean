import OAI.Computability.NearSquareRoot.BoundedBranch

/-! # Calling a bounded task on the first field of a pair -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication IntegerMultiplication.Code

/-- Repack the trees on one stack. The only additional live cell is the pair marker. -/
theorem DeckCap.coverFork {cap i : ℕ} {x y : Tree} {r : Deck}
    (h : DeckCap cap (Code.pile i x (Code.pile i y r))) : DeckCap (cap+1) (Code.pile i (.fork x y) r) := by
  intro j
  have hh := h j
  by_cases eq : j = i
  · subst j
    simp only [letters_here, List.length_append, Tree.spell_length, Tree.count] at *
    omega
  · simp only [pile_far i j (Ne.symm eq)] at *
    omega

/-- Transform the first field in place while retaining the second on the same stack.
The spectator contributes its length to space and only constant work to time. -/
theorem BoundedTask.left {I : Type*} {time space : I → ℕ} {input output : I → Tree}
    (h : BoundedTask time space input output) (spectator : I → Tree) :
    BoundedTask time (fun i => space i + (spectator i).count)
      (fun i => .fork (input i) (spectator i)) (fun i => .fork (output i) (spectator i)) := by
  obtain ⟨cmd,C,hc⟩ := h
  refine ⟨splitRoot 0 (fun _ => .pass) (cmd.join (pack 0)), C+8, ?_⟩
  intro i env r base hr
  let subcap := base + (spectator i).count + C * (space i + 1)
  let depth := (C+8)*(space i + (spectator i).count+1)
  let cap := base + depth
  have sub := hc i env (pile 0 (spectator i) r) _ ((show DeckCap base r from hr).pile 0 _)
  change BoundedFits _ _ _ _ _ subcap _ at sub
  have headroom : subcap + 1 ≤ cap := by
    unfold subcap cap depth
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have ret : C * (space i + 1) + 1 ≤ depth := by
    unfold depth
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have first := sub.mono le_rfl (by omega : subcap ≤ cap) le_rfl
  obtain ⟨_,_,run⟩ := sub
  have initial : DeckCap subcap (pile 0 (input i) (pile 0 (spectator i) r)) := run.start
  have finalCap : DeckCap subcap (pile 0 (output i) (pile 0 (spectator i) r)) := run.finish
  have packRun := BoundedFits.pack (output i) (spectator i) r 0 env (depth := depth)
    (finalCap.coverFork.mono headroom)
  have paired := BoundedFits.pair (c := fun _ => .pass) (first.join packRun ret)
    (initial.coverFork.mono headroom) (by omega)
  refine paired.mono ?_ le_rfl le_rfl
  rw [Nat.add_mul]
  omega

end Space

end NearSquareRoot
end Computability
end OAI
