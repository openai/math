import OAI.Computability.NearSquareRoot.CRTControlledReserveShort
import OAI.Computability.NearSquareRoot.CRTControlledReserveMiddle
import OAI.Computability.NearSquareRoot.CRTControlledReserve

/-! # Four position matchings with reserved high and low address bits -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

variable {k lo hi : ℕ}

theorem reserveMoves_distinct (p : Equiv.Perm (Fin k)) (lo hi : ℕ) (e : Fin k × Fin k)
    (h : e ∈ reserveMoves p lo hi) : e.1 ≠ e.2 := by
  obtain ⟨a,b⟩ := List.of_mem_zip h
  exact fun same => ((mem_misplaced p lo hi _).mp a).2
    (same.symm ▸ ((mem_available p lo hi _).mp b).2)

theorem reservedMatching_involutive (p : Equiv.Perm (Fin k)) (inv : Function.Involutive p)
    (lo hi : ℕ) : Function.Involutive (reservedMatching p lo hi) := by
  intro x
  simp [reservedMatching,inv _]

/-- Data used by one physical stage: first relocate, then act on the interior,
then undo the relocation. Both end widths remain explicit. -/
structure ReserveStage (k lo hi : ℕ) where
  moves : List (Fin k × Fin k)
  inner : Equiv.Perm (Fin (k-lo-hi))

namespace ReserveStage

def ofPerm (p : Equiv.Perm (Fin k)) (fit : lo+hi ≤ k)
    (free : lo+hi ≤ (fixedPositions p).card) : ReserveStage k lo hi where
  moves := reserveMoves p lo hi
  inner := ReserveMiddle.middle (reservedMatching p lo hi) lo hi (reservedMatching_fixed p fit free)

def act (s : ReserveStage k lo hi) (x : Fin k) : Fin k :=
  let move := positionExchanges s.moves
  move (ReserveMiddle.extend lo hi s.inner (move.symm x))

theorem ofPerm_act (p : Equiv.Perm (Fin k)) (fit : lo+hi ≤ k)
    (free : lo+hi ≤ (fixedPositions p).card) (x : Fin k) :
    (ofPerm p fit free).act x = p x := by
  simp only [act, ofPerm, ReserveMiddle.full_action]
  exact Equiv.congr_fun (reserve_reconstruct p lo hi) x

theorem ofPerm_involutive (p : Equiv.Perm (Fin k)) (fit : lo+hi ≤ k)
    (free : lo+hi ≤ (fixedPositions p).card) (inv : Function.Involutive p) :
    Function.Involutive (ofPerm p fit free).inner :=
  ReserveMiddle.middle_involutive _ _ _ _ (reservedMatching_involutive p inv lo hi)

/-- Every original address permutation has exactly four of these stages, all
sharing the same two reserved widths. -/
def four (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2) : List (ReserveStage k lo hi) :=
  (ReserveShort.four p).attach.map fun q =>
    ofPerm q.val (by omega) (cap.trans (ReserveShort.four_short p q.val q.property).2.2)

@[simp] theorem length_four (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2) :
    (four p cap).length = 4 := by simp [four,ReserveShort.four]

theorem four_bounds (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2)
    (s : ReserveStage k lo hi) (hs : s ∈ four p cap) :
    s.moves.length ≤ lo+hi ∧ (∀ e ∈ s.moves, e.1 ≠ e.2) ∧ Function.Involutive s.inner := by
  obtain ⟨⟨q,hq⟩,_,rfl⟩ := List.mem_map.mp hs
  exact ⟨reserveMoves_length q (by omega), reserveMoves_distinct q lo hi,
    ofPerm_involutive q _ _ (ReserveShort.four_short p q hq).1⟩

private theorem fold_apply (l : List (Equiv.Perm (Fin k))) (x : Fin k) :
    l.foldl (fun y e => e y) x = l.foldr Equiv.trans (Equiv.refl _) x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => exact ih (a x)

theorem four_act (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2) (x : Fin k) :
    (four p cap).foldl (fun y s => s.act y) x = p x := by
  simp only [four, List.foldl_map, ofPerm_act]
  change (ReserveShort.four p).attach.foldl (fun y e => e.val y) x = p x
  rw [← List.foldl_map (f := Subtype.val) (g := fun (y : Fin k) (e : Equiv.Perm (Fin k)) => e y),
    List.attach_map_subtype_val, fold_apply, ReserveShort.four_factor]

end ReserveStage
end Controlled

end NearSquareRoot
end Computability
end OAI
