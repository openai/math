import OAI.Computability.NearSquareRoot.CRTControlledReserveShort
import OAI.Computability.NearSquareRoot.CRTControlledReserveSmallTape
import OAI.Computability.NearSquareRoot.CRTControlledFlatSwapKey

/-! # Position exchanges for a permutation of bounded width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveSmall

open IntegerMultiplication IntegerMultiplication.Code

variable {k : ℕ}

/-- One exchange for each transposition, in increasing order of its smaller endpoint. -/
def moves (p : Equiv.Perm (Fin k)) : List (Fin k × Fin k) :=
  (ReserveShort.lowerList p).map (fun j => (j, p j))

theorem moves_length (p : Equiv.Perm (Fin k)) : (moves p).length ≤ k := by
  simpa [moves, ReserveShort.lowerList] using
    (List.length_filter_le (fun j : Fin k => decide (j < p j)) (List.finRange k))

theorem moves_distinct (p : Equiv.Perm (Fin k)) :
    ∀ z ∈ moves p, z.1 ≠ z.2 := by
  rintro z hz
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
  exact ne_of_lt (of_decide_eq_true (List.mem_filter.mp hj).2 : j < p j)

/-- No endpoint occurs in two different exchanges of the same matching. -/
theorem moves_disjoint (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    (moves p).Pairwise (fun a b => a.1 ≠ b.1 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1 ∧ a.2 ≠ b.2) := by
  rw [moves, List.pairwise_map]
  have nodup : (ReserveShort.lowerList p).Nodup := (List.nodup_finRange _).filter _
  apply nodup.pairwise_of_forall_ne
  intro a ha b hb ne
  have al : a < p a := of_decide_eq_true (List.mem_filter.mp ha).2
  have bl : b < p b := of_decide_eq_true (List.mem_filter.mp hb).2
  change a ≠ b ∧ a ≠ p b ∧ p a ≠ b ∧ p a ≠ p b
  refine ⟨ne, ?_, ?_, fun h => ne (p.injective h)⟩
  · intro e
    rw [e, hp] at al
    exact (not_lt_of_ge al.le) bl
  · intro e
    rw [← e, hp] at bl
    exact (not_lt_of_ge bl.le) al

private theorem partial_moves (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (l : List (Fin k)) (hn : l.Nodup) (lower : ∀ j ∈ l, j < p j) (x : Fin k) :
    positionExchanges (l.map (fun j => (j,p j))) x = if min x (p x) ∈ l then p x else x := by
  induction l with
  | nil => simp [positionExchanges]
  | cons b bs ih =>
    obtain ⟨fresh, nodup⟩ := List.nodup_cons.mp hn
    have hb := lower b (List.mem_cons_self ..)
    have chi := ih nodup (fun j hj => lower j (List.mem_cons_of_mem _ hj))
    change Equiv.swap b (p b) (positionExchanges (bs.map _) x) = _
    rw [chi]
    have hit : min x (p x) = b ↔ x = b ∨ x = p b := by
      constructor
      · intro e
        rcases min_choice x (p x) with h | h
        · exact Or.inl (h.symm.trans e)
        · exact Or.inr ((hp x).symm.trans (congrArg p (h.symm.trans e)))
      · rintro (rfl | rfl)
        · exact min_eq_left hb.le
        · rw [hp, min_eq_right hb.le]
    by_cases hh : min x (p x) = b
    · simp only [hh, fresh, List.mem_cons_self, ↓reduceIte]
      rcases hit.mp hh with rfl | rfl
      · exact Equiv.swap_apply_left ..
      · rw [Equiv.swap_apply_right, hp]
    · obtain ⟨hx, hxb⟩ := not_or.mp (mt hit.mpr hh)
      have hpx : p x ≠ b := fun h => hxb ((hp x).symm.trans (congrArg p h))
      have hpxb : p x ≠ p b := fun h => hx (p.injective h)
      simp only [List.mem_cons, hh, false_or]
      split_ifs <;> exact Equiv.swap_apply_of_ne_of_ne (by assumption) (by assumption)

theorem moves_value (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    positionExchanges (moves p) = p := by
  apply Equiv.ext
  intro x
  have nodup : (ReserveShort.lowerList p).Nodup := (List.nodup_finRange _).filter _
  have lower : ∀ j ∈ ReserveShort.lowerList p, j < p j :=
    fun j hj => of_decide_eq_true (List.mem_filter.mp hj).2
  rw [moves, partial_moves p hp _ nodup lower]
  by_cases eq : x = p x
  · split_ifs <;> first | rfl | exact eq
  · have h : min x (p x) ∈ ReserveShort.lowerList p := by
      rcases lt_or_gt_of_ne eq with h | h
      · simp [ReserveShort.lowerList, min_eq_left h.le, h]
      · simp [ReserveShort.lowerList, min_eq_right h.le, hp x, h]
    simp [h]

/-- The last exchange in the list acts first in the position permutation. -/
def fullMoves (p : Equiv.Perm (Fin k)) :=
  moves (Reflections.second p) ++ moves (Reflections.first p)

theorem fullMoves_length (p : Equiv.Perm (Fin k)) : (fullMoves p).length ≤ 2*k := by
  rw [fullMoves, List.length_append, two_mul]
  exact Nat.add_le_add (moves_length _) (moves_length _)

theorem fullMoves_distinct (p : Equiv.Perm (Fin k)) : ∀ z ∈ fullMoves p, z.1 ≠ z.2 := by
  intro z hz
  exact (List.mem_append.mp hz).elim (moves_distinct _ z) (moves_distinct _ z)

theorem fullMoves_value (p : Equiv.Perm (Fin k)) : positionExchanges (fullMoves p) = p := by
  rw [fullMoves, ReserveProgram.exchange_append,
    moves_value (Reflections.first p) (forwardMirror_involutive p),
    moves_value (Reflections.second p) (shiftedMirror_involutive p), Reflections.factor]

/-- Prepare both width and swap endpoints from the original unary permutation descriptor. -/
def fullHeader (t : Reflections.Table) := (ruler t, compileBoth t)

@[fun_prop] theorem poly_fullHeader : Poly fullHeader :=
  (Easy.ruler Easy.identity).poly.pair poly_compileBoth

theorem fullHeader_spec (p : Equiv.Perm (Fin k)) :
    fullHeader (Reflections.table p) = flatSwapInput k (fullMoves p) := by
  have width : ruler (Reflections.table p) = tally k := by
    rw [← recover_tally (ruler _), ruler_length, Reflections.table, List.length_ofFn]
  simp only [fullHeader, width, compileBoth_table, compile_table, flatSwapInput, fullMoves,
    List.map_append, moves, ReserveShort.lowerList, ReserveProgram.encodedMoves]
  rfl

end Controlled.ReserveSmall

end NearSquareRoot
end Computability
end OAI
