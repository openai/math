import OAI.Computability.VPVNP.IncidenceColumn

/-!
# One pass of the incidence-matrix machine

A row scan reads the tagged column records from right to left and finishes on the zero
end marker. Exactly one selected incidence advances the search to the next row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace IncidenceMachine

open UniversalMachine TableCompiler QueryTape

variable {m : ℕ}

/-- A zero after the column tags terminates each scan. -/
def rowBits (cs : List (Column m)) : Word := cs.flatMap columnBits ++ [false]

/-- Count the selected columns incident with the specified row. -/
def rowHits (r : Fin m) (cs : List (Column m)) : ℕ :=
  cs.countP (fun c => c.1 && c.2 r)

private theorem readsLeft_split {input a b : Word} {base : ℕ}
    (h : ReadsLeft input base (a ++ b)) :
    ReadsLeft input (base + b.length) a ∧ ReadsLeft input base b := by
  constructor
  · intro i hi
    have hs := h i (by simp; omega)
    simpa only [List.getElem_append_left hi, List.length_append,
      show base + (a.length + b.length) = base + b.length + a.length by omega] using hs
  · intro i hi
    have hs := h (a.length + i) (by simp [hi])
    rw [List.getElem_append_right (by omega)] at hs
    simpa only [List.length_append, Nat.add_sub_cancel_left,
      show base + (a.length + b.length) - (a.length + i) = base + b.length - i by omega] using hs

private theorem readsLeft_reverse (pre bits post : Word) :
    ReadsLeft (pre ++ false :: bits.reverse ++ post) pre.length bits := by
  intro i hi
  let pos := pre.length + bits.length - i
  have hleft : pos < (pre ++ false :: bits.reverse).length := by simp [pos]; omega
  rw [head_atPosition_of_lt _ _ (by simp [pos] at *; omega),
    List.getElem_append_left hleft, List.getElem_append_right (by dsimp [pos] at *; omega)]
  have hoff : pre.length + bits.length - i - pre.length = (bits.length - 1 - i) + 1 := by omega
  simp only [pos, hoff, List.getElem_cons_succ, List.getElem_reverse,
    show bits.length - 1 - (bits.length - 1 - i) = i by omega]

private theorem endMarker (pre bits post : Word) :
    (atPosition (pre ++ false :: bits.reverse ++ post) pre.length).head = 1 := by
  have hlt : pre.length < (pre ++ false :: bits.reverse).length := by simp
  rw [head_atPosition_of_lt _ _ (by simp),
    List.getElem_append_left hlt, List.getElem_append_right (Nat.le_refl _)]
  simp

private theorem runColumns (input : Word) (base : ℕ) (r : Fin m) (cs : List (Column m))
    (n fuel : ℕ) (h : ReadsLeft input base (cs.flatMap columnBits)) :
    countAt m input (base + (cs.flatMap columnBits).length) (.tag r (tally n))
        ((cs.flatMap columnBits).length + fuel) =
      countAt m input base (.tag r (tally (n + rowHits r cs))) fuel := by
  induction cs generalizing n with
  | nil => simp [rowHits]
  | cons c cs ih =>
    rw [List.flatMap_cons] at h ⊢
    obtain ⟨hcol, hrest⟩ := readsLeft_split h
    rw [List.length_append, show base + ((columnBits c).length + (cs.flatMap columnBits).length) =
      (base + (cs.flatMap columnBits).length) + (columnBits c).length by omega, Nat.add_assoc (columnBits c).length (cs.flatMap columnBits).length fuel]
    rw [runColumn input _ c r n _ hcol, ih _ hrest]
    congr 3
    simp only [rowHits, List.countP_cons]
    cases c.1 && c.2 r <;> simp
    omega

/-- One row consumes one transition per serialized bit, including the terminating zero. -/
theorem runRow (pre post : Word) (cs : List (Column m)) (r : Fin m) (fuel : ℕ) :
    let input := pre ++ (rowBits cs).reverse ++ post
    countAt m input (pre.length + (rowBits cs).length - 1) (.tag r (tally 0))
        ((rowBits cs).length + fuel) =
      if rowHits r cs = 1 then countAt m input pre.length (.search r.succ) fuel else 0 := by
  dsimp only
  simp only [rowBits, List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append,
    List.length_append, List.length_singleton]
  let bits := cs.flatMap columnBits
  have h := runColumns (pre ++ false :: bits.reverse ++ post) pre.length r cs 0 (fuel + 1)
    (readsLeft_reverse pre bits post)
  simp only [Nat.zero_add] at h
  rw [show pre.length + ((cs.flatMap columnBits).length + 1) - 1 =
        pre.length + (cs.flatMap columnBits).length by omega,
      show (cs.flatMap columnBits).length + 1 + fuel =
        (cs.flatMap columnBits).length + (fuel + 1) by omega, h, countAt_step]
  rw [endMarker pre bits post]
  by_cases hhit : rowHits r cs = 1
  · simp [command, hhit, tally, countAt, moveTape, bits]
  · simp [command, hhit, tally_eq_one_iff]

end IncidenceMachine

end VPVNP
end Computability
end OAI
