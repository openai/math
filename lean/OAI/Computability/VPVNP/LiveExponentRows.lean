import OAI.Computability.VPVNP.LiveExponentBuffers

/-!
# The complete first-half exponent phase

After the chosen pair path has supplied all grammar and gadget increments,
the deterministic stage scans the labels in address order. It succeeds
exactly when the outgoing cut contains their sum with the incoming cut.
There is one terminal call and one constant-probe call per encoded bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM
open scoped Classical

variable {w t Z : ℕ}

/-- Clearing the consumed increment words in address order. -/
def clearCounters (pub : Fin 5 → Word w) (rows : List (Fin t)) (m : Memory w) : Memory w :=
  rows.foldl (fun mem a => writeMemory mem (counterAddr pub a) 0) m

/-- Exact report sequence of all data calls. -/
def rowsReports (pub : Fin 5 → Word w) (Z : ℕ) : List (Fin t) → Memory w → List (Report w)
  | [], _ => []
  | a :: rest, m => rowReports pub Z (a.val*Z) m ++
    rowsReports pub Z rest (writeMemory m (counterAddr pub a) 0)

private theorem run_rows_aux {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z) (hw : 2 ≤ w)
    {x y : Fin t → Word Z} (inc : Fin t → Word w) (hc : ∀ i, (inc i).val+1 < 2^w)
    (bits : Fin t → List (List Bool)) (hwidth : ∀ i, (bits i).length = Z) (f : ℕ)
    (rows : List (Fin t)) (start : ℕ) (m : Memory w) (v : BufferValues pub x y m)
    (hmap : rows.map Fin.val = List.range' start rows.length) (huniq : rows.Nodup)
    (hi : ∀ a ∈ rows, m (counterAddr pub a).val = inc a) (tail : List (List Bool)) :
    let P := (digitTemplate.instantiate w pub).program
    runSegment P (f+31) (some (atPos (start*Z))) m (rows.flatMap bits ++ tail) =
      if ∀ a ∈ rows, (y a).val = (x a).val+(inc a).val ∧ bits a = List.replicate Z [] then
        (runSegment P (f+31) (some (atPos ((start+rows.length)*Z))) (clearCounters pub rows m)
          tail).map (rowsReports pub Z rows m ++ ·)
      else none := by
  dsimp only
  induction rows generalizing start m with
  | nil => simp [clearCounters, rowsReports]
  | cons a rows ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hmap
    obtain ⟨rfl, hmap⟩ := hmap
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp huniq
    have haddr := hi a (List.mem_cons_self ..)
    let m' := writeMemory m (counterAddr pub a) 0
    have hh : ∀ b ∈ rows, m' (counterAddr pub b).val = inc b := by
      intro b hb
      have hne : (counterAddr pub b).val ≠ (counterAddr pub a).val := by
        intro e
        exact hnot ((counterAddr_injective L hZ (Fin.ext e)) ▸ hb)
      change writeMemory m (counterAddr pub a) 0 (counterAddr pub b).val = inc b
      rw [writeMemory, ite_eq_right hne]
      exact hi b (List.mem_cons_of_mem _ hb)
    have hrow := run_wordRow L hZ hw v a (haddr ▸ hc a) (bits a) (hwidth a)
      (rows.flatMap bits ++ tail) f
    rw [List.flatMap_cons, List.append_assoc, hrow, haddr]
    have htail := ih (a.val+1) m' (v.write_counter L a 0) hmap hn hh
    simp only [List.forall_mem_cons]
    by_cases hgood : (y a).val = (x a).val+(inc a).val ∧ bits a = List.replicate Z []
    · rw [ite_eq_left hgood]
      rw [htail]
      simp only [hgood, true_and]
      by_cases ht : ∀ b ∈ rows, (y b).val = (x b).val+(inc b).val ∧ bits b = List.replicate Z []
      · rw [ite_eq_left ht, ite_eq_left ht, Option.map_map]
        have he : a.val+(a::rows).length = a.val+1+rows.length := by simp; omega
        rw [he]
        simp [Function.comp_def, rowsReports, clearCounters, m', List.append_assoc]
      · simp [ht]
    · simp [hgood]

/-- Exact native execution of all data calls, with any succeeding call sequence.
The first stage cursor is zero and the final one equals the total digit count. -/
theorem run_rows {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z) (hw : 2 ≤ w)
    {x y : Fin t → Word Z} {m : Memory w} (v : BufferValues pub x y m)
    (inc : Fin t → Word w) (hi : ∀ a, m (counterAddr pub a).val = inc a)
    (hc : ∀ a, (inc a).val+1 < 2^w) (bits : Fin t → List (List Bool))
    (hwidth : ∀ a, (bits a).length = Z) (tail : List (List Bool)) (f : ℕ) :
    let P := (digitTemplate.instantiate w pub).program
    runSegment P (f+31) (some 0) m ((List.finRange t).flatMap bits ++ tail) =
      if ∀ a, (y a).val = (x a).val+(inc a).val ∧ bits a = List.replicate Z [] then
        (runSegment P (f+31) (some (pub 4)) (clearCounters pub (List.finRange t) m)
          tail).map (rowsReports pub Z (List.finRange t) m ++ ·)
      else none := by
  have hmap : (List.finRange t).map Fin.val = List.range' 0 (List.finRange t).length := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  have he := run_rows_aux L hZ hw inc hc bits hwidth f (List.finRange t) 0 m v hmap
    (List.nodup_finRange t) (fun a _ => hi a) tail
  have hlast : atPos (w := w) (t*Z) = pub 4 := Fin.ext (by rw [← L.size]; exact Nat.mod_eq_of_lt (pub 4).isLt)
  simp only [List.length_finRange, Nat.zero_add] at he
  rw [hlast] at he
  simpa using he

/-- All data calls followed by the unique accepting end call. -/
theorem run_stage {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z) (hw : 2 ≤ w)
    {x y : Fin t → Word Z} {m : Memory w} (v : BufferValues pub x y m)
    (inc : Fin t → Word w) (hi : ∀ a, m (counterAddr pub a).val = inc a)
    (hc : ∀ a, (inc a).val+1 < 2^w) (bits : Fin t → List (List Bool))
    (hwidth : ∀ a, (bits a).length = Z) (last : List Bool) (f : ℕ) :
    let P := (digitTemplate.instantiate w pub).program
    runSegment P (f+31) (some 0) m ((List.finRange t).flatMap bits ++ [last]) =
      if (∀ a, (y a).val = (x a).val+(inc a).val ∧ bits a = List.replicate Z []) ∧ last = [] then
        some (rowsReports pub Z (List.finRange t) m ++ [⟨[.tick,.tick,.tick,.tick],none⟩])
      else none := by
  dsimp only
  rw [run_rows L hZ hw v inc hi hc bits hwidth [last] f]
  by_cases hs : ∀ a, (y a).val = (x a).val+(inc a).val ∧ bits a = List.replicate Z []
  · rw [ite_eq_left hs]
    simp only [runSegment]
    rw [show f+31 = (f+26)+5 by omega, execute_done pub (pub 4) _ last (f+26) rfl]
    by_cases hl : last = []
    · rw [ite_eq_left hl, ite_eq_left ⟨hs,hl⟩]
      rfl
    · rw [ite_eq_right hl, ite_eq_right (fun h => hl h.2)]
      rfl
  · simp [hs]

end LiveExponent

end VPVNP
end Computability
end OAI
