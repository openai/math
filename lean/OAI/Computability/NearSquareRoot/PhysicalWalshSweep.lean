import OAI.Computability.NearSquareRoot.PhysicalWalshSequence
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceHeaders
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Executing the generated base-digit agenda

The complete list of recursive piece headers is constructed from the compact
width counters on tape. The integer clock counts the occurrences of every
recursion depth with exactly its base-`A` digit multiplicity.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space PhysicalWalshNode

/-- Total field for indexing a finite physical schedule. -/
def levelAt (l : List Shape) (j : ℕ) := (l[j]?).elim 0 Shape.level

@[simp] theorem levelAt_fin (l : List Shape) (j : Fin l.length) : levelAt l j = (l.get j).level := by
  simp [levelAt]

theorem range_levels (l : List Shape) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.range l.length, f (levelAt l j) = (l.map (fun u => f u.level)).sum := by
  rw [← Fin.sum_univ_eq_sum_range, ← List.sum_ofFn]
  simp only [levelAt_fin]
  change (List.ofFn ((fun u : Shape => f u.level) ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem schedule_sum_nat {A W : ℕ} (hA : 1 < A) (hW : 0 < W) (k s w : ℕ) (f : ℕ → ℕ) :
    ((schedule A W hW k s w).map (fun p => f p.level)).sum =
      ∑ j : Fin (walshPieceDigits A s).length, (walshPieceDigits A s).get j * f j := by
  simp only [schedule,List.map_flatten,List.sum_flatten,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    shape, Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,digit_eq_get hA,Nat.cast_id]

/-- The emitted controller and its construction both fit the same polynomial. -/
private theorem headerBudget (A W : ℕ) (hA : 1 < A) (hW : 0 < W) : ∃ d C : ℕ,
    let t (p : ℕ × ℕ × ℕ) := C*(p.1+p.2.1+p.2.2+1)^d
    let out (p : ℕ × ℕ × ℕ) := (schedule A W hW p.1 p.2.1 p.2.2).map (Header.wire A)
    BoundedTask t t (fun p => send ((tally p.1,tally p.2.1),tally (p.2.2+1))) (send ∘ out) ∧
      ∀ p, size (out p) ≤ t p := by
  obtain ⟨d,C,h⟩ := headersTask A W hA hW
  obtain ⟨J,hJ⟩ := h.endpointSize
  refine ⟨d,(J+1)*(C+1),h.mono (fun p => ?_) (fun p => ?_),fun p => ?_⟩
  · exact Nat.mul_le_mul_right _ ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
  · exact Nat.mul_le_mul_right _ ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
  · let z := (p.1+p.2.1+p.2.2+1)^d
    have hz : 0 < z := Nat.pow_pos (by omega)
    apply ((Nat.le_max_right _ _).trans (hJ p)).trans
    change J*(C*z+1) ≤ (J+1)*(C+1)*z
    rw [Nat.mul_assoc,Nat.succ_mul C]
    exact Nat.mul_le_mul (Nat.le_succ _) (by omega)

variable {I D : Type} [Codec D]

/-- Emit the ordered agenda in the first field and then process the stored data. -/
noncomputable def agendaCmd (D : Type) [Codec D] (header step : Cmd) :=
  (KernelEffectiveFamily.leftCmd header).join (Sequence.walkCmd Header.Wire D step)

/-- The even-piece pass begins with only the three width counters and its
flat array. `piece` is one uniform command on the actual reached records. -/
theorem generatedSweepWith {A W : ℕ} {header step : Cmd} (d C : ℕ) (hA : 1 < A) (hW : 0 < W)
    (headerRun : EffectiveBoundedTask.Runs header
      (fun p : ℕ×ℕ×ℕ => C*(p.1+p.2.1+p.2.2+1)^d) (fun p => C*(p.1+p.2.1+p.2.2+1)^d)
      (fun p => send ((tally p.1,tally p.2.1),tally (p.2.2+1)))
      (fun p => send ((schedule A W hW p.1 p.2.1 p.2.2).map (Header.wire A))))
    (hs : ∀ p : ℕ×ℕ×ℕ, size ((schedule A W hW p.1 p.2.1 p.2.2).map (Header.wire A)) ≤
      C*(p.1+p.2.1+p.2.2+1)^d)
    (k s w : I → ℕ) (v : I → ℕ → D) (t : I → ℕ → ℕ) (space : I → ℕ) :
    let L i := schedule A W hW (k i) (s i) (w i)
    (∀ i j, j ≤ (L i).length → size (v i j) ≤ space i) →
    EffectiveBoundedTask.Runs step (fun z : (i : I) × Fin (L i).length => t z.1 ((L z.1).get z.2).level)
        (fun z => space z.1) (fun z => send (Header.wire A ((L z.1).get z.2),v z.1 z.2))
        (fun z => send (Header.wire A ((L z.1).get z.2),v z.1 (z.2.val+1))) →
    let G i := C*(k i+s i+w i+1)^d+space i
      let clock i := 2*(G i+1) + ∑ j : Fin (walshPieceDigits A (s i)).length,
        (walshPieceDigits A (s i)).get j * (t i j+G i+1)
      EffectiveBoundedTask.Runs (agendaCmd D header step) clock G (fun i => send (((tally (k i),tally (s i)),tally (w i+1)),v i 0))
        (fun i => send (v i (L i).length)) := by
  intro L fit piece G clock
  let wires i := (L i).map (Header.wire A)
  let T i j := t i (levelAt (L i) j)
  have prep := AgendaOps.left (headerRun.on fun i => (k i,s i,w i)) (fun i => send (v i 0))
  have hp : EffectiveBoundedTask.Runs step (fun z : (i : I) × Fin (wires i).length => T z.1 z.2)
      (fun z => space z.1) (fun z => send ((wires z.1).get z.2,v z.1 z.2))
      (fun z => send ((wires z.1).get z.2,v z.1 (z.2.val+1))) := by
    let idx (z : (i : I) × Fin (wires i).length) : (i : I) × Fin (L i).length :=
      ⟨z.1,⟨z.2.val,by simpa only [wires,List.length_map] using z.2.isLt⟩⟩
    apply AgendaOps.conform (piece.on idx) _ (fun _ => rfl) _ _
    · intro z
      dsimp only [Function.comp_apply]
      rw [show T z.1 z.2 = t z.1 (levelAt (L z.1) (idx z).2) from rfl,levelAt_fin]
    all_goals intro z; simp only [Function.comp_apply,idx,wires,List.get_eq_getElem,List.getElem_map]
  have run := Sequence.walkWith wires v T space (by simpa only [wires,List.length_map] using fit) hp
  simp only [wires,List.length_map] at run
  have both := AgendaOps.compose prep run
  apply both.mono (fun i => ?_) (fun i => ?_)
  · let a := C*(k i+s i+w i+1)^d
    have sizeList : size (wires i) ≤ a := hs (k i,s i,w i)
    have g : size (wires i)+space i ≤ G i := Nat.add_le_add_right sizeList _
    change a+(size (wires i)+space i+1+∑ j ∈ Finset.range (L i).length, (T i j+(size (wires i)+space i)+1)) ≤ _
    have sumBound := Finset.sum_le_sum (s := Finset.range (L i).length) (fun j _ =>
      Nat.add_le_add_right (Nat.add_le_add_left g (T i j)) 1)
    have reduction := (range_levels (L i) (fun j => t i j+G i+1)).trans (schedule_sum_nat hA hW (k i) (s i) (w i) (fun j => t i j+G i+1))
    change (∑ j ∈ Finset.range (L i).length, (T i j+G i+1)) = _ at reduction
    rw [reduction] at sumBound
    have ha : a ≤ G i := Nat.le_add_right ..
    dsimp only [clock]
    omega
  · have hf := fit i 0 (Nat.zero_le _)
    exact max_le (Nat.add_le_add_left hf _) (Nat.add_le_add_right (hs (k i,s i,w i)) _)

theorem generatedSweep {A W : ℕ} (hA : 1 < A) (hW : 0 < W)
    (k s w : I → ℕ) (v : I → ℕ → D) (t : I → ℕ → ℕ) (space : I → ℕ) :
    let L i := schedule A W hW (k i) (s i) (w i)
    (∀ i j, j ≤ (L i).length → size (v i j) ≤ space i) →
    BoundedTask (fun z : (i : I) × Fin (L i).length => t z.1 ((L z.1).get z.2).level)
        (fun z => space z.1) (fun z => send (Header.wire A ((L z.1).get z.2),v z.1 z.2))
        (fun z => send (Header.wire A ((L z.1).get z.2),v z.1 (z.2.val+1))) →
    ∃ d C : ℕ,
      let G i := C*(k i+s i+w i+1)^d+space i
      let clock i := 2*(G i+1) + ∑ j : Fin (walshPieceDigits A (s i)).length,
        (walshPieceDigits A (s i)).get j * (t i j+G i+1)
      BoundedTask clock G (fun i => send (((tally (k i),tally (s i)),tally (w i+1)),v i 0))
        (fun i => send (v i (L i).length)) := by
  intro L fit piece
  obtain ⟨step,stepRun⟩ := piece
  obtain ⟨d,C,⟨header,headerRun⟩,hs⟩ := headerBudget A W hA hW
  refine ⟨d,C,?_⟩
  exact (generatedSweepWith (header:=header) (step:=step) d C hA hW headerRun hs k s w v t space fit stepRun).task

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
