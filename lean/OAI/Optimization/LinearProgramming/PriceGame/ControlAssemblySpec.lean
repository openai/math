import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyValue

/-! The dynamic bit-stack assembly traverses visibly encoded arrays. Its prices,
integer scores and chronological probe log agree with the indexed trial operation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open Trial TrialExecution Moment States.Mass

private theorem take_as_rows {A : Type*} [Inhabited A] (xs : List A) (n : ℕ) (hn : n ≤ xs.length) :
    xs.take n = List.ofFn (fun j : Fin n => atD xs j.val) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hn]
  · intro i hi hj
    have his : i < xs.length := (show i < n by simpa using hj).trans_le hn
    simp [atD, his]

private theorem all_as_rows {A : Type*} [Inhabited A] (xs : List A) (n : ℕ) (hn : xs.length = n) :
    xs = List.ofFn (fun j : Fin n => atD xs j.val) := by
  simpa only [← hn, List.take_length] using take_as_rows xs n hn.ge

private theorem drop_as_rows {A : Type*} [Inhabited A] (xs : List A) (r : ℕ) (h : xs.length = 2*r) :
    xs.drop r = List.ofFn (fun j : Fin r => atD xs (r+j.val)) := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn, h]; omega
  · intro i hi hj
    have hir : i < r := by simpa using hj
    have hs : r+i < xs.length := by omega
    simp [atD, hs]

private theorem ofFn_halves {A : Type*} {r : ℕ} (f : Fin (2*r) → A) :
    List.ofFn f = (List.ofFn fun i : Fin r => f (probeIndex i)) ++
      (List.ofFn fun i : Fin r => f (finalIndex i)) := by
  let g : Fin (r+r) → A := fun i => f ⟨i.val, by omega⟩
  have eqg : List.ofFn f = List.ofFn g := by
    apply List.ext_getElem
    · simp [two_mul]
    · intro i hi hj; simp [g]
  rw [eqg, List.ofFn_add]
  rfl

private theorem median_congr_width {n m : ℕ} (h : n = m) (f : Fin n → ℚ) (g : Fin m → ℚ)
    (hg : ∀ i, f i = g (i.cast h)) : median f = median g := by
  subst m
  exact congrArg median (funext hg)

private theorem medianValue_ofFn {n : ℕ} (f : Fin n → ℚ) : medianValue (List.ofFn f) = median f := by
  unfold medianValue
  apply median_congr_width (List.length_ofFn (f := f))
  intro i
  change (List.ofFn f)[i.val] = f (Fin.cast _ i)
  rw [List.getElem_ofFn]
  rfl

theorem priceAt_eq_final_median (r : ℕ) (x : AssemblyFrame) (hc : x.calls.length = 2*r) (i : ℕ) :
    priceAt r x i = median fun j : Fin r => atD (atD x.calls (finalIndex j).val).mapped i := by
  simp only [priceAt, finalRows, drop_as_rows x.calls r hc, List.map_ofFn, medianValue_ofFn]
  rfl

private theorem scoreAt_eq_indexed (r : ℕ) (x : AssemblyFrame) (hc : x.calls.length = 2*r)
    (e : Fin x.experts.length) :
    scoreAt r x e.val =
      if (atD x.experts e.val).level = x.input.level then
        rationalScore scaleQ sigmaQ (meanQ r (fun t =>
          probeAt (fun j : Fin r => fun z : Fin x.experts.length =>
            atD (atD x.calls (probeIndex j).val).gains z.val) t e))
      else
        rationalScore scaleQ sigmaQ (meanQ (2*r) (fun t =>
          (probeAt (fun j : Fin (2*r) => fun z : Fin x.experts.length =>
            atD (atD x.calls j.val).child.scores z.val) t e : ℕ))) := by
  have hle : r ≤ x.calls.length := by omega
  by_cases h : (atD x.experts e.val).level = x.input.level
  · simp only [scoreAt, ite_eq_left h, take_as_rows x.calls r hle, List.map_ofFn, List.sum_ofFn,
      meanQ, ← Fin.sum_univ_eq_sum_range, probeAt_fin, Function.comp_apply, probeIndex]
  · simp only [scoreAt, ite_eq_right h, meanQ, ← Fin.sum_univ_eq_sum_range, probeAt_fin]
    have hs := congrArg (fun xs : List Completed => (xs.map (fun c => ((atD c.child.scores e.val : ℕ) : ℚ))).sum)
      (all_as_rows x.calls (2*r) hc)
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using
      congrArg (fun n : ℚ => rationalScore scaleQ sigmaQ (n / ((2*r : ℕ) : ℚ))) hs

private theorem frameLog_eq_indexed (r : ℕ) (x : AssemblyFrame) (hc : x.calls.length = 2*r) :
    frameLog r x = (List.ofFn (fun j : Fin (2*r) =>
      let c := atD x.calls j.val
      if j.val < r then ⟨x.input.level, c.baseline, x.input.history⟩ :: c.child.log
      else c.child.log)).flatten := by
  have hle : r ≤ x.calls.length := by omega
  rw [ofFn_halves _, List.flatten_append]
  simp only [frameLog, take_as_rows x.calls r hle, drop_as_rows x.calls r hc,
    List.flatMap_def, List.map_ofFn, Function.comp_def, probeIndex, finalIndex, Fin.isLt, ite_true,
    Nat.not_lt_of_ge (Nat.le_add_right _ _), ite_false]

/-- The completed-call and coordinate widths are the two length facts required by
the indexed specification. Every field of the packed result is then identical. -/
theorem assembleValue_eq_assemblePacketSized (N r : ℕ) (x : AssemblyFrame)
    (hc : x.calls.length = 2*r) (hw : outputWidth r x = N * 2^x.input.level) :
    assembleValue r x = assemblePacketSized N r x.experts.length x.experts x.input x.calls := by
  apply PackedRound.mk.injEq .. |>.mpr
  refine ⟨?_, ?_, frameLog_eq_indexed r x hc⟩
  · apply List.ext_getElem
    · simp [hw]
    · intro i hi hj
      simpa only [packTable, List.getElem_map, List.getElem_range, List.getElem_ofFn,
        lookupTable, Equiv.apply_symm_apply, atD] using priceAt_eq_final_median r x hc i
  · apply List.ext_getElem
    · simp
    · intro i hi hj
      have hx : i < x.experts.length := by simpa using hi
      simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
        scoreAt_eq_indexed r x hc ⟨i, hx⟩

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
