import OAI.Computability.MultitapeWeakETH.MotifSupply

/-! # Checking selected payload totals and locating the fields of one copy -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP MotifSelector StackInterpreter
open scoped Classical
noncomputable section

variable {E S : Type} [Fintype E] [Fintype S] (w : S → E → ℕ)

def widths (e : E) (ts : List (Label S)) := ts.map fun t => tally (w t.val e)

omit [Fintype E] in
theorem widths_poly (e : E) : Poly (widths w e) := Poly.maps _ (Easy.finite _).poly

def start (e : E) (q : List (Label S) × Tally) := (widths w e ((cutLists q.swap).1)).flatten

omit [Fintype E] in
theorem start_poly (e : E) : Poly (start w e) :=
  ((easy_cut Easy.exchange).fstCompose.poly.compose (widths_poly w e)).compose Easy.flatten.poly

omit [Fintype E] [Fintype S] in
theorem start_eq {u : ℕ} (seq : Fin u → S) (e : E) (i : Fin u) :
    start w e (List.ofFn (fun l => Label.mk (seq l)),tally i.val) = tally (MotifEntry.offset (fun l => w (seq l) e) i) := by
  unfold start widths
  rw [← recover_tally (_ : List Tally).flatten]
  simp only [Prod.swap,cutLists,tally_length,← Fin.ofFn_take_eq_take_ofFn i.isLt.le,List.map_ofFn,
    Function.comp_def,List.length_flatten,List.sum_ofFn,Fin.take,MotifEntry.offset]

def totals (q : List Tally × List (Label S)) : Bool :=
  decide (∀ e : E, (fetch [] e q.1).length = (widths w e q.2).flatten.length)

theorem totals_poly : Poly (totals w) := by
  have each (e : E) := ((Easy.fst.poly.compose (fetch_poly ([] : Tally) e)).pair ((Easy.snd.poly.compose (widths_poly w e)).compose Easy.flatten.poly)).compose Iter.linked.poly
  convert all_poly _ each using 1
  funext q
  apply Bool.eq_iff_iff.mpr
  simp [totals]

omit [Fintype S] in
theorem totals_eq {u : ℕ} (seq : Fin u → S) (v : E → ℕ) :
    totals w (bank (fun e => tally (v e)),List.ofFn (fun i => Label.mk (seq i))) =
      decide (∀ e, v e = totalWidth w seq e) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  simp only [totals,decide_eq_true_eq,fetch_bank,tally_length,widths,List.map_ofFn,Function.comp_def,List.length_flatten,List.sum_ofFn,totalWidth]

end
end OAI.Computability.MultitapeWeakETH.MotifFields
