import OAI.Computability.NearSquareRoot.FixedCandidateCRTSweep
import OAI.Computability.NearSquareRoot.FixedCandidateCRTBudget
import OAI.Computability.NearSquareRoot.CRTTableNativePlan
import OAI.Computability.NearSquareRoot.SynchronizedPermutationActiveIDs

/-! # Selecting active CRT targets by physical batch and switch depth -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTDispatch
open IntegerMultiplication Code Staff Strip Carry
open ShortFourier.BatchWord

abbrev IDQuery := (Tally × Tally × Tally) × List Tally

private def qreg (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem numeric {X : Type} [Codec X] (f : X → Tally) (P : Poly f) :
    Realizes (qreg X) (fun x => (f x).length) := by
  change Poly (fun x : X => tally (f x).length)
  simpa only [recover_tally] using P

private def selected (p : IDQuery × Tally) : Bool :=
  let q := p.1
  decide (p.2.length / q.1.1.length = q.1.2.1.length) &&
    decide (q.1.2.2.length < (Iter.pick [] (q.2,p.2)).length)

private theorem selected_poly : Poly selected := by
  let X := IDQuery × Tally
  let band (p : X) : Tally := p.1.1.2.1
  have C := numeric (fun p : X => p.1.1.1) (by fun_prop)
  have I := numeric (fun p : X => p.2) Easy.snd.poly
  have cap : Realizes (qreg X) (fun p => p.1.1.1.length) := C
  have idx : Poly (fun p : X => tally (p.2.length / p.1.1.1.length)) := I.dividing cap
  have eqn := (idx.pair (show Poly band by unfold band; fun_prop)).compose
    (Iter.linked (X := Unit) (Y := Unit)).poly
  have width := (show Easy (fun p : X => (p.1.2,p.2)) by fun_prop).compose (Iter.facile ([] : Tally))
  have test := ((show Easy (fun p : X => p.1.1.2.2) by fun_prop).pair width).compose (Iter.small_easy (X := Unit) (Y := Unit))
  have h : Poly (fun p : X => decide (p.2.length / p.1.1.1.length = p.1.1.2.1.length)) := by
    simpa only [tally_length,band] using eqn
  exact (h.pair test.poly).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

/-- Collect the active block indices from the global width, batch number,
local switch index and width directory, all given in unary. -/
def activeIDs (q : IDQuery) : List Tally :=
  (((Iter.lineup (ruler q.2)).map fun i => (i,selected (q,i))).filter Prod.snd).map Prod.fst

theorem activeIDs_poly : Poly activeIDs := by
  have idx := (Easy.ruler (Easy.snd (X := Tally × Tally × Tally) (Y := List Tally))).poly.compose Iter.poly_line
  have both := (Code.Poly.identity.pair idx).compose
    (Poly.push default [] (Easy.snd.poly.pair selected_poly))
  exact (both.compose (Poly.filter Prod.snd Easy.snd.poly)).compose (Poly.maps _ Easy.fst.poly)

/-- Typed enumeration of exactly the indices executed by the designated batch. -/
def activeBlocks {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).filter fun i => decide (i.val / k = β) && decide (step < w i)

theorem mem_activeBlocks {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) (i : Fin d) :
    i ∈ activeBlocks k β step w ↔ i.val / k = β ∧ step < w i := by
  simp [activeBlocks]

theorem activeBlocks_nodup {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) :
    (activeBlocks k β step w).Nodup := (List.nodup_finRange d).filter _

private theorem collect {X Y : Type} (l : List X) (f : X → Y) (p : X → Bool) :
    ((l.map fun x => (f x,p x)).filter Prod.snd).map Prod.fst = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : p x <;> simp [h,ih]

theorem activeIDs_eq {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) :
    activeIDs ((tally k,tally β,tally step),List.ofFn fun i => tally (w i)) =
      (activeBlocks k β step w).map (fun i => tally i.val) := by
  let q : IDQuery := ((tally k,tally β,tally step),List.ofFn fun i => tally (w i))
  have line : Iter.lineup (ruler q.2) = (List.finRange d).map (fun i => tally i.val) := by
    rw [← recover_tally (ruler q.2),ruler_length]
    change Iter.lineup (tally (List.ofFn (fun i => tally (w i))).length) = _
    rw [List.length_ofFn,Iter.lined,List.ofFn_eq_map]
  change (((Iter.lineup (ruler q.2)).map _).filter _).map _ = _
  rw [line,List.map_map]
  change (((List.finRange d).map (fun i => (tally i.val, selected (q,tally i.val)))).filter Prod.snd).map Prod.fst = _
  rw [collect]
  simp only [q,selected,tally_length,Iter.entry,activeBlocks]

/-- Enumerate the selected blocks by `Fin b`, as required by the batch header and the target layout. -/
def selectBlock {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) :
    Fin (activeBlocks k β step w).length ↪ Fin d :=
  ⟨(activeBlocks k β step w).get, List.nodup_iff_injective_getElem.mp (activeBlocks_nodup ..)⟩

theorem activeIDs_ofFn {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) :
    activeIDs ((tally k,tally β,tally step),List.ofFn fun i => tally (w i)) =
      List.ofFn fun t => tally (selectBlock k β step w t).val := by
  conv_lhs => rw [activeIDs_eq, ← List.ofFn_get (activeBlocks k β step w),List.map_ofFn]
  rfl


end FixedCandidate.CRTDispatch

end NearSquareRoot
end Computability
end OAI
