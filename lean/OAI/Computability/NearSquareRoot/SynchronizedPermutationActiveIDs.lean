import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryOffsets
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetBox

/-! # Enumerating active blocks in each physical Beneš half-stage

Block numbers preserve directory order. Division by the charged capacity assigns
a block to its batch, and the local field width determines whether it has a target
bit at this stage.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.FieldDirectory

open IntegerMultiplication Code Staff Strip Carry
open SynchronizedPermutationBudget (capacity members batches)
open ShortFourier.BatchWord

abbrev IDQuery := (Tally × Tally × Tally) × List Tally

private def qreg (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem numeric {X : Type} [Codec X] (f : X → Tally) (P : Poly f) :
    Realizes (qreg X) (fun x => (f x).length) := by
  change Poly (fun x : X => tally (f x).length)
  simpa only [recover_tally] using P

/-- The actual number of block targets budgeted in a single physical pass. -/
theorem capacity_poly : Poly (fun k : Tally => tally (capacity k.length)) := by
  have K := numeric id (Code.Poly.identity (X := Tally))
  have lg := (Figure.of_spoken (K.plus (.fix 1))).short_log
  have w := (Realizes.fix 140).times ((Realizes.fix 1).plus lg)
  exact K.dividing (((Realizes.fix 8).times (.fix 1)).times w)

private def selected (p : IDQuery × Tally) : Bool :=
  let q := p.1
  decide (p.2.length / capacity q.1.1.length = q.1.2.1.length) &&
    decide (q.1.2.2.length < (Iter.pick [] (q.2,p.2)).length)

private theorem selected_poly : Poly selected := by
  let X := IDQuery × Tally
  let band (p : X) : Tally := p.1.1.2.1
  have C := (show Poly (fun p : X => p.1.1.1) by fun_prop).compose capacity_poly
  have I := numeric (fun p : X => p.2) Easy.snd.poly
  have cap : Realizes (qreg X) (fun p => capacity p.1.1.1.length) := C
  have idx : Poly (fun p : X => tally (p.2.length / capacity p.1.1.1.length)) := I.dividing cap
  have eqn := (idx.pair (show Poly band by unfold band; fun_prop)).compose
    (Iter.linked (X := Unit) (Y := Unit)).poly
  have width := (show Easy (fun p : X => (p.1.2,p.2)) by fun_prop).compose (Iter.facile ([] : Tally))
  have test := ((show Easy (fun p : X => p.1.1.2.2) by fun_prop).pair width).compose (Iter.small_easy (X := Unit) (Y := Unit))
  have h : Poly (fun p : X => decide (p.2.length / capacity p.1.1.1.length = p.1.1.2.1.length)) := by
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
  (List.finRange d).filter fun i => decide (i.val / capacity k = β) && decide (step < w i)

theorem mem_activeBlocks {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) (i : Fin d) :
    i ∈ activeBlocks k β step w ↔ i.val / capacity k = β ∧ step < w i := by
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

theorem selectBlock_range {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) (i : Fin d) :
    (∃ t, selectBlock k β step w t = i) ↔ i.val / capacity k = β ∧ step < w i := by
  rw [← mem_activeBlocks]
  exact List.mem_iff_get.symm

theorem activeCount_le {d k : ℕ} (hcap : 0 < capacity k) (β step : ℕ) (w : Fin d → ℕ) :
    (activeBlocks k β step w).length ≤ capacity k := by
  have h := SynchronizedPermutationBudget.members_card (d := d) hcap β
  have e := List.toFinset_card_of_nodup (activeBlocks_nodup k β step w)
  rw [← e]
  apply (Finset.card_le_card ?_).trans h
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((mem_activeBlocks _ _ _ _ _).mp (List.mem_toFinset.mp hi)).1⟩

theorem selectBlock_live {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ)
    (t : Fin (activeBlocks k β step w).length) :
    (selectBlock k β step w t).val / capacity k = β ∧ step < w (selectBlock k β step w t) :=
  (selectBlock_range ..).mp ⟨t,rfl⟩

theorem selectBlock_subset {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) :
    Finset.univ.image (selectBlock k β step w) ⊆ members k β := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(selectBlock_live k β step w t).1⟩

/-- Exactly one port is the target of each selected block. Its other ports fit
the control-bit budget proved for all blocks in this batch. -/
theorem activeControls_le {d : ℕ} (k β step : ℕ) (w : Fin d → ℕ) :
    (∑ t : Fin (activeBlocks k β step w).length, (w (selectBlock k β step w t) - 1)) ≤
      SynchronizedPermutationBudget.controlBits w k β := by
  let f := selectBlock k β step w
  calc
    _ = ∑ i ∈ Finset.univ.image f, (w i-1) := (Finset.sum_image f.injective.injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (selectBlock_subset k β step w)

/-- The typed target and control banks of the actual active-ID enumeration
fit the two physical reserves and both guard chunks. -/
theorem activeLayout_le {d k low high : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, w i ≤ SynchronizedPermutationBudget.width k)
    (room : 8*SynchronizedPermutationBudget.width k ≤ k) (res : low+high ≤ k/4) (β step : ℕ) :
    let b := (activeBlocks k β step w).length
    let c := ∑ i, (w (selectBlock k β step w i)-1)
    high + c + (b+1)*Controlled.guardWidth k + (b+1)*Controlled.guardWidth k + low ≤ k := by
  let f := selectBlock k β step w
  have bound := SynchronizedPermutationBudget.selected_fits w hw room res β _ (selectBlock_subset k β step w)
  simpa only [Finset.sum_image f.injective.injOn, Finset.card_image_of_injective _ f.injective,
    Finset.card_univ, Fintype.card_fin, f] using bound

/-- Across the batch schedule every available local target bit is used once. -/
theorem uniqueBatch {d k : ℕ} (hcap : 0 < capacity k) (step : ℕ) (w : Fin d → ℕ)
    (i : Fin d) (hi : step < w i) :
    ∃! β : Fin (batches d k), ∃ t, selectBlock k β.val step w t = i := by
  let β : Fin (batches d k) := ⟨i.val / capacity k,SynchronizedPermutationBudget.batch_index_lt hcap i⟩
  exact ⟨β,(selectBlock_range _ _ _ _ _).2 ⟨rfl,hi⟩,fun b hb =>
    Fin.ext ((selectBlock_range _ _ _ _ _).1 hb).1.symm⟩

/-- The active block IDs for an actual directed row, with its computed width directory. -/
def activeRow (p : PermDirectory.Query × Tally × Tally) : List Tally :=
  activeIDs ((p.1.2.1,p.2.1,p.2.2),(PermDirectory.directory p.1).map Prod.fst)

theorem activeRow_poly : Poly activeRow := by
  let X := PermDirectory.Query × Tally × Tally
  have W := ((Easy.fst (X := PermDirectory.Query) (Y := Tally × Tally)).poly.compose PermDirectory.directory_poly).compose
    (Poly.maps _ Easy.fst.poly)
  exact ((show Poly (fun x : X => (x.1.2.1,x.2.1,x.2.2)) by fun_prop).pair W).compose activeIDs_poly

theorem activeRow_eq {k L : ℕ} (hb : BoxShape.Valid k L (CoprimeBox.box k)) (dir : Bool)
    (stage : Tally) (β step : ℕ) :
    activeRow ((dir,tally k,stage),tally β,tally step) =
      List.ofFn (fun t => tally (selectBlock k β step
        (BoxFin.physicalWidth (box := CoprimeBox.box k)) t).val) := by
  rw [activeRow,PermHeader.rowWidths hb,activeIDs_ofFn]

end Benes.FieldDirectory

end NearSquareRoot
end Computability
end OAI
