import OAI.Computability.VPVNP.RankQueryUniformResources
import OAI.Computability.VPVNP.RankCoordinatePrepareCost
import OAI.Computability.VPVNP.RankCoordinateSelectedAdvice

/-! # Uniform time and peak of the prepared evaluator coordinate machine -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ConcreteResources

open PolynomiallyBounded Cost

theorem argumentClock_poly {w : ℕ → ℕ} (hw : PB w) : PB (fun n => ArgumentStage.clock (w n)) :=
  (((const 4).mul (hw.add (const 1))).add (const 1)).add
    (((const 4).mul (((const 5).mul hw).add (const 2))).add (const 1))

/-- The label-mode estimate with the largest permitted label also covers
the Frobenius branch and shorter unary labels. -/
theorem prepare_mode_covers (P : Type) [Fintype P] (b : Bool) (M A B S w : ℕ) {label labels : ℕ}
    (h : label ≤ labels) :
    Prepare.time P b M B label w ≤ Prepare.time P false M B labels w ∧
      Prepare.peak P M A S label w ≤ Prepare.peak P M A S labels w := by
  have hclock : LabelWord.clock label w ≤ LabelWord.clock labels w := by unfold LabelWord.clock; gcongr
  have htime : Prepare.labelTime b label w ≤ LabelWord.clock labels w := by
    cases b with
    | false => exact hclock
    | true => change 1 ≤ LabelWord.clock labels w; unfold LabelWord.clock; omega
  constructor
  · unfold Prepare.time
    change _ ≤ _ + LabelWord.clock labels w + ArgumentStage.clock w
    gcongr
  · unfold Prepare.peak Prepare.baseCap
    gcongr

theorem prepare_feasible (P : Type) [Fintype P] {M A label w : ℕ → ℕ} {row : ℕ → Budget}
    (hM : PB M) (hA : PB A) (hl : PB label) (hw : PB w) (hr : Feasible row) :
    Feasible (fun n => ⟨Prepare.time P false (M n) (row n).time (label n) (w n),
      Prepare.peak P (M n) (A n) (row n).space (label n) (w n)⟩) := by
  have load := loadClock_poly P hM
  have dyn := dynamic_feasible hr hw
  have tag := label_feasible hl hw
  have args := argumentClock_poly hw
  exact ⟨clog_add (clog_add (clog_add load.clog dyn.time) tag.time) args.clog,
    (poly_max (hA.add load) (poly_max dyn.space tag.space)).add args⟩

/-- Common bounds on the loaded root, selector, and unary-register templates
and on the public request while they are loaded. -/
abbrev inputCap := FullAdvice.portBound

/-- Budget for the selector scan including the time and space of the ordinal calling
convention. -/
def selectorBudget (K : Type) [Fintype K] (rows d w v e B A S : ℕ) : Budget :=
  ⟨Select.scanTime K rows d w v e B A S + OrdinalABI.overhead w,
   Select.scanSpace K d w v e A S + OrdinalABI.overhead w⟩

/-- Run the live preparation with the actual greedy selector as a callback. -/
def prepareBudget (P K : Type) [Fintype P] [Fintype K] (rows d w v e B A S labels : ℕ) : Budget :=
  let row := selectorBudget K rows d w v e B A S
  let M := SelectedAdvice.portBound K d w v e A S
  ⟨Prepare.time P false M row.time labels w, Prepare.peak P M (max M labels) row.space labels w⟩

/-- The physical setup theorem takes the actual label, operation mode and
starting advice. A single budget uses the largest label at this length. -/
theorem prepareBudget_covers (P K : Type) [Fintype P] [Fintype K]
    (rows d w v e B A S : ℕ) (mode : Bool) {label labels : ℕ} (hl : label ≤ labels) :
    let row := selectorBudget K rows d w v e B A S
    let M := SelectedAdvice.portBound K d w v e A S
    let budget := prepareBudget P K rows d w v e B A S labels
    Prepare.time P mode M row.time label w ≤ budget.time ∧
      Prepare.peak P M (max label M) row.space label w ≤ budget.space := by
  intro row M budget
  have ha : max label M ≤ max M labels := max_le (hl.trans (le_max_right ..)) (le_max_left ..)
  have room : Prepare.peak P M (max label M) row.space label w ≤
      Prepare.peak P M (max M labels) row.space label w := by
    unfold Prepare.peak Prepare.baseCap
    gcongr
  have bounds := prepare_mode_covers P mode M (max M labels) row.time row.space w hl
  exact ⟨bounds.1,room.trans bounds.2⟩

theorem prepareBudget_feasible (P K : Type) [Fintype P] [Fintype K] {rows d w v e B A S labels : ℕ → ℕ}
    (hr : LB rows) (hd : PB d) (hw : PB w) (hv : PB v) (he : PB e)
    (hB : LB B) (hA : PB A) (hS : PB S) (hlabels : PB labels) :
    Feasible (fun n => prepareBudget P K (rows n) (d n) (w n) (v n) (e n) (B n) (A n) (S n) (labels n)) := by
  have row := selector_feasible K hr hd hw hv he hA hS hB
  have ready := poly_max row.space (poly_max hS hA)
  have cap := poly_max (templateCap_poly hw hv he ready) (poly_max hw row.space)
  exact prepare_feasible P cap (poly_max cap hlabels) hlabels hw row

/-- The budget of the native reader as a function of its five varying
numerical parameters. It includes the preparation at this matrix shape. -/
def preparedBudget (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    (rows cols r d w v e B A S E labels : ℕ) :=
  mountedBudget H K rows cols r d w v e B A S E (prepareBudget P K rows d w v e B A S labels)

/-- The public advice supplied to the literal evaluator already fits the
same mounted reader's workspace estimate. -/
theorem preparedBudget_advice (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    (rows cols r d w v e B A S E labels : ℕ) :
    SelectedAdvice.portBound K d w v e A S ≤
      (preparedBudget P H K rows cols r d w v e B A S E labels).space := by
  let M := SelectedAdvice.portBound K d w v e A S
  let row := selectorBudget K rows d w v e B A S
  let stage := prepareBudget P K rows d w v e B A S labels
  let minor := minorBudget K rows cols d w v e B A S E
  let V := SelectedMinor.space K d w v e A S
  let cap := pairPeak r w v e V minor.space stage.space
  have load : M ≤ max M labels + RootInit.loadClock P M := (le_max_left ..).trans (Nat.le_add_right ..)
  have start : M ≤ stage.space := (load.trans (le_max_left ..)).trans (Nat.le_add_right ..)
  have pair : M ≤ cap := start.trans (le_max_left ..)
  exact (pair.trans (Nat.le_add_right cap (NativeReader.returnClock H cap))).trans (le_max_left ..)

/-- Maximum preparation budget over the two matrix dimensions, minor order, extension degree
and limb width admitted by the bounds. -/
def preparedMaximum (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    (limit d w degree limb B A S E labels : ℕ) :=
  maximum (fun x : Shapes limit degree limb => preparedBudget P H K (x.1 0) (x.1 1) (x.1 2)
    d w x.2.2 x.2.1 B A S E labels)

theorem preparedMaximum_covers (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    {rows cols r e v limit degree limb : ℕ} (hr : rows ≤ limit) (hc : cols ≤ limit) (ho : r ≤ limit)
    (he : e ≤ degree) (hv : v ≤ limb) (d w B A S E labels : ℕ) :
    let cost := preparedBudget P H K rows cols r d w v e B A S E labels
    let cap := preparedMaximum P H K limit d w degree limb B A S E labels
    cost.time ≤ cap.time ∧ cost.space ≤ cap.space := by
  let shape : Shapes limit degree limb :=
    ⟨![⟨rows,Nat.lt_succ_of_le hr⟩,⟨cols,Nat.lt_succ_of_le hc⟩,⟨r,Nat.lt_succ_of_le ho⟩],
      ⟨e,Nat.lt_succ_of_le he⟩,⟨v,Nat.lt_succ_of_le hv⟩⟩
  exact le_maximum (fun x : Shapes limit degree limb => preparedBudget P H K (x.1 0) (x.1 1) (x.1 2)
    d w x.2.2 x.2.1 B A S E labels) shape

theorem preparedMaximum_feasible (P H K : Type) [Fintype P] [Fintype H] [Fintype K]
    {limit d w degree limb B A S E labels : ℕ → ℕ}
    (hl : LB limit) (hd : PB d) (hw : PB w) (he : PB degree) (hv : PB limb)
    (hB : LB B) (hA : PB A) (hS : PB S) (hE : LB E) (hlabels : PB labels) :
    Feasible (fun n => preparedMaximum P H K (limit n) (d n) (w n) (degree n) (limb n)
      (B n) (A n) (S n) (E n) (labels n)) := by
  apply maximum_feasible
  intro shape
  have dim (j : Fin 3) : LB (fun n => (shape n).1 j) :=
    hl.of_le fun n => Nat.clog_mono_right _ (Nat.lt_succ_iff.mp ((shape n).1 j).isLt)
  have limb := hv.of_le (f := fun n => ((shape n).2.2 : ℕ)) fun n => Nat.lt_succ_iff.mp (shape n).2.2.isLt
  have deg := he.of_le (f := fun n => ((shape n).2.1 : ℕ)) fun n => Nat.lt_succ_iff.mp (shape n).2.1.isLt
  exact mounted_feasible_of_shape H K (dim 0) (dim 1) (dim 2) hd hw limb deg hB hA hS hE
    (prepareBudget_feasible P K (dim 0) hd hw limb deg hB hA hS hlabels)

end RankQuery.Stack.Coordinate.ConcreteResources

end VPVNP
end Computability
end OAI
