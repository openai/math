import OAI.Computability.VPVNP.CompressorRecordScores
import OAI.Computability.VPVNP.PrimedScheduleRAM
import Mathlib.Algebra.BigOperators.Fin

/-!
# The two layout counters on the stored motif terms

The dense term row has its repetition count at offset one and its vector of payload
coordinates starting at offset two. One pass visits all motif rows for a fixed role
and layout. Its native worker computes the supply width, including the selector bits.
Eight such passes are preceded by a two-cell clear and followed by one comparison
that writes the common layout into its level's cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermScores

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Encode a natural term-score parameter as a machine word. -/
abbrev word (n : ℕ) : Word w := Fin.ofNat _ n

/-- The dense term layout, score-counter base, selector width, and destination for the common
layout choice. -/
structure Tables (w : ℕ) where
  /-- First address of the fixed-stride term rows. -/
  termBase : Word w
  /-- Distance in words between successive motif term rows. -/
  termStride : Word w
  /-- Address of the first of two adjacent layout score counters. -/
  scoreBase : Word w
  /-- Selector width charged once for each repetition in the term record. -/
  selectorBits : Word w
  /-- Address where the final comparison publishes the chosen layout. -/
  levelCell : Word w

/-- Parameters for one scoring pass over a fixed payload coordinate and layout side. -/
structure Axis (w : ℕ) where
  /-- Payload coordinate whose width contributes to this scoring pass. -/
  coordinate : Word w
  /-- Layout side whose counter the pass updates. -/
  side : Bool
  /-- Weight multiplying the squared supply width in this pass. -/
  weight : Word w

/-- Assemble the seven public operands for the term-score worker from the term layout and
selected scoring axis. -/
def params (L : Tables w) (A : Axis w) : Fin 7 → Word w :=
  ![L.termBase, L.termStride, L.scoreBase, L.selectorBits, A.coordinate, word A.side.toNat, A.weight]

/-- First word of motif term row `i` at the configured stride. -/
def rowBase (L : Tables w) (i : Word w) := L.termBase + i * L.termStride
/-- Address of the repetition-count word in motif term row `i`. -/
def repetitions (L : Tables w) (i : Word w) := rowBase L i + 1
/-- Address of the axis's payload-width coordinate in the specified motif term row. -/
def payload (L : Tables w) (A : Axis w) (i : Word w) := rowBase L i + 2 + A.coordinate
/-- Select the score-counter address for the Boolean layout side. -/
def counter (L : Tables w) (l : Bool) := L.scoreBase + word l.toNat

/-- Natural supply width of one axis and motif, including the selector width for each stored
repetition. -/
def supplyWidth (L : Tables w) (A : Axis w) (m : Memory w) (i : ℕ) : ℕ :=
  (m (payload L A (word i)).val).val + (m (repetitions L (word i)).val).val * L.selectorBits.val

/-- Sum the axis's weighted squared supply widths over the first `n` motif rows. -/
def axisTotal (L : Tables w) (m : Memory w) (n : ℕ) (A : Axis w) : ℕ :=
  ∑ i ∈ Finset.range n, A.weight.val * supplyWidth L A m i ^ 2

/-- Add the axis totals assigned to the requested layout side. -/
def total (L : Tables w) (m : Memory w) (n : ℕ) (axes : List (Axis w)) (l : Bool) : ℕ :=
  (axes.map (fun A => if A.side = l then axisTotal L m n A else 0)).sum

/-- Enumerating the eight axes by layout and role is the same as summing the four
role scores of the selected layout over the dense motif rows. -/
theorem total_fin_axes (L : Tables w) (m : Memory w) (n : ℕ) (axes : Fin 8 → Axis w)
    (side : ∀ j : Fin 2 × Fin 4, (axes (finProdFinEquiv j)).side = finTwoEquiv j.1)
    (l : Bool) :
    total L m n (List.ofFn axes) l =
      ∑ t : Fin 4, ∑ j : Fin n, (axes (finProdFinEquiv (finTwoEquiv.symm l, t))).weight.val *
        supplyWidth L (axes (finProdFinEquiv (finTwoEquiv.symm l, t))) m j.val ^ 2 := by
  let f (i : Fin 8) := if (axes i).side = l then axisTotal L m n (axes i) else 0
  change ((List.ofFn axes).map _).sum = _
  rw [List.map_ofFn, List.sum_ofFn]
  change ∑ i, f i = _
  rw [← (finProdFinEquiv (m := 2) (n := 4)).sum_comp f, Fintype.sum_prod_type]
  have hs (b : Fin 2) (t : Fin 4) : (axes (finProdFinEquiv (b,t))).side = l ↔ b = finTwoEquiv.symm l := by
    rw [side]; exact finTwoEquiv.eq_symm_apply.symm
  simp only [f, hs, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro t _
  exact (Fin.sum_univ_eq_sum_range (fun i => (axes (finProdFinEquiv (finTwoEquiv.symm l,t))).weight.val *
    supplyWidth L (axes (finProdFinEquiv (finTwoEquiv.symm l,t))) m i ^ 2) n).symm

/-- Four probes: read the repetition count and payload, then read and write the counter. -/
def worker : List (Op 5 7) :=
  [.stateWord 0, .publicWord 1 1, .binary .mul 1 0 1, .publicWord 2 0, .binary .add 1 2 1,
    .constant 2 1, .binary .add 3 1 2, .read 3 3, .publicWord 4 3, .binary .mul 3 3 4,
    .constant 4 2, .binary .add 1 1 4, .publicWord 4 4, .binary .add 1 1 4, .read 4 1,
    .binary .add 3 4 3, .binary .mul 3 3 3, .publicWord 4 6, .binary .mul 3 4 3,
    .publicWord 1 2, .publicWord 4 5, .binary .add 1 1 4, .read 4 1, .binary .add 4 4 3,
    .write 1 4, .binary .add 0 0 2]

/-- Instantiate the native single-row score accumulator with the term layout and axis operands. -/
def workerMachine (L : Tables w) (A : Axis w) := (template worker 0).instantiate w (params L A)

/-- The updated machine-word score after adding the current row's weighted squared supply width
to its side's counter. -/
def nextScore (L : Tables w) (A : Axis w) (m : Memory w) (i : Word w) : Word w :=
  let width := m (payload L A i).val + m (repetitions L i).val * L.selectorBits
  m (counter L A.side).val + A.weight * (width * width)

/-- The report of one score update, with reads of the repetition count, payload width, and
counter, followed by the counter write and next row cursor. -/
def workerReport (L : Tables w) (A : Axis w) (m : Memory w) (i : Word w) : Report w :=
  let u := repetitions L i
  let v := payload L A i
  let cell := counter L A.side
  ⟨List.replicate 7 .tick ++ [.read u (m u.val)] ++ List.replicate 6 .tick ++ [.read v (m v.val)]
    ++ List.replicate 7 .tick ++ [.read cell (m cell.val), .tick, .write cell (nextScore L A m i), .tick],
    some (i+1)⟩

theorem execute_worker (L : Tables w) (A : Axis w) (m : Memory w) (i : Word w) :
    let M := workerMachine L A
    execute M.program 27 (M.program.start i) m [] = some (workerReport L A m i) := by
  rfl

theorem worker_after (L : Tables w) (A : Axis w) (m : Memory w) (i : Word w) :
    after m (workerReport L A m i).events = writeMemory m (counter L A.side) (nextScore L A m i) := rfl

theorem worker_report_cost (L : Tables w) (A : Axis w) (m : Memory w) (i : Word w) :
    let r := workerReport L A m i
    r.events.length = 26 ∧ r.probes = 4 ∧ choiceBits r.events = [] := ⟨rfl, rfl, rfl⟩

/-- Only the two accumulator addresses and the output cell need separation. Repetition
and coordinate reads may be shared between axes or between rows. -/
structure Layout (L : Tables w) (n : ℕ) (axes : List (Axis w)) : Prop where
  distinct : Function.Injective (counter L)
  output : ∀ l, L.levelCell ≠ counter L l
  rep : ∀ i < n, ∀ l, repetitions L (word i) ≠ counter L l
  coord : ∀ A ∈ axes, ∀ i < n, ∀ l, payload L A (word i) ≠ counter L l

theorem rowBase_val (L : Tables w) {i : ℕ} (h : L.termBase.val+i*L.termStride.val < 2^w) :
    (rowBase L (word i)).val = L.termBase.val+i*L.termStride.val := by
  simp only [rowBase, Fin.val_add, Fin.val_mul, Fin.val_ofNat, Nat.mod_mul_mod,
    Nat.add_mod_mod, Nat.mod_eq_of_lt h]

theorem repetitions_val (L : Tables w) {i : ℕ} (h : L.termBase.val+i*L.termStride.val+1 < 2^w) :
    (repetitions L (word i)).val = L.termBase.val+i*L.termStride.val+1 := by
  have hb := rowBase_val L (i := i) (by omega)
  rw [repetitions, Fin.val_add, hb, Fin.val_one', Nat.add_mod_mod, Nat.mod_eq_of_lt h]

theorem payload_val (L : Tables w) (A : Axis w) {i : ℕ}
    (h : L.termBase.val+i*L.termStride.val+2+A.coordinate.val < 2^w) :
    (payload L A (word i)).val = L.termBase.val+i*L.termStride.val+2+A.coordinate.val := by
  have hb := rowBase_val L (i := i) (by omega)
  have h₂ : (2 : Word w).val = 2 := Nat.mod_eq_of_lt (by omega : 2 < 2^w)
  rw [payload, Fin.val_add, Fin.val_add, hb, h₂, Nat.mod_add_mod, Nat.mod_eq_of_lt h]

/-- Consecutive dense term rows and a disjoint two-word scratch region implement all
the read/write separation required by the eight passes. -/
theorem Layout.ofIntervals (L : Tables w) (n : ℕ) (axes : List (Axis w))
    (rowSize : 1 < L.termStride.val) (fields : ∀ A ∈ axes, 2+A.coordinate.val < L.termStride.val)
    (termFit : L.termBase.val+n*L.termStride.val ≤ 2^w) (scoreFit : L.scoreBase.val+1 < 2^w)
    (regions : L.termBase.val+n*L.termStride.val ≤ L.scoreBase.val ∨ L.scoreBase.val+2 ≤ L.termBase.val)
    (level : L.levelCell.val < L.scoreBase.val ∨ L.scoreBase.val+1 < L.levelCell.val) : Layout L n axes := by
  have hv (l : Bool) : (counter L l).val = L.scoreBase.val+l.toNat := by
    have hb : l.toNat ≤ 1 := by cases l <;> decide
    rw [counter, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
  have endRow (i : ℕ) (hi : i < n) : (i+1)*L.termStride.val ≤ n*L.termStride.val :=
    Nat.mul_le_mul_right _ hi
  constructor
  · intro l k h
    have he := congrArg Fin.val h
    rw [hv, hv] at he
    cases l <;> cases k <;> simp_all
  · intro l h
    have he := congrArg Fin.val h
    rw [hv] at he
    have hb : l.toNat ≤ 1 := by cases l <;> decide
    omega
  · intro i hi l h
    have he := congrArg Fin.val h
    have heR := endRow i hi
    rw [Nat.add_mul, Nat.one_mul] at heR
    rw [repetitions_val L (by omega), hv] at he
    have hb : l.toNat ≤ 1 := by cases l <;> decide
    omega
  · intro A ha i hi l h
    have he := congrArg Fin.val h
    have hf := fields A ha
    have heR := endRow i hi
    rw [Nat.add_mul, Nat.one_mul] at heR
    rw [payload_val L A (by omega), hv] at he
    have hb : l.toNat ≤ 1 := by cases l <;> decide
    omega

/-- A single integer bound, using the number of rows, the fixed weights in the given
layout and the largest supply width, suffices for every counter in the phase. -/
theorem total_le (L : Tables w) (m : Memory w) (n W : ℕ) (axes : List (Axis w)) (l : Bool)
    (widthBound : ∀ A ∈ axes, ∀ i < n, supplyWidth L A m i ≤ W) :
    total L m n axes l ≤ n * (axes.map (fun A => if A.side = l then A.weight.val else 0)).sum * W^2 := by
  induction axes with
  | nil => simp [total]
  | cons A rest ih =>
    have tail := ih fun a ha => widthBound a (List.mem_cons_of_mem _ ha)
    have head : axisTotal L m n A ≤ n*(A.weight.val*W^2) := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, A.weight.val * W^2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (widthBound A (List.mem_cons_self ..) i
            (Finset.mem_range.mp hi)) _)
        _ = _ := by simp
    by_cases h : A.side = l
    · simp only [total, List.map_cons, List.sum_cons, h, ite_true, Nat.mul_add, Nat.add_mul]
      exact Nat.add_le_add (by simpa [Nat.mul_assoc] using head) tail
    · simpa [total, h] using tail

theorem partial_le_total (L : Tables w) (m : Memory w) (n k : ℕ) (hk : k ≤ n)
    (done rest : List (Axis w)) (A : Axis w) (l : Bool) :
    total L m n done l + (if A.side = l then axisTotal L m k A else 0) ≤
      total L m n (done ++ A :: rest) l := by
  have hmono : axisTotal L m k A ≤ axisTotal L m n A :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => Nat.zero_le _)
  by_cases h : A.side = l <;> simp [total, h]
  omega

/-- The words in the counters are residues of the integer totals. All other words still
have their values from the entry to the score phase. -/
structure Snapshot (L : Tables w) (initial current : Memory w) (score : Bool → ℕ) : Prop where
  stored : ∀ l, current (counter L l).val = word (score l)
  frame : ∀ j, (∀ l, j ≠ (counter L l).val) → current j = initial j

theorem Snapshot.exact {L : Tables w} {initial current : Memory w} {score : Bool → ℕ}
    (s : Snapshot L initial current score) (l : Bool) (fit : score l < 2^w) :
    (current (counter L l).val).val = score l := by
  rw [s.stored]
  exact Nat.mod_eq_of_lt fit

private theorem word_succ (k : ℕ) : word (w := w) k + 1 = word (k+1) := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_one', Fin.val_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]

private theorem nextScore_eq (L : Tables w) (A : Axis w) (initial current : Memory w)
    (i : ℕ) (score : Bool → ℕ) (snap : Snapshot L initial current score)
    (hr : ∀ l, repetitions L (word i) ≠ counter L l)
    (hv : ∀ l, payload L A (word i) ≠ counter L l) :
    nextScore L A current (word i) = word (score A.side + A.weight.val * supplyWidth L A initial i ^ 2) := by
  have hrep := snap.frame _ fun l => Fin.val_ne_of_ne (hr l)
  have hpay := snap.frame _ fun l => Fin.val_ne_of_ne (hv l)
  apply Fin.ext
  simp only [nextScore, hrep, hpay, snap.stored, supplyWidth, pow_two, Fin.val_add, Fin.val_mul,
    Fin.val_ofNat, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]

private theorem snapshot_step (L : Tables w) (A : Axis w) (initial current : Memory w)
    (i : ℕ) (score : Bool → ℕ) (snap : Snapshot L initial current score)
    (distinct : Function.Injective (counter L))
    (hr : ∀ l, repetitions L (word i) ≠ counter L l)
    (hv : ∀ l, payload L A (word i) ≠ counter L l) :
    Snapshot L initial (after current (workerReport L A current (word i)).events)
      (fun l => score l + if A.side = l then A.weight.val * supplyWidth L A initial i ^ 2 else 0) := by
  rw [worker_after, nextScore_eq L A initial current i score snap hr hv]
  constructor
  · intro l
    by_cases h : A.side = l
    · subst l; simp [writeMemory]
    · have hne := Fin.val_ne_of_ne (fun he => h (distinct he.symm) : counter L l ≠ counter L A.side)
      simp [writeMemory, hne, h, snap.stored]
  · intro j hj
    simp [writeMemory, hj, snap.frame j hj]

private theorem probes_append (rs ts : List (Report w)) :
    RAMBuckets.probeCount Report.probes (rs++ts) =
      RAMBuckets.probeCount Report.probes rs + RAMBuckets.probeCount Report.probes ts := by
  have h := RAMBuckets.cost_append Report.probes rs ts
  simp only [RAMBuckets.cost_eq_length_add_probes, List.length_append] at h
  omega

/-- All rows of one role pass, from a fresh private register file at each call. -/
theorem pass (L : Tables w) (A : Axis w) (n : ℕ) (initial current : Memory w)
    (start : Bool → ℕ) (snap : Snapshot L initial current start)
    (distinct : Function.Injective (counter L))
    (hr : ∀ i < n, ∀ l, repetitions L (word i) ≠ counter L l)
    (hv : ∀ i < n, ∀ l, payload L A (word i) ≠ counter L l) :
    ∃ rs, runSegment (workerMachine L A).program 27 (some 0) current (List.replicate n []) = some rs ∧
      Snapshot L initial (after current (eventLog rs))
        (fun l => start l + if A.side = l then axisTotal L initial n A else 0) ∧
      endState (some 0) rs = some (word n) ∧ rs.length = n ∧
      RAMBuckets.probeCount Report.probes rs = 4*n := by
  induction n with
  | zero => exact ⟨[], rfl, by simpa [axisTotal, eventLog, after] using snap, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨rs, hrun, hs, hend, hlen, hcost⟩ := ih
      (fun i hi => hr i (by omega)) (fun i hi => hv i (by omega))
    let m := after current (eventLog rs)
    let r := workerReport L A m (word n)
    have step := snapshot_step L A initial m n _ hs distinct (hr n (by omega)) (hv n (by omega))
    refine ⟨rs ++ [r], ?_, ?_, ?_, by simp [hlen], ?_⟩
    · rw [List.replicate_succ', PrimedSchedule.runSegment_append, hrun, Option.bind_some, hend]
      simp [runSegment, execute_worker, r, m, workerReport]
    · have hm : after current (eventLog (rs ++ [r])) = after m r.events := by
        simp [eventLog, m, after]
      rw [hm]
      convert step using 1
      funext l
      by_cases h : A.side = l <;> simp [h, axisTotal, Finset.sum_range_succ, Nat.add_assoc]
    · rw [endState_append, hend]
      change some (word n + 1) = some (word (n+1))
      rw [word_succ]
    · rw [probes_append, hcost]
      change 4 * n + 4 = 4*(n+1)
      omega

/-- Execute the successive axis-specific public tables, with the previous pass's memory
and a fresh row cursor at each pass boundary. -/
def runAxes (L : Tables w) (n : ℕ) : List (Axis w) → Memory w → Option (List (Report w))
  | [], _ => some []
  | A :: axes, m => do
    let rs ← runSegment (workerMachine L A).program 27 (some 0) m (List.replicate n [])
    let ts ← runAxes L n axes (after m (eventLog rs))
    return rs ++ ts

theorem run_axes (L : Tables w) (n : ℕ) (axes : List (Axis w))
    (initial current : Memory w) (start : Bool → ℕ) (snap : Snapshot L initial current start)
    (layout : Layout L n axes) :
    ∃ rs, runAxes L n axes current = some rs ∧
      Snapshot L initial (after current (eventLog rs)) (fun l => start l + total L initial n axes l) ∧
      rs.length = axes.length*n ∧ RAMBuckets.probeCount Report.probes rs = axes.length*(4*n) := by
  induction axes generalizing current start with
  | nil => exact ⟨[], rfl, by simpa [total, eventLog, after] using snap, by simp, by simp [RAMBuckets.probeCount]⟩
  | cons A axes ih =>
    obtain ⟨rs, hr, hs, _, hn, hc⟩ := pass L A n initial current start snap layout.distinct
      layout.rep (layout.coord A (List.mem_cons_self ..))
    let m := after current (eventLog rs)
    have smaller : Layout L n axes :=
      ⟨layout.distinct, layout.output, layout.rep, fun a ha => layout.coord a (List.mem_cons_of_mem _ ha)⟩
    obtain ⟨ts, ht, hst, htn, htc⟩ := ih m _ hs smaller
    refine ⟨rs++ts, ?_, ?_, ?_, ?_⟩
    · rw [runAxes, hr]
      change (runAxes L n axes m).bind _ = _
      rw [ht]
      rfl
    · have hm : after current (eventLog (rs++ts)) = after m (eventLog ts) := by simp [eventLog, after, m]
      rw [hm]
      simpa [total, Nat.add_assoc] using hst
    · simp [hn, htn, Nat.add_mul, Nat.add_comm]
    · simp [probes_append, hc, htc, Nat.add_mul, Nat.add_comm]

theorem counter_false (L : Tables w) : counter L false = L.scoreBase := by
  change L.scoreBase + 0 = _
  rw [add_zero]

theorem counter_true (L : Tables w) : counter L true = L.scoreBase + 1 := rfl

/-- A fixed call clears both scores, even when reusing a scratch area. -/
def clearCode : List (Op 3 1) :=
  [.publicWord 0 0, .constant 1 0, .write 0 1, .constant 2 1,
   .binary .add 0 0 2, .write 0 1]

/-- Instantiate the native call that clears the two adjacent layout score counters. -/
def clearMachine (L : Tables w) := (template clearCode 1).instantiate w (fun _ => L.scoreBase)

/-- The six-event report that writes zero to both score counters and returns zero. -/
def clearReport (L : Tables w) : Report w :=
  ⟨[.tick,.tick,.write L.scoreBase 0,.tick,.tick,.write (L.scoreBase+1) 0],some 0⟩

theorem execute_clear (L : Tables w) (m : Memory w) :
    let M := clearMachine L
    execute M.program 7 (M.program.start 0) m [] = some (clearReport L) := rfl

theorem clear_report_cost (L : Tables w) :
    let r := clearReport L
    r.events.length = 6 ∧ r.probes = 2 ∧ choiceBits r.events = [] := ⟨rfl, rfl, rfl⟩

theorem clear_snapshot (L : Tables w) (m : Memory w) :
    Snapshot L m (after m (clearReport L).events) (fun _ => 0) := by
  change Snapshot L m (writeMemory (writeMemory m L.scoreBase 0) (L.scoreBase+1) 0) _
  constructor
  · intro l
    cases l <;> simp [counter_false, counter_true, writeMemory]
  · intro j hj
    have h0 : j ≠ L.scoreBase.val := counter_false L ▸ hj false
    have h1 : j ≠ (L.scoreBase+1).val := hj true
    simp only [writeMemory, ite_eq_right h0, ite_eq_right h1]

/-- The comparison reads both accumulators and writes the chosen bit directly to the
designated level cell. The strict branch returns one. -/
def compareTemplate : Template 11 5 2 where
  literalWidth := 1
  entry := 0
  code pc := match pc.val with
    | 0 => .publicWord 0 0 1
    | 1 => .readExternal 1 0 2
    | 2 => .constant 2 1 3
    | 3 => .binary .add 0 0 2 4
    | 4 => .readExternal 3 0 5
    | 5 => .jumpLt 3 1 6 7
    | 6 => .constant 4 1 8
    | 7 => .constant 4 0 8
    | 8 => .publicWord 0 1 9
    | 9 => .writeExternal 0 4 10
    | _ => .returnState 4

/-- Instantiate the comparison call with the two-counter base and the destination level cell. -/
def compareMachine (L : Tables w) := compareTemplate.instantiate w ![L.scoreBase, L.levelCell]

/-- Choose layout one exactly when its score is strictly smaller than layout zero's score,
resolving ties in favor of zero. -/
def bit (L : Tables w) (m : Memory w) : Word w :=
  if m (L.scoreBase+1).val < m L.scoreBase.val then 1 else 0

/-- The comparison report reads both scores, writes the chosen bit to the level cell, and
returns that bit. -/
def compareReport (L : Tables w) (m : Memory w) : Report w :=
  ⟨[.tick,.read L.scoreBase (m L.scoreBase.val),.tick,.tick,
    .read (L.scoreBase+1) (m (L.scoreBase+1).val),.tick,.tick,.tick,
    .write L.levelCell (bit L m)],some (bit L m)⟩

theorem execute_compare (L : Tables w) (m : Memory w) :
    let M := compareMachine L
    execute M.program 10 (M.program.start 0) m [] = some (compareReport L m) := by
  let M := compareMachine L
  let c := (((M.program.start 0).put 1 0 L.scoreBase).put 2 1 (m L.scoreBase.val)).put 3 2 1
  let d := (c.put 4 0 (L.scoreBase+1)).put 5 3 (m (L.scoreBase+1).val)
  let pc := if m (L.scoreBase+1).val < m L.scoreBase.val then (6 : Fin 11) else 7
  change (execute M.program 4 { d with pc := pc } m []
    |>.map (Report.prepend .tick) |>.map (Report.prepend (.read (L.scoreBase+1) (m (L.scoreBase+1).val)))
    |>.map (Report.prepend .tick) |>.map (Report.prepend .tick)
    |>.map (Report.prepend (.read L.scoreBase (m L.scoreBase.val))) |>.map (Report.prepend .tick)) = _
  by_cases h : m (L.scoreBase+1).val < m L.scoreBase.val <;>
    simp only [pc, h, ↓reduceIte, compareReport, bit] <;> rfl

theorem compare_report_cost (L : Tables w) (m : Memory w) :
    let r := compareReport L m
    r.events.length = 9 ∧ r.probes = 3 ∧ choiceBits r.events = [] := ⟨rfl, rfl, rfl⟩

/-- Actual memory at an arbitrary prefix, after clearing, visiting whole earlier axes,
and then processing the first `k` rows of the current axis. A bound on the final scores
suffices for all such prefix scores. -/
theorem run_prefix (L : Tables w) (n k : ℕ) (hk : k ≤ n) (done rest : List (Axis w))
    (A : Axis w) (m : Memory w) (layout : Layout L n (done ++ A :: rest))
    (fit : ∀ l, total L m n (done ++ A :: rest) l < 2^w) :
    let cleared := after m (clearReport L).events
    ∃ first part, runAxes L n done cleared = some first ∧
      runSegment (workerMachine L A).program 27 (some 0) (after cleared (eventLog first))
        (List.replicate k []) = some part ∧
      ∀ l, (after (after cleared (eventLog first)) (eventLog part) (counter L l).val).val =
        total L m n done l + if A.side = l then axisTotal L m k A else 0 := by
  let m₁ := after m (clearReport L).events
  have earlier : Layout L n done :=
    ⟨layout.distinct, layout.output, layout.rep, fun a ha => layout.coord a (List.mem_append_left _ ha)⟩
  obtain ⟨first, hf, hs, _, _⟩ := run_axes L n done m m₁ _ (clear_snapshot L m) earlier
  have hs' : Snapshot L m (after m₁ (eventLog first)) (total L m n done) := by
    simpa only [Nat.zero_add] using hs
  obtain ⟨part, hp, ht, _, _, _⟩ := pass L A k m _ _ hs' layout.distinct
    (fun i hi => layout.rep i (hi.trans_le hk))
    (fun i hi => layout.coord A (List.mem_append_right _ (List.mem_cons_self ..)) i (hi.trans_le hk))
  exact ⟨first, part, hf, hp, fun l => ht.exact l ((partial_le_total L m n k hk done rest A l).trans_lt (fit l))⟩

/-- The scheduled clear, eight row passes, and level-cell write all execute the native
instruction tables. Only the row cursors are reset at the pass boundaries. -/
def run (L : Tables w) (n : ℕ) (axes : List (Axis w)) (m : Memory w) : Option (List (Report w)) := do
  let c ← execute (clearMachine L).program 7 ((clearMachine L).program.start 0) m []
  let rs ← runAxes L n axes (after m c.events)
  let m' := after (after m c.events) (eventLog rs)
  let d ← execute (compareMachine L).program 10 ((compareMachine L).program.start 0) m' []
  return c :: (rs ++ [d])

theorem run_eight (L : Tables w) (n : ℕ) (axes : Fin 8 → Axis w) (m : Memory w)
    (layout : Layout L n (List.ofFn axes)) (fit : ∀ l, total L m n (List.ofFn axes) l < 2^w) :
    let score := total L m n (List.ofFn axes)
    let selected : Word w := if score true < score false then 1 else 0
    ∃ rs, run L n (List.ofFn axes) m = some rs ∧
      (∀ l, (after m (eventLog rs) (counter L l).val).val = score l) ∧
      after m (eventLog rs) L.levelCell.val = selected ∧
      (∀ j, j ≠ L.levelCell.val → (∀ l, j ≠ (counter L l).val) → after m (eventLog rs) j = m j) ∧
      endState (some 0) rs = some selected ∧ rs.length = 8*n+2 ∧
      RAMBuckets.probeCount Report.probes rs = 32*n+5 := by
  dsimp only
  let c := clearReport L
  let m₁ := after m c.events
  obtain ⟨rs, hrun, hs, hlen, hcost⟩ := run_axes L n (List.ofFn axes) m m₁ _ (clear_snapshot L m) layout
  let m₂ := after m₁ (eventLog rs)
  let d := compareReport L m₂
  have stored (l : Bool) : (m₂ (counter L l).val).val = total L m n (List.ofFn axes) l := by
    have h := congrArg Fin.val (hs.stored l)
    change (m₂ (counter L l).val).val = (0 + total L m n (List.ofFn axes) l) % (2^w) at h
    rwa [Nat.zero_add, Nat.mod_eq_of_lt (fit l)] at h
  have chosen : bit L m₂ = if total L m n (List.ofFn axes) true < total L m n (List.ofFn axes) false
      then 1 else 0 := by
    change (if (m₂ (L.scoreBase+1).val).val < (m₂ L.scoreBase.val).val then _ else _) = _
    rw [← counter_true L, ← counter_false L, stored, stored]
  have hm : after m (eventLog (c :: (rs ++ [d]))) = writeMemory m₂ L.levelCell (bit L m₂) := by
    change after m (c.events ++ eventLog (rs++[d])) = _
    rw [show after m (c.events ++ eventLog (rs++[d])) = after m₁ (eventLog (rs++[d])) from List.foldl_append]
    simp only [eventLog, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      after, List.foldl_append]
    rfl
  refine ⟨c :: (rs++[d]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run, execute_clear]
    change (runAxes L n (List.ofFn axes) m₁).bind _ = _
    rw [hrun]
    change (execute (compareMachine L).program 10 ((compareMachine L).program.start 0) m₂ []).bind _ = _
    rw [execute_compare]
    rfl
  · intro l
    rw [hm, writeMemory, ite_eq_right (Fin.val_ne_of_ne (layout.output l).symm), stored]
  · simp [hm, writeMemory, chosen]
  · intro j hj hjs
    rw [hm, writeMemory, ite_eq_right hj]
    exact hs.frame j hjs
  · change endState c.result (rs ++ [d]) = _
    rw [endState_append]
    change some (bit L m₂) = _
    rw [chosen]
  · simp [hlen]
  · change 2 + RAMBuckets.probeCount Report.probes (rs ++ [d]) = _
    rw [probes_append, hcost, List.length_ofFn]
    change 2 + (8*(4*n)+3) = _
    omega

end CompressorRecords.TermScores

end VPVNP
end Computability
end OAI
