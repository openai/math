import OAI.Computability.VPVNP.LiveHeaderProgramFit

/-!
# Field scans at the live header's scheduled addresses

The descriptor's two words supply the occupied interval. The scheduled row
supplies the destination and capacity. The processor sites precede scratch,
so an active copy preserves the remaining source bits and descriptor words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.ScanRows

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderDescriptors LiveHeader
open scoped Fin.CommRing

variable {w : ℕ}

/-- The first sixteen words of the scan row, before its wrapper appends the capacity. -/
private abbrev operands (w : ℕ) (s : Sizes) (base : ℕ) (side : Side) (f : Field) :=
  scalarPub w s base (.scan side f)

private theorem scan_row (s : Sizes) (base : ℕ) (side : Side) (f : Field) :
    rowData w s base (.scan side f) ∘ includeFin (by decide : 17 ≤ 17) =
      LiveHeaderBounded.publicData (operands w s base side f) (s.capacity f : Word w) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [LiveHeaderBounded.publicData, Fin.snoc_last]
    rfl
  · rw [LiveHeaderBounded.publicData, Fin.snoc_castSucc]
    rfl

private abbrev machine (w : ℕ) (s : Sizes) (base : ℕ) (side : Side) (f : Field) :=
  ((stageTemplate (.scan side f)).2.instantiate w (rowData w s base (.scan side f))).program

/-- A scheduled scan call executes the bounded field table with its exact public row. -/
theorem execute_scan (s : Sizes) (base : ℕ) (side : Side) (f : Field) (fuel : ℕ)
    (st : Word w) (m : Memory w) (bits : List Bool) :
    let P := ((stageTemplate (.scan side f)).2.instantiate w (rowData w s base (.scan side f))).program
    let Q := Allocated.boundedProgram scanSlots (cutSlot side) (decide (f = .padding))
      (scalarPub w s base (.scan side f)) (s.capacity f)
    execute P fuel (P.start st) m bits = execute Q fuel (Q.start st) m bits := by
  dsimp only
  unfold stageTemplate
  rw [entry_start, scan_row]
  cases side <;> rfl

private theorem run_scan (s : Sizes) (base : ℕ) (side : Side) (f : Field) (fuel : ℕ)
    (st : Option (Word w)) (m : Memory w) (bs : List (List Bool)) :
    runSegment (machine w s base side f) fuel st m bs =
      runSegment (Allocated.boundedProgram scanSlots (cutSlot side) (decide (f = .padding))
        (operands w s base side f) (s.capacity f)) fuel st m bs := by
  have hs : (if side = Side.left then 2 else 3 : Fin 4) = cutSlot side := by cases side <;> rfl
  unfold machine stageTemplate
  rw [run_entry, scan_row, hs]

private theorem scan_loaded (s : Sizes) (base : ℕ) (fit : limit s base < 2^w)
    (side : Side) (f : Field) (m : Memory w) (iv : ℕ × ℕ)
    (offset : (m (offsetAddr base)).val = iv.1) (count : (m (countAddr base)).val = iv.2) :
    Allocated.Loaded scanSlots (operands w s base side f) iv m := by
  obtain ⟨_, ho, hc, _⟩ := scan_public fit.le side f
  exact ⟨ho ▸ offset, hc ▸ count⟩

/-- The complete native scan copies exactly the occupied field to its scheduled
destination. Every successful report preserves the linker's tag on replay. -/
theorem copy_run (hw : 4 ≤ w) (s : Sizes) (base d : ℕ) (fit : limit s base < 2^w)
    (scratch : 2^d ≤ base) (side : Side) (f : Field) (hf : f ≠ .padding)
    (m : Memory w) (iv : ℕ × ℕ) (sites : iv.1+iv.2 ≤ 2^d) (capacity : iv.2 ≤ s.capacity f)
    (offset : (m (offsetAddr base)).val = iv.1) (count : (m (countAddr base)).val = iv.2) :
    let st := Stage.scan side f
    let P := ((stageTemplate st).2.instantiate w (rowData w s base st)).program
    ∃ rs, runSegment P 25 (some 0) m (List.replicate (calls s st) []) = some rs ∧
      endState (some 0) rs = none ∧ FieldCopy m (cutSlot side) iv.1 (dest s base side f) iv.2
        (after m (eventLog rs)) ∧ rs.length = calls s st ∧
      (∀ r ∈ rs, r.probes ≤ probes st) ∧ LiveStageLink.PreservesTag (Fin.ofNat _ base) rs := by
  dsimp only
  let pub := operands w s base side f
  obtain ⟨prefixBound, endFit⟩ := dest_bounds s base side f hf
  have sep : countAddr base < dest s base side f := by
    unfold countAddr adviceBase rightIndexBase leftIndexBase populationAddr highAddr indexBase at *
    omega
  obtain ⟨_, ho, hc, hdword⟩ := scan_public fit.le side f
  have hd : (pub scanSlots.destinationBase).val = dest s base side f := by
    rw [show pub scanSlots.destinationBase = _ from hdword]
    exact Nat.mod_eq_of_lt (by omega)
  have hbase : base < 2^w := by unfold countAddr at sep; omega
  have layout : Allocated.CopyLayout scanSlots pub iv := by
    constructor
    all_goals simp only [Allocated.Outside, hd, show (pub scanSlots.srcOffsetAddress).val = _ from ho,
      show (pub scanSlots.countAddress).val = _ from hc]
    all_goals unfold offsetAddr countAddr at *; omega
  have tag : Allocated.Outside (pub scanSlots.destinationBase).val iv.2
      (Fin.ofNat (2^w) base).val := by
    rw [hd, show (Fin.ofNat (2^w) base).val = base from Nat.mod_eq_of_lt hbase]
    exact Or.inl (by unfold countAddr at sep; omega)
  obtain ⟨rs, run, last, copy, len, hp, frame⟩ := Allocated.copy_bounded hw scanSlots (cutSlot side) pub
    m iv (s.capacity f) (scan_sizes fit.le side f iv capacity (sites.trans scratch))
    (scan_loaded s base fit side f m iv offset count) layout (Fin.ofNat _ base) tag
  rw [hd] at copy
  refine ⟨rs, ?_, last, copy, len, ?_, frame⟩
  · change runSegment (machine w s base side f) _ _ _ _ = _
    rw [run_scan, decide_eq_false hf]
    exact run
  · have hprobes : probes (.scan side f) = 4 := by cases f <;> simp_all [probes]
    rw [hprobes]
    exact hp

/-- A zero padding interval accepts after its scheduled calls and leaves
every scratch cell and every packed processor word intact. -/
theorem padding_run (hw : 4 ≤ w) (s : Sizes) (base d : ℕ) (fit : limit s base < 2^w)
    (scratch : 2^d ≤ base) (side : Side) (m : Memory w) (iv : ℕ × ℕ)
    (sites : iv.1+iv.2 ≤ 2^d) (capacity : iv.2 ≤ s.capacity .padding)
    (offset : (m (offsetAddr base)).val = iv.1) (count : (m (countAddr base)).val = iv.2)
    (zero : Allocated.ZeroPad (cutSlot side) iv m) :
    let st := Stage.scan side .padding
    let P := ((stageTemplate st).2.instantiate w (rowData w s base st)).program
    ∃ rs, runSegment P 25 (some 0) m (List.replicate (calls s st) []) = some rs ∧
      endState (some 0) rs = none ∧ after m (eventLog rs) = m ∧ rs.length = calls s st ∧
      (∀ r ∈ rs, r.probes ≤ probes st) ∧ LiveStageLink.PreservesTag (Fin.ofNat _ base) rs := by
  dsimp only
  obtain ⟨rs, run, last, mem, len, hp, frame⟩ := Allocated.padding_bounded hw scanSlots (cutSlot side)
    (operands w s base side .padding) m iv (s.capacity .padding)
    (scan_sizes fit.le side .padding iv capacity (sites.trans scratch))
    (scan_loaded s base fit side .padding m iv offset count) (Fin.ofNat _ base) zero
  refine ⟨rs, ?_, last, mem, len, hp, frame⟩
  change runSegment (machine w s base side .padding) _ _ _ _ = _
  rw [run_scan]
  exact run

/-- Arbitrary choice strings and an arbitrary source fuel cannot skip a
nonzero occupied padding bit on an accepting row execution. -/
theorem padding_sound (hw : 4 ≤ w) (s : Sizes) (base d : ℕ) (fit : limit s base < 2^w)
    (scratch : 2^d ≤ base) (side : Side) (m : Memory w) (iv : ℕ × ℕ)
    (sites : iv.1+iv.2 ≤ 2^d) (capacity : iv.2 ≤ s.capacity .padding)
    (offset : (m (offsetAddr base)).val = iv.1) (count : (m (countAddr base)).val = iv.2)
    (fuel : ℕ) (bs : List (List Bool)) {rs : List (Report w)}
    (run : runSegment ((stageTemplate (.scan side .padding)).2.instantiate w
      (rowData w s base (.scan side .padding))).program (fuel+3) (some 0) m bs = some rs)
    (last : endState (some 0) rs = none) : Allocated.ZeroPad (cutSlot side) iv m := by
  change runSegment (machine w s base side .padding) _ _ _ _ = _ at run
  rw [run_scan] at run
  exact Allocated.padding_bounded_sound hw scanSlots (cutSlot side) (operands w s base side .padding)
    m iv (s.capacity .padding) (scan_sizes fit.le side .padding iv capacity (sites.trans scratch))
    (scan_loaded s base fit side .padding m iv offset count) fuel bs run last

/-- A complete call must execute the three guard instructions and a terminal instruction. -/
private theorem short_call (s : Sizes) (base : ℕ) (side : Side) (fuel : ℕ) (short : fuel ≤ 3)
    (st : Word w) (m : Memory w) (bits : List Bool) :
    let P := machine w s base side .padding
    execute P fuel (P.start st) m bits = none := by
  dsimp only
  unfold machine stageTemplate
  rw [entry_start]
  interval_cases fuel <;> rfl

/-- Soundness for every total fuel, including attempts to stop during the guard. -/
theorem padding_sound_any (hw : 4 ≤ w) (s : Sizes) (base d : ℕ) (fit : limit s base < 2^w)
    (scratch : 2^d ≤ base) (side : Side) (m : Memory w) (iv : ℕ × ℕ)
    (sites : iv.1+iv.2 ≤ 2^d) (capacity : iv.2 ≤ s.capacity .padding)
    (offset : (m (offsetAddr base)).val = iv.1) (count : (m (countAddr base)).val = iv.2)
    (fuel : ℕ) (bs : List (List Bool)) {rs : List (Report w)}
    (run : runSegment ((stageTemplate (.scan side .padding)).2.instantiate w
      (rowData w s base (.scan side .padding))).program fuel (some 0) m bs = some rs)
    (last : endState (some 0) rs = none) : Allocated.ZeroPad (cutSlot side) iv m := by
  by_cases room : 3 ≤ fuel
  · apply padding_sound hw s base d fit scratch side m iv sites capacity offset count (fuel-3) bs _ last
    rwa [Nat.sub_add_cancel room]
  · cases bs with
    | nil => simp only [runSegment, Option.some.injEq] at run; subst rs; contradiction
    | cons b bs =>
      change runSegment (machine w s base side .padding) fuel (some 0) m (b::bs) = some rs at run
      simp only [runSegment, short_call s base side fuel (by omega) 0 m b] at run
      contradiction

/-- On every successful call of the scheduled padding row, its event log leaves
every replay address intact. This includes returning calls before an eventual
failure and the closing call. No descriptor validity is required. -/
theorem padding_call_frame (s : Sizes) (base : ℕ) (side : Side) (fuel : ℕ) (st : Word w)
    (m : Memory w) (bits : List Bool) {rep : Report w}
    (run : let P := ((stageTemplate (.scan side .padding)).2.instantiate w
      (rowData w s base (.scan side .padding))).program
      execute P fuel (P.start st) m bits = some rep) (addr : Word w) (replay : Memory w) :
    after replay rep.events addr.val = replay addr.val := by
  change execute (machine w s base side .padding) fuel ((machine w s base side .padding).start st) m bits = some rep at run
  by_cases room : 4 ≤ fuel
  · replace run := (execute_scan s base side .padding fuel st m bits).symm.trans run
    let pub := operands w s base side .padding
    let bound : Word w := s.capacity .padding
    let T := Allocated.table scanSlots (cutSlot side) true
    change execute (LiveHeaderBounded.machine T pub bound).program fuel
      ((LiveHeaderBounded.machine T pub bound).program.start st) m bits = some rep at run
    by_cases active : st < bound
    · rw [show fuel = (fuel-3)+3 by omega,
          LiveHeaderBounded.execute_active T pub bound (fuel-3) st active] at run
      obtain ⟨raw, hr, rfl⟩ := Option.map_eq_some_iff.mp run
      exact Allocated.report_frame scanSlots (cutSlot side) true pub st m bits (fuel-3) hr addr
        (fun _ => Or.inl rfl) replay
    · rw [show fuel = (fuel-4)+4 by omega,
          LiveHeaderBounded.execute_closed T pub bound (fuel-4) st (le_of_not_gt active)] at run
      split at run
      · obtain rfl := Option.some.inj run
        rfl
      · contradiction
  · rw [short_call s base side fuel (by omega) st m bits] at run
    contradiction

end LiveHeaderProgram.ScanRows

end VPVNP
end Computability
end OAI
