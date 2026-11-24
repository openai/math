import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionLayout

/-!
# Transferring the physical input prefix to the grammar phase

The data calls of Section 11 return after the second pass with the assembled memory.
They can be used in a larger program whose data calls are linked to the same opcodes
and whose terminal cursor enters the parser. The residual stream of parser calls is
arbitrary and is passed unchanged to that cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {w M : ℕ} {C : Type*} {P : Program w C} {fuel : ℕ} {ops : Fin M → Item w}
  {bitWord : Bool → Word w} {fit : M < 2^w} {Pre : Memory w → Prop}

/-- Data calls of an enclosing program. Its phase transition can continue in the grammar
parser, and the extra private ticks of its dispatch may differ from the standalone RAM. -/
structure ReturningCalls (P : Program w C) (fuel : ℕ) (ops : Fin M → Item w)
    (bitWord : Bool → Word w) (fit : M < 2^w) (Pre : Memory w → Prop) where
  /-- Report of one input-stage call in the enclosing program, indexed by the scheduled item,
  incoming memory and supplied bit. -/
  report : Fin M → Memory w → Bool → Report w
  data : ∀ i m b, Pre m → execute P fuel (P.start (cursor fit i.val i.isLt.le)) m
    ((ops i).bits b) = some (report i m b)
  result : ∀ i m b, Pre m → (report i m b).result = some (successor fit i)
  memory : ∀ i m b, Pre m → after m (report i m b).events = (ops i).memory bitWord m b
  closed : ∀ i m b, Pre m → Pre ((ops i).memory bitWord m b)

/-- Per-item reports before a continuation takes control. -/
def reportList (ops : Fin M → Item w) (bitWord : Bool → Word w)
    (report : Fin M → Memory w → Bool → Report w) (g : Fin M → Bool) :
    List (Fin M) → Memory w → List (Report w)
  | [], _ => []
  | i :: xs, m => report i m (g i) :: reportList ops bitWord report g xs ((ops i).memory bitWord m (g i))

namespace ReturningCalls

variable (D : ReturningCalls P fuel ops bitWord fit Pre)

/-- Reports of successive returning input-stage calls, threading each item's memory update into
the next call. -/
abbrev dataReports := reportList ops bitWord D.report

private theorem dataReports_end (g : Fin M → Bool) (xs : List (Fin M)) (k : ℕ) (hk : k ≤ M)
    (ha : Aligned k xs) (m : Memory w) (hm : Pre m) :
    endState (some (cursor fit k hk)) (D.dataReports g xs m) = some (cursor fit M le_rfl) := by
  induction xs generalizing k m with
  | nil =>
    have he : k = M := by simpa using ha.2
    subst k
    rfl
  | cons i xs ih =>
    obtain ⟨hi, ht⟩ := aligned_cons ha
    subst k
    rw [dataReports, reportList, endState, D.result _ _ _ hm]
    exact ih _ i.isLt ht _ (D.closed _ _ _ hm)

/-- The actual data reports, taken without the halt, end at the first parser cursor. -/
theorem prefix_endState (g : Fin M → Bool) (m : Memory w) (hm : Pre m) :
    endState (some 0) (D.dataReports g (List.finRange M) m) = some (cursor fit M le_rfl) :=
  D.dataReports_end g _ 0 (Nat.zero_le _) (aligned_all M) m hm

private theorem splice_aux
    (g : Fin M → Bool) (xs : List (Fin M)) (k : ℕ) (hk : k ≤ M) (ha : Aligned k xs)
    (m : Memory w) (hm : Pre m) (tail : List (List Bool)) :
    runSegment P fuel (some (cursor fit k hk)) m (xs.map (fun i ↦ (ops i).bits (g i)) ++ tail) =
      (runSegment P fuel (some (cursor fit M le_rfl)) (scheduledMemory ops bitWord g xs m) tail).map
        (D.dataReports g xs m ++ ·) := by
  induction xs generalizing k m with
  | nil =>
    have he : k = M := by simpa using ha.2
    subst k
    simp [dataReports, reportList, scheduledMemory]
  | cons i xs ih =>
    obtain ⟨hi, ht⟩ := aligned_cons ha
    subst k
    simp only [List.map_cons, List.cons_append, runSegment, D.data _ _ _ hm, D.memory _ _ _ hm,
      D.result _ _ _ hm, dataReports, reportList, scheduledMemory]
    rw [show successor fit i = cursor fit (i.val+1) i.isLt by rfl, ih _ _ ht _ (D.closed _ _ _ hm)]
    simp only [Option.map_map, Function.comp_def]

/-- Any enclosing burst program with the physical data-call implementations can resume
at cursor `M`. Its exit behavior and its remaining private branch streams are unrestricted. -/
theorem splice
    (g : Fin M → Bool) (m : Memory w) (hm : Pre m) (tail : List (List Bool)) :
    runSegment P fuel (some 0) m ((List.finRange M).map (fun i ↦ (ops i).bits (g i)) ++ tail) =
      (runSegment P fuel (some (cursor fit M le_rfl))
        (scheduledMemory ops bitWord g (List.finRange M) m) tail).map
        (D.dataReports g (List.finRange M) m ++ ·) :=
  D.splice_aux g _ 0 (Nat.zero_le _) (aligned_all M) m hm tail

include D in
private theorem choices_of_prefix_aux
    (xs : List (Fin M)) (k : ℕ) (hk : k ≤ M) (ha : Aligned k xs)
    (m : Memory w) (hm : Pre m) (bits : List (List Bool)) (rs : List (Report w))
    (hr : runSegment P fuel (some (cursor fit k hk)) m bits = some rs)
    (hfull : xs.length ≤ bits.length ∨ endState (some (cursor fit k hk)) rs = none) :
    ∃ g : Fin M → Bool, ∃ suffix, bits = xs.map (fun i ↦ (ops i).bits (g i)) ++ suffix := by
  induction xs generalizing k m bits rs with
  | nil => exact ⟨fun _ ↦ false, bits, rfl⟩
  | cons i xs ih =>
    obtain ⟨hi, ht⟩ := aligned_cons ha
    have fresh := aligned_fresh ha
    subst k
    cases bits with
    | nil => simp [runSegment] at hr; subst rs; simp [endState] at hfull
    | cons bs more =>
      obtain ⟨a,ts,he,htail,rfl⟩ := unpack_call P fuel _ _ _ _ _ hr
      obtain ⟨b, rfl⟩ := only_item_choices (ops i) (D.report i m) (fun b ↦ D.data i m b hm) he
      obtain rfl := Option.some.inj (he.symm.trans (D.data i m b hm))
      rw [D.result _ _ _ hm, D.memory _ _ _ hm] at htail
      simp only [List.length_cons, Nat.add_le_add_iff_right, endState, D.result _ _ _ hm] at hfull
      obtain ⟨g,suffix,rfl⟩ := ih _ i.isLt ht _ (D.closed _ _ _ hm) more ts htail hfull
      refine ⟨Function.update g i b, suffix, ?_⟩
      simp only [List.map_cons, List.cons_append, Function.update_self, List.cons.injEq, true_and]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hne : j ≠ i := fun e ↦ fresh (e ▸ hj)
      rw [Function.update_of_ne hne]

/-- Conversely, every accepting execution of the enclosing program must pass all the
input cursors with their prescribed branch streams. Its suffix starts at the grammar
cursor, consumes the remaining streams, and finishes with an accepting halt. -/
theorem recover (m : Memory w) (hm : Pre m)
    (bits : List (List Bool)) (rs : List (Report w))
    (hr : runSegment P fuel (some 0) m bits = some rs) (hend : endState (some 0) rs = none) :
    ∃ (g : Fin M → Bool) (suffix : List (List Bool)) (tail : List (Report w)),
      bits = (List.finRange M).map (fun i ↦ (ops i).bits (g i)) ++ suffix ∧
      rs = D.dataReports g (List.finRange M) m ++ tail ∧
      runSegment P fuel (some (cursor fit M le_rfl))
        (scheduledMemory ops bitWord g (List.finRange M) m) suffix = some tail ∧
      endState (some (cursor fit M le_rfl)) tail = none := by
  obtain ⟨g,suffix,rfl⟩ := D.choices_of_prefix_aux _ 0 (Nat.zero_le _) (aligned_all M)
    m hm bits rs hr (Or.inr hend)
  rw [D.splice g m hm suffix, Option.map_eq_some_iff] at hr
  obtain ⟨tail,hcont,rfl⟩ := hr
  exact ⟨g, suffix, tail, rfl, rfl, hcont, by simpa only [endState_append, D.prefix_endState g m hm] using hend⟩

include D in
/-- If exactly the data calls have returned, every choice list must have the
scheduled shape, even when the later program rejects. -/
theorem choices_of_length (m : Memory w) (hm : Pre m) (bits : List (List Bool))
    (rs : List (Report w)) (hr : runSegment P fuel (some 0) m bits = some rs)
    (hlen : bits.length = M) :
    ∃ g : Fin M → Bool, bits = (List.finRange M).map (fun i ↦ (ops i).bits (g i)) := by
  obtain ⟨g, suffix, hb⟩ := D.choices_of_prefix_aux _ 0 (Nat.zero_le _) (aligned_all M)
    m hm bits rs hr (Or.inl (by simp [hlen]))
  have hs : suffix = [] := by
    rw [hb, List.length_append, List.length_map, List.length_finRange] at hlen
    exact List.length_eq_zero_iff.mp (by omega)
  exact ⟨g, by simpa only [hs, List.append_nil] using hb⟩

end ReturningCalls

namespace PhysicalSchedule

variable (R : PhysicalSchedule P fuel ops bitWord fit Pre)

/-- Reports for the specified physical data calls in order, using the memory produced by each
preceding item. -/
abbrev dataReports := reportList ops bitWord R.report

/-- Keep the per-cursor implementations and leave the terminal call to the enclosing
program. -/
def returningCalls {C' : Type*} (P' : Program w C') (fuel' : ℕ)
    (hdata : ∀ i m b, Pre m → execute P' fuel' (P'.start (cursor fit i.val i.isLt.le)) m
      ((ops i).bits b) = some (R.report i m b)) : ReturningCalls P' fuel' ops bitWord fit Pre :=
  ⟨R.report, hdata, R.result, R.memory, R.closed⟩

theorem dataReports_matched (g : Fin M → Bool) (xs : List (Fin M)) (m : Memory w) (hm : Pre m) :
    MatchedReports m (R.dataReports g xs m) (scheduledReports ops bitWord fit g xs m) := by
  induction xs generalizing m with
  | nil => exact .nil m
  | cons i xs ih =>
    apply MatchedReports.cons
    · rw [R.result _ _ _ hm, Item.report_result]
    · rw [R.memory _ _ _ hm, Item.after_report]
    · simp only [R.probes _ _ _ hm, Item.probes_eq_probeCount, Item.report_result]
      rfl
    · rw [Item.after_report]
      exact ih _ (R.closed _ _ _ hm)

theorem dataReports_cost (g : Fin M → Bool) (xs : List (Fin M)) (m : Memory w) (hm : Pre m) :
    RAMBuckets.cost Report.probes (R.dataReports g xs m) =
      RAMBuckets.cost Report.probes (scheduledReports ops bitWord fit g xs m) + 3*xs.length := by
  induction xs generalizing m with
  | nil => rfl
  | cons i xs ih =>
    have ht := ih _ (R.closed i m (g i) hm)
    dsimp only [dataReports] at ht
    simp only [dataReports, reportList, scheduledReports, RAMBuckets.cost, List.length_cons, R.probes _ _ _ hm,
      Item.probes_eq_probeCount]
    omega

/-- The actual data reports, taken without the halt, end at the first parser cursor. -/
theorem prefix_endState (g : Fin M → Bool) (m : Memory w) (hm : Pre m) :
    endState (some 0) (R.dataReports g (List.finRange M) m) = some (cursor fit M le_rfl) :=
  (R.returningCalls P fuel R.data).prefix_endState g m hm

/-- Any enclosing burst program with the physical data-call implementations can resume
at cursor `M`. Its exit behavior and its remaining private branch streams are unrestricted. -/
theorem splice_data {C' : Type*} (P' : Program w C') (fuel' : ℕ)
    (hdata : ∀ i m b, Pre m → execute P' fuel' (P'.start (cursor fit i.val i.isLt.le)) m
      ((ops i).bits b) = some (R.report i m b))
    (g : Fin M → Bool) (m : Memory w) (hm : Pre m) (tail : List (List Bool)) :
    runSegment P' fuel' (some 0) m ((List.finRange M).map (fun i ↦ (ops i).bits (g i)) ++ tail) =
      (runSegment P' fuel' (some (cursor fit M le_rfl))
        (scheduledMemory ops bitWord g (List.finRange M) m) tail).map
        (R.dataReports g (List.finRange M) m ++ ·) :=
  (R.returningCalls P' fuel' hdata).splice g m hm tail

/-- Conversely, every accepting execution of the enclosing program must pass all the
input cursors with their prescribed branch streams. Its suffix starts at the grammar
cursor, consumes the remaining streams, and finishes with an accepting halt. -/
theorem recover_data_prefix {C' : Type*} (P' : Program w C') (fuel' : ℕ)
    (hdata : ∀ i m b, Pre m → execute P' fuel' (P'.start (cursor fit i.val i.isLt.le)) m
      ((ops i).bits b) = some (R.report i m b)) (m : Memory w) (hm : Pre m)
    (bits : List (List Bool)) (rs : List (Report w))
    (hr : runSegment P' fuel' (some 0) m bits = some rs) (hend : endState (some 0) rs = none) :
    ∃ (g : Fin M → Bool) (suffix : List (List Bool)) (tail : List (Report w)),
      bits = (List.finRange M).map (fun i ↦ (ops i).bits (g i)) ++ suffix ∧
      rs = R.dataReports g (List.finRange M) m ++ tail ∧
      runSegment P' fuel' (some (cursor fit M le_rfl))
        (scheduledMemory ops bitWord g (List.finRange M) m) suffix = some tail ∧
      endState (some (cursor fit M le_rfl)) tail = none :=
  (R.returningCalls P' fuel' hdata).recover m hm bits rs hr hend

/-- The generated native data calls without the halt. -/
theorem run_data (g : Fin M → Bool) (m : Memory w) (hm : Pre m) :
    runSegment P fuel (some 0) m ((List.finRange M).map (fun i ↦ (ops i).bits (g i))) =
      some (R.dataReports g (List.finRange M) m) := by
  simpa [runSegment] using R.splice_data P fuel R.data g m hm []

end PhysicalSchedule

namespace Opcodes

variable {L : Lengths} {n r H w : ℕ}

/-- Extend the internal assignment to every cursor; only owner positions consume these bits. -/
def cursorBits (Q : Layout L n r H w) (bits : Internal L r H w → Bool) :=
  bitAt ((Q.twoPass (encodeBit w)).assignmentEquiv (Q.assignment bits))

/-- Generated data-call prefix for the actual, finite opcode table. Its cost omits the
terminal call, and its return cursor and memory are ready for the parser. -/
theorem input_prefix (Q : Layout L n r H w) (F : ParameterFit Q) (bits : Internal L r H w → Bool)
    (m : Memory w) (hm : CutMemory L m) :
    let R := physicalSchedule Q F
    let g := cursorBits Q bits
    let cells := List.finRange (positions n r + positions n r)
    let rs := R.dataReports g cells m
    runSegment (nativeMachine Q).program (nativeFuel r) (some 0) m
        (cells.map (fun i ↦ (nativeOps Q i).bits (g i))) = some rs ∧
      endState (some 0) rs = some (cursor Q.cursorFits _ le_rfl) ∧
      after m (eventLog rs) = Q.assembled (encodeBit w) bits m ∧
      RAMBuckets.cost Report.probes rs ≤ 11 * positions n r := by
  dsimp only
  let R := physicalSchedule Q F
  let T := Q.twoPass (encodeBit w)
  let g := cursorBits Q bits
  let cells := List.finRange (positions n r + positions n r)
  refine ⟨R.run_data g m hm, R.prefix_endState g m hm, ?_, ?_⟩
  · exact ((R.dataReports_matched g cells m hm).after_eq.trans
      (after_scheduledReports _ _ _ _ _ _)).trans
      (T.scheduledMemory_eq _ Q.cursorFits (Q.assignment bits) m)
  · rw [R.dataReports_cost _ _ _ hm, List.length_finRange]
    have h := T.completeReports_cost_le (encodeBit w) Q.cursorFits (Q.assignment bits) m
    simp only [TwoPass.completeReports, RAMBuckets.cost_append, haltReport, RAMBuckets.cost,
      Report.probes, countProbes] at h
    change RAMBuckets.cost Report.probes (scheduledReports T.ops _ Q.cursorFits g cells m) + _ ≤ _
    change RAMBuckets.cost Report.probes (scheduledReports T.ops _ Q.cursorFits g cells m) + 1 ≤ 5 * positions n r + 1 at h
    omega

end Opcodes
end PrimedInputRAM

end VPVNP
end Computability
end OAI
