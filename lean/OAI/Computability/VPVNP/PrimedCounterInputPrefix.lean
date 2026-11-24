import OAI.Computability.VPVNP.PrimedCounterInputPrefixCall
import OAI.Computability.VPVNP.PrimedCounterPostHistory
import OAI.Computability.VPVNP.PrimedCounterLength

/-!
# The input prefix in the complete coefficient counter

The combined table assembles the two full rectangles before any parser call. Every
accepted raw tape begins with precisely the choice lists of one internal assignment.
The reports of this prefix include the combined table's private dispatch ticks and
carry the assembled memory to the first parser cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.InputPrefix

open BurstRAM PrimedInputRAM Opcodes

variable {L : Lengths} {n r H w s : ℕ} {Q : Layout L n r H w}

/-- Every physical assembler report acquires the same private dispatch padding. -/
theorem reports_padded (D : Data Q s) (F : D.Fits) (g : Fin D.assembly → Bool)
    (cells : List (Fin D.assembly)) (m : Memory w) :
    (calls D F).dataReports g cells m = ((physicalSchedule Q F.assembler).dataReports g cells m).map padded := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    simp only [ReturningCalls.dataReports, PhysicalSchedule.dataReports, reportList, List.map_cons] at ih ⊢
    exact congrArg (_ :: ·) (ih _)

private theorem prefix_bounds (D : Data Q s) (F : D.Fits) (g : Fin D.assembly → Bool)
    (cells : List (Fin D.assembly)) (m : Memory w) (hm : CutMemory L m) :
    ((calls D F).dataReports g cells m).length = cells.length ∧
      ∀ p ∈ (calls D F).dataReports g cells m, p.probes ≤ 5 := by
  induction cells generalizing m with
  | nil => exact ⟨rfl, fun _ h ↦ False.elim (List.not_mem_nil h)⟩
  | cons i cells ih =>
    let R := physicalSchedule Q F.assembler
    obtain ⟨hlen,hprobes⟩ := ih _ (R.closed i m (g i) hm)
    refine ⟨congrArg Nat.succ hlen, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ht
    · change (padded (R.report i m (g i))).probes ≤ 5
      rw [padded_probes, R.probes _ _ _ hm]
      have h := Item.report_probes (nativeOps Q i) (encodeBit w) 0 m (g i)
      rw [Item.probes_eq_probeCount] at h
      omega
    · exact hprobes _ ht

private theorem padded_cost (xs : List (Report w)) :
    RAMBuckets.cost Report.probes (xs.map padded) = RAMBuckets.cost Report.probes xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [RAMBuckets.cost, ih]

/-- The actual report prefix reaches the grammar cursor with the required memory,
preserves the header words and costs at most eleven units per tape position. -/
theorem run (D : Data Q s) (F : D.Fits) (bits : Chronology.Bits L r H w) :
    let pre := (calls D F).dataReports (cursorBits Q bits) (List.finRange D.assembly) D.initial
    runSegment D.machine.program D.fuel (some 0) D.initial (List.ofFn (Chronology.inputCalls Q bits)) = some pre ∧
      endState (some 0) pre = some (cursor Q.cursorFits D.assembly le_rfl) ∧
      after D.initial (eventLog pre) = Q.assembled (encodeBit w) bits D.initial ∧
      RAMBuckets.cost Report.probes pre ≤ 11 * PrimedInputRAM.positions n r := by
  dsimp only
  let g := cursorBits Q bits
  let xs := List.finRange D.assembly
  have hm := cutMemory_header Q D.header D.hist
  have hrun := (calls D F).splice g D.initial hm []
  rw [List.append_nil, runSegment, Option.map_some, List.append_nil] at hrun
  refine ⟨?_, (calls D F).prefix_endState g D.initial hm, ?_, ?_⟩
  · rw [List.ofFn_eq_map]
    exact hrun
  · rw [reports_padded]
    have same (rs : List (Report w)) (m : Memory w) :
        after m (eventLog (rs.map padded)) = after m (eventLog rs) := by
      induction rs generalizing m with
      | nil => rfl
      | cons a rs ih =>
        simp only [eventLog, List.map_cons, List.flatMap_cons, after, List.foldl_append] at ih ⊢
        exact (ih _).trans (congrArg (fun x ↦ (rs.flatMap Report.events).foldl update x) (padded_memory a m))
    exact (same _ _).trans (input_prefix Q F.assembler bits D.initial hm).2.2.1
  · rw [reports_padded, padded_cost]
    exact (input_prefix Q F.assembler bits D.initial hm).2.2.2

private theorem assignment_of_total (g : Fin (PrimedInputRAM.positions n r + PrimedInputRAM.positions n r) → Bool) :
    ∃ bits : Chronology.Bits L r H w, Chronology.inputCalls Q bits = fun i ↦ (nativeOps Q i).bits (g i) := by
  let T := Q.twoPass (encodeBit w)
  let f : Assignment (fun i ↦ (nativeOps Q i).owns) := fun i ↦ g i.val
  let a := T.assignmentEquiv.symm f
  let bits : Chronology.Bits L r H w := a ∘ Q.internalOwner
  have ha : Q.assignment bits = a := by
    funext i
    change a (Q.internalOwner (Q.internalOwner.symm i)) = a i
    rw [Equiv.apply_symm_apply]
  refine ⟨bits, ?_⟩
  funext i
  change (nativeOps Q i).bits (bitAt (T.assignmentEquiv (Q.assignment bits)) i) = _
  rw [ha, show T.assignmentEquiv a = f from T.assignmentEquiv.apply_symm_apply f]
  change (T.ops i).bits (bitAt f i) = (T.ops i).bits (g i)
  cases h : (T.ops i).owns
  · simp only [Item.bits, h, Bool.false_eq_true, ↓reduceIte]
  · have hn : (nativeOps Q i).owns = true := h
    simp only [Item.bits, bitAt, h, hn, ↓reduceIte]
    rfl

/-- Complete characterization at the boundary of the input phase, independently
of every later parser and histogram choice. A malformed data call rejects here. -/
theorem run_iff (D : Data Q s) (F : D.Fits) (inputTape : Fin D.assembly → List Bool)
    (rs : List (Report w)) :
    runSegment D.machine.program D.fuel (some 0) D.initial (List.ofFn inputTape) = some rs ↔
      ∃ bits : Chronology.Bits L r H w, inputTape = Chronology.inputCalls Q bits ∧
        rs = (calls D F).dataReports (cursorBits Q bits) (List.finRange D.assembly) D.initial := by
  constructor
  · intro hr
    obtain ⟨g, hg⟩ := (calls D F).choices_of_length D.initial (cutMemory_header Q D.header D.hist)
      (List.ofFn inputTape) rs hr List.length_ofFn
    obtain ⟨bits, hb⟩ := assignment_of_total (Q := Q) g
    have he : inputTape = Chronology.inputCalls Q bits := by
      apply List.ofFn_injective
      rw [hb, List.ofFn_eq_map (f := fun i ↦ (nativeOps Q i).bits (g i))]
      exact hg
    rw [he] at hr
    exact ⟨bits, he, Option.some.inj (hr.symm.trans (run D F bits).1)⟩
  · rintro ⟨bits, rfl, rfl⟩
    exact (run D F bits).1

/-- After the physical input prefix the entire remaining native run is the parser
and histogram suffix, including its possible rejection. -/
theorem full_splice (D : Data Q s) (F : D.Fits) (raw : Chronology.PairTape n r D.labels)
    (bits : Chronology.Bits L r H w) (he : Chronology.inputPart raw = Chronology.inputCalls Q bits) :
    ∃ pre : List (Report w),
      runSegment D.machine.program D.fuel (some 0) D.initial (List.ofFn raw) =
        (D.postNative bits raw).map (pre ++ ·) ∧
      pre.length = D.assembly ∧ ∀ rep ∈ pre, rep.probes ≤ 14 := by
  let xs := List.finRange D.assembly
  let g := cursorBits Q bits
  let pre := (calls D F).dataReports g xs D.initial
  have hm := cutMemory_header Q D.header D.hist
  have h := (calls D F).splice g D.initial hm (D.postTape raw)
  have hb := prefix_bounds D F g xs D.initial hm
  refine ⟨pre, ?_, hb.1.trans List.length_finRange, fun rep hrep ↦ (hb.2 _ hrep).trans (by decide)⟩
  rw [← D.postTape_append raw, he, List.ofFn_eq_map]
  unfold Data.postNative
  rw [show PrimedSchedule.control w D.total D.assembly = some (cursor Q.cursorFits D.assembly le_rfl) by
      rw [PrimedSchedule.control, ite_eq_left (assembly_lt_total D)]
      exact congrArg some (Fin.ext (Nat.mod_eq_of_lt Q.cursorFits))]
  exact h.trans (congrArg (fun m ↦ (runSegment D.machine.program D.fuel
      (some (cursor Q.cursorFits D.assembly le_rfl)) m (D.postTape raw)).map (pre ++ ·))
    ((Q.twoPass (encodeBit w)).scheduledMemory_eq _ Q.cursorFits (Q.assignment bits) D.initial))

/-- A successful full native execution forces an internal assignment's exact
per-cell choice streams in the input portion of the raw tape. -/
theorem full_recover (D : Data Q s) (F : D.Fits) (raw : Chronology.PairTape n r D.labels)
    (rs : List (Report w))
    (hr : runSegment D.machine.program D.fuel (some 0) D.initial (List.ofFn raw) = some rs) :
    ∃ bits : Chronology.Bits L r H w, Chronology.inputPart raw = Chronology.inputCalls Q bits := by
  obtain ⟨g, suffix, _, hc, _, _, _⟩ := (calls D F).recover D.initial (cutMemory_header Q D.header D.hist)
    (List.ofFn raw) rs hr (D.history_end F hr)
  obtain ⟨bits,hbits⟩ := assignment_of_total (Q := Q) g
  refine ⟨bits, List.ofFn_injective ?_⟩
  have ht := congrArg (List.take D.assembly) ((D.postTape_append raw).trans hc)
  rw [hbits, List.ofFn_eq_map]
  have takePrefix (f : Fin D.assembly → List Bool) (xs : List (List Bool)) :
      List.take D.assembly ((List.finRange D.assembly).map f ++ xs) = (List.finRange D.assembly).map f := by
    convert (List.take_left (l₁ := (List.finRange D.assembly).map f) (l₂ := xs)) using 1; simp
  simpa only [List.ofFn_eq_map, takePrefix] using ht

end PrimedCounter.InputPrefix

end VPVNP
end Computability
end OAI
