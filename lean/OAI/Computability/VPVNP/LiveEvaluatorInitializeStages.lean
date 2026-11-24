import OAI.Computability.VPVNP.LiveEvaluatorInitializeSweep
import OAI.Computability.VPVNP.PrimedCounterRename

/-!
# Linkable stages for the evaluator endpoints

The control-word write accepts immediately. The tape-copy stage returns its
cursor on an intermediate bit and accepts on the last bit. If the public
active length is zero, one call accepts without reading or writing memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorInitialize

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM LiveEvaluatorEncoding
open scoped Fin.CommRing

variable {w : ℕ}

/-- The control-word write is a complete native stage. -/
def putStage (tag : Word 2) : Template 4 32 4 where
  literalWidth := 2
  entry := 0
  code
    | 0 => .publicWord 23 1 1
    | 1 => .constant 16 tag 2
    | 2 => .writeExternal 23 16 3
    | 3 => .accept

/-- Exact result and branch string for the one-call stage. -/
theorem execute_putStage (tag : Word 2) (pub : Fin 4 → Word w) (s : Word w)
    (m : Memory w) (bits : List Bool) (f : ℕ) :
    let P := ((putStage tag).instantiate w pub).program
    execute P (f+4) (P.start s) m bits = if bits = [] then
      some ⟨[.tick, .tick, .write (pub 1) (Fin.ofNat _ tag.val)], none⟩ else none := by
  cases bits <;> rfl

/-- The endpoint stage that writes the accepting control word and finishes in one call. -/
abbrev finalStage : Template 4 32 4 := putStage 1

/-- One native stage prepares the accepting endpoint in its scratch bank. -/
theorem finalStage_stores {extra M : ℕ} (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w)
    (pub : Fin 4 → Word w) (s : Word w) (m : Memory w)
    (zero : ∀ k : Fin (fieldWords M), m ((pub 1).val + k.val) = 0) :
    let P := (finalStage.instantiate w pub).program
    ∃ es, execute P 4 (P.start s) m [] = some ⟨es, none⟩ ∧
      Stores hw hs (pub 1).val (after m es) (.accepted : Code extra M) ∧
      es.length = 3 ∧ countProbes es = 1 ∧ choiceBits es = [] := by
  refine ⟨[.tick, .tick, .write (pub 1) 1], ?_, final_stores hw hs _ _ zero, rfl, rfl, rfl⟩
  exact execute_putStage 1 pub s m [] 0

private def copyOps : List (Op 32 5) := copyBit.map (PrimedCounter.renameOp id Fin.castSucc)

/-- The fifth public word is the active bit length. The entry guard bypasses
the packed input for a zero-length sweep. The exit test hands off the stage
on the call that actually wrote the last input symbol. -/
def copyStage : Template 25 32 5 where
  literalWidth := 2
  entry := 21
  code i := if h : i.val < copyOps.length then
      copyOps[i.val].emit ⟨i.val+1, by have : copyOps.length = 18 := rfl; omega⟩ 24
    else if i = 18 then .jumpLt 29 30 19 20
    else if i = 19 then .returnState 29
    else if i = 20 then .accept
    else if i = 21 then .stateWord 26 22
    else if i = 22 then .publicWord 30 4 23
    else if i = 23 then .jumpLt 26 30 0 20
    else .reject

/-- Place the active bit count after the four existing evaluator operands. -/
def copyPublic (pub : Fin 4 → Word w) (count : Word w) : Fin 5 → Word w := Fin.snoc pub count

private theorem contains_copy (data : Fin 5 → Word w) :
    Contains (copyStage.instantiate w data) 24 0 copyOps 18 := by
  iterate 18 apply Contains.cons rfl
  exact .nil _

private def entryRegs (s count : Word w) : Regs w 32 :=
  Function.update (Function.update (fun _ => 0) 26 s) 30 count

private theorem execute_entry (data : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (f : ℕ) (hs : s < data 4) :
    let M := copyStage.instantiate w data
    execute M.program (f+3) (M.program.start s) m bits =
      (execute M.program f ⟨0,s,entryRegs s (data 4),fun _ => 0⟩ m bits).map
        (fun r => r.prepend .tick |>.prepend .tick |>.prepend .tick) := by
  dsimp only
  simp (config := { decide := true }) [execute, Machine.program, copyStage, Template.instantiate,
    Instr.resize, Instr.run, Config.put, Function.update, hs, Option.map_map, Function.comp_def, entryRegs, copyOps, copyBit]

/-- When the cursor is already at the public capacity, the guard accepts
with three local ticks and leaves memory intact. -/
theorem execute_copyStage_skip (data : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (f : ℕ) (hs : data 4 ≤ s) :
    let P := (copyStage.instantiate w data).program
    execute P (f+4) (P.start s) m bits =
      if bits = [] then some ⟨[.tick,.tick,.tick], none⟩ else none := by
  cases bits <;>
    simp (config := { decide := true }) [execute, Machine.program, copyStage, Template.instantiate,
      Instr.resize, Instr.run, Config.put, Function.update, not_lt.mpr hs, copyOps, copyBit, Report.prepend]

private theorem execute_exit (data : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (f : ℕ) (regs : Regs w 32) :
    let M := copyStage.instantiate w data
    execute M.program (f+2) ⟨18,s,regs,fun _ => 0⟩ m bits =
      if bits = [] then some ⟨[.tick], if regs 29 < regs 30 then some (regs 29) else none⟩ else none := by
  by_cases h : regs 29 < regs 30 <;> cases bits <;>
    simp (config := { decide := true }) [execute, Machine.program, copyStage, Template.instantiate,
      Instr.resize, Instr.run, h, copyOps, copyBit, Report.prepend]

/-- Execute one active bit at any sufficient instruction cap. Only the
empty branch string succeeds. Every such call performs the packed source
read, the destination write, and four extra control ticks. -/
theorem execute_copyStage_active_replay (hw : 2 ≤ w) (pub : Fin 4 → Word w)
    (width : (pub 3).val = w) (bound s : Word w) (active : s < bound)
    (m : Memory w) (bits : List Bool) (f : ℕ) :
    let P := (copyStage.instantiate w (copyPublic pub bound)).program
    let bit := (m (sourceAddress pub s).val).val.testBit (s.val % w)
    ∃ es, execute P (f+23) (P.start s) m bits = (if bits = [] then
      some ⟨es, if s+1 < bound then some (s+1) else none⟩ else none) ∧
      after m es = writeMemory m (targetAddress pub s) (PrimedInputRAM.encodeBit w bit + 1) ∧
      es.length = 22 ∧ countProbes es = 2 ∧ choiceBits es = [] ∧
      ∀ u, after u es = writeMemory u (targetAddress pub s) (PrimedInputRAM.encodeBit w bit + 1) := by
  let data := copyPublic pub bound
  have hdata : data 4 = bound := Fin.snoc_last ..
  let regs := entryRegs s bound
  obtain ⟨es, out, ht, hout, hmem, hl, hp, hb, replay⟩ := copyBit_trace_replay hw pub width s regs m
  have hout' : out 30 = bound := by
    have hf : out 30 = regs 30 := trace_preserves (by decide : ∀ op ∈ copyBit, op.destination ≠ some 30) ht
    rw [hf]
    exact Function.update_self ..
  have ht' : trace data s copyOps regs m = _ := ht
  let M := copyStage.instantiate w data
  have hrun := (contains_copy data).execute (by rfl) s regs (fun _ => 0) m bits (f+2)
  change execute M.program (f+20) ⟨0,s,regs,fun _ => 0⟩ m bits = _ at hrun
  rw [run_eq_trace] at hrun
  change trace M.publicData s copyOps regs m = _ at ht'
  rw [ht'] at hrun
  dsimp only [Option.bind_some] at hrun
  rw [execute_exit data, hout, hout'] at hrun
  dsimp only
  refine ⟨.tick :: .tick :: .tick :: (es ++ [.tick]), ?_, ?_, by simp [hl], ?_, ?_, ?_⟩
  · change execute M.program (f+23) (M.program.start s) m bits = _
    rw [show f+23 = (f+20)+3 by omega, execute_entry data s m bits _ (by rwa [hdata]), hdata, hrun]
    cases bits <;> simp [Report.prepend]
  · simpa [after, List.foldl_append, update] using hmem
  · change countProbes (es ++ [.tick]) = 2
    have ha (xs : List (Event w)) : countProbes (xs ++ [.tick]) = countProbes xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => cases x <;> simp [countProbes, ih]
    rwa [ha]
  · change choiceBits (es ++ [.tick]) = []
    have ha (xs : List (Event w)) : choiceBits (xs ++ [.tick]) = choiceBits xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => cases x <;> simp [choiceBits, ih]
    rwa [ha]

  · intro u
    simpa only [after, List.foldl_append, List.foldl_cons, List.foldl_nil, update] using replay u

theorem execute_copyStage_active (hw : 2 ≤ w) (pub : Fin 4 → Word w)
    (width : (pub 3).val = w) (bound s : Word w) (active : s < bound)
    (m : Memory w) (bits : List Bool) (f : ℕ) :
    let P := (copyStage.instantiate w (copyPublic pub bound)).program
    let bit := (m (sourceAddress pub s).val).val.testBit (s.val % w)
    ∃ es, execute P (f+23) (P.start s) m bits = (if bits = [] then
      some ⟨es, if s+1 < bound then some (s+1) else none⟩ else none) ∧
      after m es = writeMemory m (targetAddress pub s) (PrimedInputRAM.encodeBit w bit + 1) ∧
      es.length = 22 ∧ countProbes es = 2 ∧ choiceBits es = [] := by
  obtain ⟨es, run, effect, size, probes, choices, _⟩ :=
    execute_copyStage_active_replay hw pub width bound s active m bits f
  exact ⟨es, run, effect, size, probes, choices⟩

private abbrev copyProgram (pub : Fin 4 → Word w) :=
  ((template copyBit 29).instantiate w pub).program

private abbrev stageProgram (pub : Fin 4 → Word w) (count : Word w) :=
  (copyStage.instantiate w (copyPublic pub count)).program

/-- The bounded and unbounded copies differ only in control events and their
return state. They read and write the same actual memory. -/
private theorem copy_pair (hw : 2 ≤ w) (pub : Fin 4 → Word w) (width : (pub 3).val = w)
    (bound s : Word w) (active : s < bound) (m : Memory w) :
    ∃ es fs, execute (copyProgram pub) 19 ((copyProgram pub).start s) m [] = some ⟨es,some (s+1)⟩ ∧
      execute (stageProgram pub bound) 23 ((stageProgram pub bound).start s) m [] =
        some ⟨fs, if s+1 < bound then some (s+1) else none⟩ ∧
      after m es = after m fs ∧ fs.length = 22 ∧ countProbes fs = 2 ∧ choiceBits fs = [] := by
  obtain ⟨es, out, ht, ho, hm, _, _, _⟩ := copyBit_trace hw pub width s (fun _ => 0) m
  obtain ⟨fs, hf, hm', hl, hp, hb⟩ := execute_copyStage_active hw pub width bound s active m [] 0
  refine ⟨es,fs,?_,hf,hm.trans hm'.symm,hl,hp,hb⟩
  change execute (copyProgram pub) (1+copyBit.length) ⟨_,s,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [ho]

private theorem eventLog_after_cons (m : Memory w) (r : Report w) (rs : List (Report w)) :
    after m (eventLog (r :: rs)) = after (after m r.events) (eventLog rs) := by
  simp [after, eventLog, List.foldl_append]

private theorem replay_positive (hw : 2 ≤ w) (pub : Fin 4 → Word w) (width : (pub 3).val = w)
    (bound : Word w) (n j : ℕ) (remaining : j + (n+1) = bound.val) (m : Memory w)
    (old : List (Report w))
    (hr : runSegment (copyProgram pub) 19 (some (j : Word w)) m (List.replicate (n+1) []) = some old) :
    ∃ rs, runSegment (stageProgram pub bound) 23 (some (j : Word w)) m (List.replicate (n+1) []) = some rs ∧
      endState (some (j : Word w)) rs = none ∧ after m (eventLog rs) = after m (eventLog old) ∧
      rs.length = n+1 ∧ ∀ r ∈ rs, r.events.length = 22 ∧ countProbes r.events = 2 ∧ choiceBits r.events = [] := by
  induction n generalizing j m old with
  | zero =>
    have hj : (j : Word w).val = j := Fin.val_cast_of_lt (by have := bound.isLt; omega)
    have hactive : (j : Word w) < bound := Fin.lt_def.mpr (by omega)
    have hnext : (j : Word w) + 1 = bound := by
      apply Fin.ext
      rw [Fin.val_add_one_of_lt' (by have := bound.isLt; omega), hj]; omega
    obtain ⟨es, fs, he, hf, hm, hl, hp, hb⟩ := copy_pair hw pub width bound _ hactive m
    change runSegment (copyProgram pub) 19 (some (j : Word w)) m [[]] = some old at hr
    simp only [runSegment, he, Option.map_some, Option.some.injEq] at hr
    subst old
    simp only [hnext, lt_irrefl, ite_false] at hf
    refine ⟨[⟨fs,none⟩], ?_, rfl, ?_, rfl, ?_⟩
    · change runSegment (stageProgram pub bound) 23 (some (j : Word w)) m [[]] = _
      simp [runSegment, hf]
    · simpa [eventLog] using hm.symm
    · simpa using And.intro hl (And.intro hp hb)
  | succ n ih =>
    have hj : (j : Word w).val = j := Fin.val_cast_of_lt (by have := bound.isLt; omega)
    have hactive : (j : Word w) < bound := Fin.lt_def.mpr (by omega)
    have hcast : (j : Word w)+1 = ((j+1 : ℕ) : Word w) := by simp
    have hnext : (j : Word w)+1 < bound :=
      Fin.lt_def.mpr (by rw [Fin.val_add_one_of_lt' (by have := bound.isLt; omega), hj]; omega)
    obtain ⟨es, fs, he, hf, hm, hl, hp, hb⟩ := copy_pair hw pub width bound _ hactive m
    rw [ite_eq_left hnext, hcast] at hf
    rw [hcast] at he
    rw [List.replicate_succ, runSegment, he] at hr
    obtain ⟨oldTail, ht, rfl⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨rs, hrun, hend, hmem, hlen, hcost⟩ := ih (j+1) (by omega) (after m es) oldTail ht
    let r : Report w := ⟨fs, some ((j+1 : ℕ) : Word w)⟩
    refine ⟨r :: rs, ?_, hend, ?_, by simpa only [List.length_cons] using congrArg (·+1) hlen, ?_⟩
    · rw [List.replicate_succ, runSegment, hf]
      dsimp only
      rw [← hm, hrun]
      rfl
    · simpa only [eventLog_after_cons, r, ← hm] using hmem
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hl,hp,hb⟩
      · exact hcost t ht

/-- Starting at cursor zero, the copy stage uses exactly one call per active
bit, or one empty skip for a zero-length input. Its last call accepts, and its
memory contains the same initialized symbols as the unbounded copy sweep. -/
theorem copyStage_sweep (hw : 2 ≤ w) (pub : Fin 4 → Word w) (width : (pub 3).val = w)
    (p : UniversalMachine.Program) (raw : UniversalMachine.Word) (original : Memory w)
    (fit : firstData pub + activeLength p raw ≤ 2 ^ w)
    (packed : ∀ j < activeLength p raw,
      original (sourceAddress pub (j : Word w)).val = inputWord w raw (j / w))
    (disjoint : ∀ j < activeLength p raw, (sourceAddress pub (j : Word w)).val < firstData pub ∨
      firstData pub + activeLength p raw ≤ (sourceAddress pub (j : Word w)).val) :
    let count := activeLength p raw
    let P := (copyStage.instantiate w (copyPublic pub (count : Word w))).program
    ∃ rs, runSegment P 23 (some 0) original (List.replicate (max 1 count) []) = some rs ∧
      endState (some 0) rs = none ∧ Copied raw (firstData pub) count original (after original (eventLog rs)) ∧
      rs.length = max 1 count ∧ ∀ r ∈ rs,
        r.events.length ≤ 22 ∧ countProbes r.events ≤ 2 ∧ choiceBits r.events = [] := by
  dsimp only
  let count := activeLength p raw
  have hfit : count < 2 ^ w := by dsimp [firstData] at fit; change activeLength p raw < _; omega
  have hval : (count : Word w).val = count := Fin.val_cast_of_lt hfit
  obtain ⟨old, hr, _, hcopy, _, _⟩ := copy_segment hw pub width p raw original fit packed disjoint
  change runSegment (copyProgram pub) 19 (some 0) original (List.replicate count []) = some old at hr
  change Copied raw _ count _ _ at hcopy
  change ∃ rs : List (Report w), runSegment (stageProgram pub (count : Word w)) 23 (some 0) original (List.replicate (max 1 count) []) = some rs ∧
    endState (some 0) rs = none ∧ Copied raw _ count original (after original (eventLog rs)) ∧ rs.length = max 1 count ∧ _
  cases hc : count with
  | zero =>
    rw [hc] at hr hcopy
    simp only [List.replicate_zero, runSegment, Option.some.injEq] at hr
    subst old
    let r : Report w := ⟨[.tick,.tick,.tick],none⟩
    refine ⟨[r], ?_, rfl, hcopy, rfl, ?_⟩
    · change (runSegment (stageProgram pub 0) 23 (some 0) original [[]]) = _
      have he := execute_copyStage_skip (copyPublic pub 0) 0 original [] 19
        (by have heq : copyPublic pub 0 4 = 0 := Fin.snoc_last ..; exact heq.le)
      rw [runSegment, he]
      rfl
    · simp [r, countProbes, choiceBits]
  | succ n =>
    rw [max_eq_right (by omega : 1 ≤ n+1)]
    rw [hc] at hval hcopy
    have hr' : runSegment (copyProgram pub) 19 (some (0 : Word w)) original (List.replicate (n+1) []) = some old := by
      simpa [hc] using hr
    obtain ⟨rs, hrun, hend, hm, hl, hp⟩ := replay_positive hw pub width ((n+1 : ℕ) : Word w)
      n 0 (by omega) original old hr'
    refine ⟨rs,hrun,hend,hm ▸ hcopy,hl,?_⟩
    intro r hr
    obtain ⟨h₁,h₂,h₃⟩ := hp r hr
    exact ⟨h₁.le,h₂.le,h₃⟩

/-- The two accepting stages, with a fresh cursor at the handoff, prepare the
actual evaluator's initial bank from the packed input words. -/
theorem prepareStages (hw : 2 ≤ w) (pub : Fin 4 → Word w) (width : (pub 3).val = w)
    (p : UniversalMachine.Program) (hs : p.extra + 2 ≤ 2 ^ w)
    (raw : UniversalMachine.Word) (blank : Memory w)
    (space : raw.length ≤ (pub 0).val + 1)
    (fit : firstData pub + activeLength p raw ≤ 2 ^ w)
    (zero : ∀ k : Fin (fieldWords (pub 0).val), blank ((pub 1).val + k.val) = 0)
    (packed : ∀ j < activeLength p raw, blank (sourceAddress pub (j : Word w)).val = inputWord w raw (j / w))
    (disjoint : ∀ j < activeLength p raw, let a := (sourceAddress pub (j : Word w)).val
      a ≠ (pub 1).val ∧ (a < firstData pub ∨ firstData pub + activeLength p raw ≤ a)) :
    let count := activeLength p raw
    let S := ((putStage (controlTag p)).instantiate w pub).program
    let P := (copyStage.instantiate w (copyPublic pub (count : Word w))).program
    ∃ es rs, execute S 4 (S.start 0) blank [] = some ⟨es,none⟩ ∧
      runSegment P 23 (some 0) (after blank es) (List.replicate (max 1 count) []) = some rs ∧
      endState (some 0) rs = none ∧ Stores hw hs (pub 1).val (after (after blank es) (eventLog rs))
        (LiveEvaluatorTail.initialCode (pub 0).val (UniversalMachine.initial p raw)) ∧
      es.length = 3 ∧ countProbes es = 1 ∧ choiceBits es = [] ∧ rs.length = max 1 count ∧
      ∀ r ∈ rs, r.events.length ≤ 22 ∧ countProbes r.events ≤ 2 ∧ choiceBits r.events = [] := by
  let es : List (Event w) := [.tick,.tick,.write (pub 1) (Fin.ofNat _ (controlTag p).val)]
  have hm : after blank es = writeMemory blank (pub 1) (Fin.ofNat _ (controlTag p).val) := rfl
  have saved (j : ℕ) (hj : j < activeLength p raw) :
      after blank es (sourceAddress pub (j : Word w)).val = inputWord w raw (j / w) := by
    rw [hm, writeMemory, ite_eq_right (disjoint j hj).1, packed j hj]
  obtain ⟨rs, hrun, hend, hcopy, hl, hp⟩ :=
    copyStage_sweep hw pub width p raw (after blank es) fit saved (fun j hj => (disjoint j hj).2)
  refine ⟨es, rs, execute_putStage _ _ _ _ _ 0, hrun, hend, ?_, rfl, rfl, rfl, hl, hp⟩
  exact copied_stores hw pub p hs raw blank _ space zero hcopy

end LiveEvaluatorInitialize

end VPVNP
end Computability
end OAI
