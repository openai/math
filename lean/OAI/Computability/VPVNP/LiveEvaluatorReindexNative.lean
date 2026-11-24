import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMRecords
import OAI.Computability.VPVNP.LiveHeaderRuns

/-!
# Native scatter of dense exponent bits into the initial evaluator tape

The incoming cut stores one bit per word, in dense label order and
least-significant digit first. The map table gives the formal evaluator label
of each dense label. On the evaluator tape the exponent payload is in reverse
order and one delimiter separates consecutive payload symbols. A native call
reads one bit and one map entry, and writes exactly one tape symbol.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorReindex

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Public words are the incoming bit base, label-map base, first exponent
payload symbol address, bits per label, and total number of payload bits. -/
def scatterOps : List (Op 32 5) :=
  [.constant 1 1, .stateWord 26, .publicWord 4 4, .publicWord 3 3,
   .publicWord 5 0, .binary .add 5 5 26, .read 6 5,
   .publicWord 7 1, .binary .div 8 26 3, .binary .add 7 7 8, .read 9 7,
   .binary .mul 9 9 3, .binary .mod 10 26 3, .binary .add 9 9 10,
   .binary .sub 11 4 1, .binary .sub 11 11 9, .binary .add 11 11 11,
   .publicWord 12 2, .binary .add 11 12 11, .binary .add 6 6 1,
   .write 11 6, .binary .add 29 26 1]

/-- The source address of one serialized exponent bit on the incoming cut. -/
def incomingAddress (pub : Fin 5 → Word w) (q : Word w) := pub 0 + q

/-- The address of the formal label ordinal corresponding to the dense exponent row containing
this bit. -/
def mapAddress (pub : Fin 5 → Word w) (q : Word w) :=
  pub 1 + BinaryOp.div.eval q (pub 3)

/-- The bit index in formal label order, combining the mapped label ordinal with the bit's
within-row position. -/
def formalBit (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :=
  m (mapAddress pub q).val * pub 3 + BinaryOp.mod.eval q (pub 3)

/-- The bit's destination in the reverse-ordered evaluator tape payload, accounting for the
interleaved delimiter cells. -/
def targetAddress (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :=
  let back := pub 4 - 1 - formalBit pub q m
  pub 2 + (back + back)

/-- Encode the incoming exponent bit as a nonblank evaluator tape symbol by adding one. -/
def inputSymbol (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :=
  m (incomingAddress pub q).val + 1

/-- The two reads precede the write, so the read values are both from the
memory at entry. All arithmetic and cursor updates produce ticks. -/
def scatterEvents (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) : List (Event w) :=
  [.tick,.tick,.tick,.tick,.tick,.tick,.read (incomingAddress pub q) (m (incomingAddress pub q).val),
   .tick,.tick,.tick,.read (mapAddress pub q) (m (mapAddress pub q).val),
   .tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,
   .write (targetAddress pub q m) (inputSymbol pub q m),.tick]

theorem scatterEvents_counts (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :
    (scatterEvents pub q m).length = 22 ∧ countProbes (scatterEvents pub q m) = 3 ∧
    choiceBits (scatterEvents pub q m) = [] := ⟨rfl,rfl,rfl⟩

theorem after_scatterEvents (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :
    after m (scatterEvents pub q m) =
      writeMemory m (targetAddress pub q m) (inputSymbol pub q m) := rfl

theorem scatter_trace (pub : Fin 5 → Word w) (q : Word w) (rs : Regs w 32) (m : Memory w) :
    ∃ out, trace pub q scatterOps rs m = some (scatterEvents pub q m, out,
      writeMemory m (targetAddress pub q m) (inputSymbol pub q m)) ∧
      out 29 = q+1 ∧ out 4 = pub 4 := by
  simp (config := {decide := true}) [scatterOps, trace, Op.effect, Function.update,
    BinaryOp.eval, scatterEvents, incomingAddress, mapAddress, targetAddress, formalBit, inputSymbol]

theorem scatter_native (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :
    let P := ((template scatterOps 29).instantiate w pub).program
    execute P 23 (P.start q) m [] = some ⟨scatterEvents pub q m,some (q+1)⟩ := by
  obtain ⟨out,ht,hr,-⟩ := scatter_trace pub q (fun _ => 0) m
  change execute ((template scatterOps 29).instantiate w pub).program (1 + scatterOps.length) ⟨_,q,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hr]

theorem incomingAddress_val (pub : Fin 5 → Word w) (q : Word w)
    (fit : (pub 0).val + q.val < 2 ^ w) :
    (incomingAddress pub q).val = (pub 0).val + q.val := Nat.mod_eq_of_lt fit

private theorem div_val (q z : Word w) : (BinaryOp.div.eval q z).val = q.val / z.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt q.isLt)

private theorem mod_val (q z : Word w) : (BinaryOp.mod.eval q z).val = q.val % z.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt q.isLt)

theorem mapAddress_val (pub : Fin 5 → Word w) (q : Word w)
    (fit : (pub 1).val + q.val / (pub 3).val < 2 ^ w) :
    (mapAddress pub q).val = (pub 1).val + q.val / (pub 3).val := by
  rw [mapAddress, Fin.val_add, div_val, Nat.mod_eq_of_lt fit]

/-- With a valid formal bit number, its product and digit addition fit a
word. The two subtractions are in increasing distance from the right end. -/
theorem targetAddress_val (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) (hw : 2 ≤ w)
    (formal : (m (mapAddress pub q).val).val * (pub 3).val + q.val % (pub 3).val < (pub 4).val)
    (fit : (pub 2).val + 2 * ((pub 4).val - 1 -
      ((m (mapAddress pub q).val).val * (pub 3).val + q.val % (pub 3).val)) < 2 ^ w) :
    (targetAddress pub q m).val = (pub 2).val + 2 * ((pub 4).val - 1 -
      ((m (mapAddress pub q).val).val * (pub 3).val + q.val % (pub 3).val)) := by
  have total := (pub 4).isLt
  have one : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hf : (formalBit pub q m).val = (m (mapAddress pub q).val).val * (pub 3).val +
      q.val % (pub 3).val := by
    rw [formalBit, Fin.val_add, Fin.val_mul, mod_val,
      Nat.mod_eq_of_lt (by omega : (m (mapAddress pub q).val).val * (pub 3).val < 2 ^ w),
      Nat.mod_eq_of_lt (formal.trans total)]
  have ht : (pub 4 - 1).val = (pub 4).val - 1 := by
    rw [Fin.sub_val_of_le, one]
    change (1 : Word w).val ≤ _
    omega
  have hb : (pub 4 - 1 - formalBit pub q m).val =
      (pub 4).val - 1 - ((m (mapAddress pub q).val).val * (pub 3).val + q.val % (pub 3).val) := by
    rw [Fin.sub_val_of_le, ht, hf]
    change (formalBit pub q m).val ≤ (pub 4 - 1).val
    omega
  dsimp only [targetAddress]
  rw [Fin.val_add, Fin.val_add, hb, ← two_mul, Nat.add_mod_mod, Nat.mod_eq_of_lt fit]

theorem inputSymbol_val (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) (hw : 2 ≤ w)
    (bit : (m (incomingAddress pub q).val).val < 2) :
    (inputSymbol pub q m).val = (m (incomingAddress pub q).val).val + 1 := by
  have cap : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  rw [inputSymbol, Fin.val_add_one_of_lt' (by omega)]

/-- The phase enters through a cursor check. A completed final write
accepts in the same burst. On an empty array the initial call accepts
without accessing either array or the destination tape. -/
def scatterPhase : Template 30 32 5 where
  literalWidth := 2
  entry := 26
  code i := if h : i.val < scatterOps.length then
      (scatterOps[i.val]).emit ⟨i.val + 1, by have : scatterOps.length = 22 := rfl; omega⟩ 25
    else if i = 22 then .jumpEq 29 4 24 23
    else if i = 23 then .returnState 29
    else if i = 24 then .accept
    else if i = 26 then .publicWord 4 4 27
    else if i = 27 then .stateWord 26 28
    else if i = 28 then .jumpLt 26 4 0 29
    else if i = 29 then .jumpEq 26 0 24 25
    else .reject

/-- Three entry ticks and a final cursor test surround the two reads and
one write of the scatter block. -/
def phaseEvents (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) : List (Event w) :=
  .tick :: .tick :: .tick :: (scatterEvents pub q m ++ [.tick])

theorem phaseEvents_counts (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :
    (phaseEvents pub q m).length = 26 ∧ countProbes (phaseEvents pub q m) = 3 ∧
    choiceBits (phaseEvents pub q m) = [] := ⟨rfl,rfl,rfl⟩

theorem after_phaseEvents (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) :
    after m (phaseEvents pub q m) =
      writeMemory m (targetAddress pub q m) (inputSymbol pub q m) := rfl

private theorem contains_scatter (pub : Fin 5 → Word w) :
    Contains (scatterPhase.instantiate w pub) 25 0 scatterOps 22 := by
  repeat' first | exact .nil _ | refine .cons (next := _) rfl ?_

private theorem phase_entry (pub : Fin 5 → Word w) (q : Word w) (m : Memory w)
    (bs : List Bool) (fuel : ℕ) (hq : q < pub 4) :
    let M := scatterPhase.instantiate w pub
    let rs : Regs w 32 := Function.update (Function.update (fun _ => 0) 4 (pub 4)) 26 q
    execute M.program (fuel+3) (M.program.start q) m bs =
      (execute M.program fuel ⟨0,q,rs,fun _ => 0⟩ m bs).map
        (fun r => r.prepend .tick |>.prepend .tick |>.prepend .tick) := by
  dsimp only
  simp (config := {decide := true}) [execute, Machine.program, scatterPhase, Template.instantiate,
    Instr.resize, Instr.run, Config.put, Function.update, hq, Option.map_map, Function.comp_def]

private theorem phase_finish (pub : Fin 5 → Word w) (q : Word w) (rs : Regs w 32)
    (m : Memory w) (bs : List Bool) (fuel : ℕ) :
    let M := scatterPhase.instantiate w pub
    execute M.program (fuel+2) ⟨22,q,rs,fun _ => 0⟩ m bs =
      if bs = [] then some ⟨[.tick], if rs 29 = rs 4 then none else some (rs 29)⟩ else none := by
  by_cases hb : bs = [] <;> by_cases he : rs 29 = rs 4 <;>
    simp (config := {decide := true}) [execute, Machine.program, scatterPhase, Template.instantiate,
      Instr.resize, Instr.run, Report.prepend, hb, he]

/-- Exact execution of the entire native phase on every active cursor and
choice stream. A nonterminal call returns the next cursor. -/
theorem execute_phase_active (pub : Fin 5 → Word w) (q : Word w) (m : Memory w)
    (bs : List Bool) (fuel : ℕ) (hq : q < pub 4) :
    let P := (scatterPhase.instantiate w pub).program
    execute P (fuel+27) (P.start q) m bs =
      if bs = [] then some ⟨phaseEvents pub q m, if q+1 = pub 4 then none else some (q+1)⟩ else none := by
  let rs : Regs w 32 := Function.update (Function.update (fun _ => 0) 4 (pub 4)) 26 q
  have hc := (contains_scatter pub).execute (by rfl) q rs (fun _ => 0) m bs (fuel+2)
  have ⟨out,ht,hn,htotal⟩ := scatter_trace pub q rs m
  dsimp only
  rw [show fuel+27 = (fuel+2+scatterOps.length)+3 by rfl, phase_entry pub q m bs _ hq,
    hc, run_eq_trace]
  change ((trace pub q scatterOps rs m).bind _).map _ = _
  rw [ht, Option.bind_some]
  dsimp only
  rw [phase_finish, hn, htotal]
  by_cases hb : bs = [] <;> simp [hb, phaseEvents, Report.prepend]

/-- A zero-capacity phase at its initial cursor consumes no choices and
does no memory operations. -/
theorem execute_phase_empty (pub : Fin 5 → Word w) (m : Memory w) (bs : List Bool)
    (fuel : ℕ) (empty : pub 4 = 0) :
    let P := (scatterPhase.instantiate w pub).program
    execute P (fuel+5) (P.start 0) m bs =
      if bs = [] then some ⟨[.tick,.tick,.tick,.tick],none⟩ else none := by
  by_cases hb : bs = [] <;> simp (config := {decide := true}) [execute, Machine.program, scatterPhase,
    Template.instantiate, Instr.resize, Instr.run, Config.put, empty, Report.prepend, hb]

/-- Positive out-of-range cursors cannot accept the phase. -/
theorem execute_phase_past (pub : Fin 5 → Word w) (q : Word w) (m : Memory w) (bs : List Bool)
    (fuel : ℕ) (past : pub 4 ≤ q) (positive : q ≠ 0) :
    let P := (scatterPhase.instantiate w pub).program
    execute P (fuel+5) (P.start q) m bs = none := by
  simp (config := {decide := true}) [execute, Machine.program, scatterPhase, Template.instantiate,
    Instr.resize, Instr.run, Config.put, Function.update, not_lt.mpr past, positive]

/-- A complete native scatter sweep. Every nonempty row contributes its
payload calls, with the final call accepting. The empty sweep uses its
single accepting entry check and preserves the initial memory. -/
theorem scatterPhase_segment (pub : Fin 5 → Word w) (T : ℕ) (total : (pub 4).val = T)
    (inv : ℕ → Memory w → Prop) (original : Memory w) (init : inv 0 original)
    (step : ∀ j < T, ∀ m, inv j m → inv (j+1) (after m (phaseEvents pub (j : Word w) m))) :
    let P := (scatterPhase.instantiate w pub).program
    ∃ rs, runSegment P 27 (some 0) original (List.replicate (max 1 T) []) = some rs ∧
      endState (some 0) rs = none ∧ inv T (after original (eventLog rs)) ∧
      rs.length = max 1 T ∧ ∀ r ∈ rs, countProbes r.events ≤ 3 := by
  let P := (scatterPhase.instantiate w pub).program
  cases T with
  | zero =>
    let last : Report w := ⟨[.tick,.tick,.tick,.tick],none⟩
    have he : execute P 27 (P.start 0) original [] = some last := by
      simpa only [ite_true] using execute_phase_empty pub original [] 22 (Fin.ext total)
    refine ⟨[last], ?_, rfl, init, rfl, ?_⟩
    · change (match execute P 27 (P.start 0) original [] with
        | none => none | some r => some [r]) = some [last]
      rw [he]
    · intro r hr
      have := List.mem_singleton.mp hr
      subst r
      change 0 ≤ 3
      decide
  | succ n =>
    have fit := (pub 4).isLt
    have val (j : ℕ) (hj : j ≤ n+1) : (j : Word w).val = j :=
      Fin.val_cast_of_lt (by omega)
    have call (j : ℕ) (hj : j ≤ n) (m : Memory w) :
        execute P 27 (P.start (j : Word w)) m [] =
          some ⟨phaseEvents pub (j : Word w) m, if j = n then none else some ((j+1 : ℕ) : Word w)⟩ := by
      have hq : (j : Word w) < pub 4 := by
        rw [Fin.lt_def, val _ (by omega), total]
        omega
      have hn : (j : Word w) + 1 = ((j+1 : ℕ) : Word w) := by simp
      have iff : ((j+1 : ℕ) : Word w) = pub 4 ↔ j = n := by
        rw [Fin.ext_iff, val _ (by omega), total]
        omega
      simpa only [ite_true, hn, iff] using execute_phase_active pub (j : Word w) m [] 0 hq
    obtain ⟨rs,hr,hs,hi,hl,hp⟩ := LiveHeader.run_cursor_segment P 27 n 3 inv original init
      (fun j hj m hm => ⟨phaseEvents pub (j : Word w) m, by
        simpa only [ite_eq_right (Nat.ne_of_lt hj)] using call j hj.le m,
        step j (by omega) m hm, (phaseEvents_counts pub _ m).2.1.le⟩)
    let m := after original (eventLog rs)
    let last : Report w := ⟨phaseEvents pub (n : Word w) m, none⟩
    have he : execute P 27 (P.start (n : Word w)) m [] = some last := by
      simpa only [ite_true] using call n le_rfl m
    rw [max_eq_right (by omega : 1 ≤ n+1)]
    refine ⟨rs ++ [last], ?_, ?_, ?_, by simp [hl], ?_⟩
    · rw [List.replicate_succ', PrimedSchedule.runSegment_append, hr]
      simp only [Option.bind_some, hs, runSegment]
      rw [he]
      rfl
    · rw [endState_append]
      rfl
    · simpa only [last, m, eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append]
        using step n (by omega) m hi
    · intro r hr'
      rcases List.mem_append.mp hr' with h | h
      · exact hp r h
      · have eq : r = last := List.mem_singleton.mp h
        exact eq ▸ (phaseEvents_counts pub (n : Word w) m).2.1.le

/-- An accepting run from any cursor consumes exactly its remaining calls,
each with the empty choice stream. This includes runs of arbitrary
proposed lengths and establishes uniqueness of the initialization path. -/
theorem scatterPhase_choices (pub : Fin 5 → Word w) (q : Word w) (m : Memory w)
    (bs : List (List Bool)) (rs : List (Report w)) (fuel : ℕ)
    (run : runSegment (scatterPhase.instantiate w pub).program (fuel+27) (some q) m bs = some rs)
    (halt : endState (some q) rs = none) :
    bs = List.replicate (max 1 ((pub 4).val - q.val)) [] := by
  induction bs generalizing q m rs with
  | nil =>
    change some [] = some rs at run
    cases run
    contradiction
  | cons b bs ih =>
    let P := (scatterPhase.instantiate w pub).program
    rw [runSegment] at run
    cases h : execute P (fuel+27) (P.start q) m b with
    | none => simp [P] at h; simp [h] at run
    | some r =>
      change execute (scatterPhase.instantiate w pub).program (fuel+27)
        ((scatterPhase.instantiate w pub).program.start q) m b = some r at h
      rw [h, Option.map_eq_some_iff] at run
      obtain ⟨rest, tail, rfl⟩ := run
      change endState r.result rest = none at halt
      have final (done : r.result = none) : bs = [] := by
        rw [done] at tail
        cases bs <;> first | rfl | contradiction
      by_cases active : q < pub 4
      · rw [execute_phase_active pub q m b fuel active] at h
        split at h
        · rename_i empty
          subst b
          obtain rfl := (Option.some.inj h).symm
          have hv : (q+1).val = q.val+1 := Fin.val_add_one_of_lt' ((Nat.succ_le_of_lt active).trans_lt (pub 4).isLt)
          by_cases last : q+1 = pub 4
          · rw [final (ite_eq_left last)]
            have he := congrArg Fin.val last
            rw [hv] at he
            rw [show max 1 ((pub 4).val - q.val) = 1 by omega]
            rfl
          · rw [ite_eq_right last] at tail halt
            rw [ih (q+1) _ _ tail halt]
            have hlt : q.val < (pub 4).val := active
            have hne : (q+1).val ≠ (pub 4).val := fun e => last (Fin.ext e)
            rw [hv] at hne ⊢
            rw [show max 1 ((pub 4).val - q.val) = max 1 ((pub 4).val - (q.val+1)) + 1 by omega,
              List.replicate_succ]
        · contradiction
      · by_cases zero : q = 0
        · subst q
          have empty : pub 4 = 0 := Fin.ext (by
            change ¬ (0 : Word w).val < (pub 4).val at active
            simpa using Nat.eq_zero_of_not_pos active)
          rw [show fuel+27 = (fuel+22)+5 by omega, execute_phase_empty pub m b _ empty] at h
          split at h
          · rename_i hb
            subst b
            obtain rfl := (Option.some.inj h).symm
            rw [final rfl]
            simp [empty]
          · contradiction
        · rw [show fuel+27 = (fuel+22)+5 by omega,
            execute_phase_past pub q m b _ (le_of_not_gt active) zero] at h
          contradiction

end LiveEvaluatorReindex

end VPVNP
end Computability
end OAI
