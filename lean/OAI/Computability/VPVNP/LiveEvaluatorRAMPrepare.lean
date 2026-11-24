import OAI.Computability.VPVNP.LiveEvaluatorRAMDispatch
import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedStackRAMLeafVisit

/-!
# Preparing a live evaluator transition

The first scheduled call checks the old state, reads the two heads of a
running configuration, chooses a row slot, and checks the proposed output
state. It writes the selected target, first write and move, and second write
and move to five consecutive scratch words. An accepting source carries
state one and four zeros without a choice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAMPrepare

open BurstRAM (Word Memory Event choiceBits countProbes writeMemory)
open BurstRAM.PrivateRAM (BinaryOp)
open PrimedInputRAM (Flow)
open PrimedStackRAM (Op Regs lines trace)
open UniversalMachine (Program Instruction Branches chosenInstruction)
open LiveEvaluatorRAMDispatch

/-- The transition-preparation flow with 32 registers and four public configuration operands. -/
abbrev Code := Flow 32 4
private abbrev Ops := List (Op 32 4)
variable {w : ℕ}

/-- The head of the first tape follows the state word and the left half-window. -/
def firstAddress (rs : Regs w 32) : Word w := rs 23 + rs 1 + rs 11

/-- The second tape starts one complete window after the first. -/
def secondAddress (rs : Regs w 32) : Word w := firstAddress rs + rs 22

/-- Read the symbol under the old first-tape head from its external configuration address. -/
def firstHead (rs : Regs w 32) (m : Memory w) := m (firstAddress rs).val
/-- Read the symbol under the old second-tape head from its external configuration address. -/
def secondHead (rs : Regs w 32) (m : Memory w) := m (secondAddress rs).val

/-- The zero-based row number computed in machine-word arithmetic. -/
def rowNumber (rs : Regs w 32) (m : Memory w) : Word w :=
  (rs 16 - rs 2) * (rs 3 * rs 3) + firstHead rs m * rs 3 + secondHead rs m

private def rowOps : Ops :=
  [.binary .add 10 23 1, .binary .add 10 10 11, .read 17 10, .guardLt 17 3,
   .binary .add 10 10 22, .read 18 10, .guardLt 18 3,
   .binary .mul 19 3 3, .binary .sub 4 16 2, .binary .mul 4 4 19,
   .binary .mul 20 17 3, .binary .add 4 4 20, .binary .add 4 4 18]

private def indexRow : Code := lines rowOps (by decide)

/-- The register bank after reading both heads and computing the instruction row indexed by the
old state and the two symbols. -/
def rowRegs (rs : Regs w 32) (m : Memory w) : Regs w 32 :=
  let s := Function.update rs 10 (firstAddress rs)
  let s := Function.update s 17 (firstHead rs m)
  let s := Function.update s 10 (secondAddress rs)
  let s := Function.update s 18 (secondHead rs m)
  let s := Function.update s 19 (rs 3 * rs 3)
  let s := Function.update s 4 ((rs 16 - rs 2) * (rs 3 * rs 3))
  let s := Function.update s 20 (firstHead rs m * rs 3)
  Function.update s 4 (rowNumber rs m)

/-- The two external head reads and arithmetic ticks used to locate the running configuration's
dispatch row. -/
def rowTrace (rs : Regs w 32) (m : Memory w) : List (Event w) :=
  [.tick,.tick,.read (firstAddress rs) (firstHead rs m),.tick,.tick,
    .read (secondAddress rs) (secondHead rs m),.tick,.tick,.tick,.tick,.tick,.tick,.tick]

set_option maxHeartbeats 2000000 in
private theorem indexRow_iff (pub : Fin 4 → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (es out m') :
    Flow.Exec pub state indexRow rs m es out m' ↔
      firstHead rs m < rs 3 ∧ secondHead rs m < rs 3 ∧
      es = rowTrace rs m ∧ out = rowRegs rs m ∧ m' = m := by
  rw [indexRow, PrimedCounter.Admin.exec_lines_iff_trace]
  by_cases ha : firstHead rs m < rs 3 <;> by_cases hb : secondHead rs m < rs 3
  all_goals
    simp only [firstHead, secondHead, firstAddress, secondAddress] at ha hb
    simp (config := {decide := true}) [rowOps, trace, Op.effect, BinaryOp.eval,
      rowTrace, rowRegs, rowNumber, firstHead, secondHead, firstAddress, secondAddress,
      Function.update, ha, hb] <;> try tauto

private def carryOps : Ops :=
  [.copy 5 1,.copy 6 0,.copy 7 0,.copy 8 0,.copy 9 0]

private def carry : Code := lines carryOps (by decide)

/-- Set the instruction registers to the accepting carry transition, with target one and zero
tape writes and motions. -/
def carryRegs (rs : Regs w 32) : Regs w 32 :=
  let s := Function.update rs 5 (rs 1)
  let s := Function.update s 6 (rs 0)
  let s := Function.update s 7 (rs 0)
  let s := Function.update s 8 (rs 0)
  Function.update s 9 (rs 0)

private theorem carry_iff (pub : Fin 4 → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (es out m') :
    Flow.Exec pub state carry rs m es out m' ↔ es = ticks 5 ∧ out = carryRegs rs ∧ m' = m := by
  rw [carry, PrimedCounter.Admin.exec_lines_iff_trace]
  have ht : trace pub state carryOps rs m = some (ticks 5, carryRegs rs, m) := rfl
  rw [ht]; simp [eq_comm]

private def publishOps : Ops :=
  [.guardLt 0 5, .read 10 24, .guardEq 10 5,
   .write 25 5, .binary .add 10 25 1, .write 10 6, .binary .add 10 10 1, .write 10 7,
   .binary .add 10 10 1, .write 10 8, .binary .add 10 10 1, .write 10 9]

private def publish : Code := lines publishOps (by decide)

/-- The physical scratch addresses visited in order; all increments are native word additions. -/
def scratchAddress (rs : Regs w 32) : ℕ → Word w
  | 0 => rs 25
  | i+1 => scratchAddress rs i + rs 1

/-- The exact external memory after the five consecutive writes. -/
def scratchMemory (rs : Regs w 32) (m : Memory w) : Memory w :=
  let m := writeMemory m (scratchAddress rs 0) (rs 5)
  let m := writeMemory m (scratchAddress rs 1) (rs 6)
  let m := writeMemory m (scratchAddress rs 2) (rs 7)
  let m := writeMemory m (scratchAddress rs 3) (rs 8)
  writeMemory m (scratchAddress rs 4) (rs 9)

/-- The register bank at the end of publishing an instruction, with the address cursor on its
fifth scratch word. -/
def publishRegs (rs : Regs w 32) : Regs w 32 := Function.update rs 10 (scratchAddress rs 4)

/-- The destination state read and five scratch writes that publish the checked target, tape
symbols, and motions. -/
def publishTrace (rs : Regs w 32) (m : Memory w) : List (Event w) :=
  [.tick,.read (rs 24) (m (rs 24).val),.tick,.write (scratchAddress rs 0) (rs 5),
    .tick,.write (scratchAddress rs 1) (rs 6),.tick,.write (scratchAddress rs 2) (rs 7),
    .tick,.write (scratchAddress rs 3) (rs 8),.tick,.write (scratchAddress rs 4) (rs 9)]

private theorem publish_iff (pub : Fin 4 → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (es out m') :
    Flow.Exec pub state publish rs m es out m' ↔
      rs 0 < rs 5 ∧ m (rs 24).val = rs 5 ∧
      es = publishTrace rs m ∧ out = publishRegs rs ∧ m' = scratchMemory rs m := by
  rw [publish, PrimedCounter.Admin.exec_lines_iff_trace]
  by_cases hpos : rs 0 < rs 5 <;> by_cases heq : m (rs 24).val = rs 5
  all_goals
    simp (config := {decide := true}) [publishOps, trace, Op.effect, BinaryOp.eval,
      scratchMemory, scratchAddress, publishTrace, publishRegs, Function.update, hpos, heq] <;> try tauto

/-- Install the highest permitted control-state number in the register used for the state bound
check. -/
def boundsRegs (p : Program) (rs : Regs w 32) : Regs w 32 :=
  Function.update rs 5 (Fin.ofNat (2^w) (p.extra+1))

private def reject : Code := .line (.guardLt 0 0)

private def select (p : Program) : Code :=
  .ifEq 16 1 carry (.seq indexRow (dispatch p))

/-- Register 16 is the source state, 11 the window radius, 22 the window length,
23 and 24 the input and output state-word addresses, and 25 the scratch base.
Registers 0 through 3 carry their respective constants. -/
def prepare (p : Program) : Code :=
  .seq (.line (.guardLt 0 16)) <| .seq (targetFlow (p.extra+1)) <|
  .ifLt 5 16 reject (.seq (select p) publish)

/-- Only fixed straight-line blocks and the machine's finite dispatch occur. -/
theorem prepare_loopFree (p : Program) : LiveEvaluatorRAM.loopFree (prepare p) = true := by
  simp only [prepare, select, LiveEvaluatorRAM.loopFree, target_loopFree, dispatch_loopFree,
    show LiveEvaluatorRAM.loopFree carry = true by rfl,
    show LiveEvaluatorRAM.loopFree indexRow = true by rfl,
    show LiveEvaluatorRAM.loopFree publish = true by rfl,
    show LiveEvaluatorRAM.loopFree reject = true by rfl]
  rfl


/-- The fixed program row addressed by the two actual head reads. -/
def tableRow (p : Program) (rs : Regs w 32) (m : Memory w) : Branches p.extra :=
  p.rows[(rowNumber rs m).val]?.getD .stop

/-- The register bank after locating the row and installing the chosen instruction's five
fields. -/
def selectedRegs {extra : ℕ} (rs : Regs w 32) (m : Memory w) (a : Instruction extra) : Regs w 32 :=
  instructionRegs (Function.update (rowRegs rs m) 4 0) a

/-- The two successful possibilities before checking and publishing the proposed target. -/
inductive Selected (p : Program) (rs : Regs w 32) (m : Memory w) :
    List (Event w) → Regs w 32 → Prop
  | carry (h : rs 16 = rs 1) : Selected p rs m (.tick :: ticks 5) (carryRegs rs)
  | slot (h : rs 16 ≠ rs 1) (hf : firstHead rs m < rs 3) (hs : secondHead rs m < rs 3)
      (bit : Bool) (a : Instruction p.extra) (ha : chosenInstruction (tableRow p rs m) bit = some a) :
      Selected p rs m (.tick :: (rowTrace rs m ++ dispatchEvents (rowNumber rs m).val (tableRow p rs m) bit a))
        (selectedRegs rs m a)

private theorem select_iff (p : Program) (pub : Fin 4 → Word w) (st : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (h0 : rs 0 = 0) (h1 : rs 1 = 1) (es out m') :
    Flow.Exec pub st (select p) rs m es out m' ↔ Selected p rs m es out ∧ m' = m := by
  have hr0 : (rowRegs rs m) 0 = 0 := h0
  have hr1 : (rowRegs rs m) 1 = 1 := h1
  constructor
  · intro h
    cases h with
    | ifEqYes he hc =>
      obtain ⟨rfl,rfl,hm⟩ := (carry_iff pub st rs m _ _ _).mp hc
      exact ⟨.carry he,hm⟩
    | ifEqNo he hr =>
      cases hr with
      | seq hi hd =>
        obtain ⟨hf,hs,rfl,rfl,hm⟩ := (indexRow_iff pub st rs m _ _ _).mp hi
        subst_vars
        obtain ⟨bit,a,ha,rfl,rfl,hm'⟩ := (dispatch_exec_iff p pub st _ _ hw hr0 hr1 _ _ _).mp hd
        exact ⟨.slot he hf hs bit a ha,hm'⟩
  · rintro ⟨h,rfl⟩
    cases h with
    | carry he => exact .ifEqYes he ((carry_iff pub st rs _ _ _ _).mpr ⟨rfl,rfl,rfl⟩)
    | slot he hf hs bit a ha =>
      exact .ifEqNo he (.seq ((indexRow_iff pub st rs _ _ _ _).mpr ⟨hf,hs,rfl,rfl,rfl⟩)
        (dispatch_exec p pub st _ _ hw hr0 hr1 bit a ha))

/-- The complete event stream for a successful preparing call. -/
def prepareTrace (p : Program) (fs : List (Event w)) (s : Regs w 32) (m : Memory w) :=
  .tick :: (ticks (p.extra+2) ++ (.tick :: (fs ++ publishTrace s m)))

private theorem guard_iff (pub : Fin 4 → Word w) (st : Word w) (x y : Fin 32)
    (rs : Regs w 32) (m : Memory w) (es out m') :
    Flow.Exec pub st (.line (.guardLt x y)) rs m es out m' ↔
      rs x < rs y ∧ es = [.tick] ∧ out = rs ∧ m' = m := by
  constructor
  · intro h
    cases h with
    | line he =>
      by_cases ht : rs x < rs y
      · simp only [Op.effect, ht, ite_true, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl,rfl,rfl⟩ := he
        exact ⟨ht,rfl,rfl,rfl⟩
      · simp [Op.effect, ht] at he
  · rintro ⟨ht,rfl,rfl,rfl⟩
    exact .line (by simp [Op.effect,ht])

/-- Characterization for *all* raw source words, proposed outputs and choice streams.
A successful run validates the source-state range, the chosen slot, the nonzero target
and the matching output word before performing precisely the five scratch writes. -/
theorem prepare_exec_iff (p : Program) (pub : Fin 4 → Word w) (st : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (hcap : p.extra+2 ≤ 2^w) (h0 : rs 0 = 0) (h1 : rs 1 = 1)
    (es out m') :
    Flow.Exec pub st (prepare p) rs m es out m' ↔
      0 < (rs 16).val ∧ (rs 16).val ≤ p.extra+1 ∧
      ∃ fs s, Selected p (boundsRegs p rs) m fs s ∧
        s 0 < s 5 ∧ m (s 24).val = s 5 ∧
        es = prepareTrace p fs s m ∧ out = publishRegs s ∧ m' = scratchMemory s m := by
  let u := boundsRegs p rs
  have hu0 : u 0 = 0 := h0
  have hu1 : u 1 = 1 := h1
  have hu5 : (u 5).val = p.extra+1 := Nat.mod_eq_of_lt (by omega)
  have hu16 : u 16 = rs 16 := rfl
  constructor
  · intro h
    cases h with
    | seq hg h =>
      obtain ⟨hpos,rfl,rfl,hm⟩ := (guard_iff pub st 0 16 rs m _ _ _).mp hg
      subst_vars
      cases h with
      | seq ht h =>
        obtain ⟨rfl,rfl,hm⟩ := (target_exec_iff pub st _ _ h1 (p.extra+1) _ _ _).mp ht
        subst_vars
        cases h with
        | ifLtYes _ hr =>
          obtain ⟨h,-⟩ := (guard_iff pub st 0 0 _ _ _ _ _).mp hr
          exact (lt_irrefl _ h).elim
        | ifLtNo hle h =>
          cases h with
          | seq hs hp =>
            obtain ⟨hsel,hm⟩ := (select_iff p pub st u _ hw hu0 hu1 _ _ _).mp hs
            subst_vars
            obtain ⟨hpt,heq,rfl,rfl,hm'⟩ := (publish_iff pub st _ _ _ _ _).mp hp
            change ¬ (u 5).val < (u 16).val at hle
            rw [hu5, hu16] at hle
            exact ⟨by simpa [h0] using hpos, le_of_not_gt hle, _, _, hsel,hpt,heq,rfl,rfl,hm'⟩
  · rintro ⟨hpos,hle,fs,s,hsel,hpt,heq,rfl,rfl,rfl⟩
    have hg := (guard_iff pub st 0 16 rs m _ _ _).mpr
      ⟨show rs 0 < rs 16 by rw [h0]; exact hpos, rfl,rfl,rfl⟩
    have ht := target_exec pub st rs m h1 (p.extra+1)
    have hle' : ¬ u 5 < u 16 := by change ¬ (u 5).val < (u 16).val; rw [hu5,hu16]; omega
    have hs := (select_iff p pub st u m hw hu0 hu1 _ _ _).mpr ⟨hsel,rfl⟩
    have hp := (publish_iff pub st s m _ _ _).mpr ⟨hpt,heq,rfl,rfl,rfl⟩
    exact hg.seq (ht.seq (.ifLtNo hle' (hs.seq hp)))


/-- A previously accepting state is carried deterministically after checking its proposed successor. -/
theorem prepare_accept_exec (p : Program) (pub : Fin 4 → Word w) (st : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (hcap : p.extra+2 ≤ 2^w) (h0 : rs 0 = 0) (h1 : rs 1 = 1)
    (hold : rs 16 = 1) (hout : m (rs 24).val = 1) :
    let s := carryRegs (boundsRegs p rs)
    Flow.Exec pub st (prepare p) rs m (prepareTrace p (.tick :: ticks 5) s m)
      (publishRegs s) (scratchMemory s m) := by
  let u := boundsRegs p rs
  let s := carryRegs u
  have hv : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hval : (rs 16).val = 1 := by rw [hold,hv]
  have hs : Selected p u m (.tick :: ticks 5) s := .carry (hold.trans h1.symm)
  have hs0 : s 0 = 0 := h0
  have hs5 : s 5 = 1 := h1
  have hp : s 0 < s 5 := by rw [hs0,hs5]; change 0 < (1 : Word w).val; omega
  exact (prepare_exec_iff p pub st rs m hw hcap h0 h1 _ _ _).mpr
    ⟨by omega,by omega,_,s,hs,hp,hout.trans hs5.symm,rfl,rfl,rfl⟩

/-- An occupied slot of a running source executes with its actual head reads and exact target. -/
theorem prepare_running_exec (p : Program) (pub : Fin 4 → Word w) (st : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (hcap : p.extra+2 ≤ 2^w) (h0 : rs 0 = 0) (h1 : rs 1 = 1)
    (hold : 2 ≤ (rs 16).val) (hstate : (rs 16).val ≤ p.extra+1)
    (hf : firstHead rs m < rs 3) (hs : secondHead rs m < rs 3)
    (bit : Bool) (a : Instruction p.extra) (ha : chosenInstruction (tableRow p rs m) bit = some a)
    (hp : 0 < a.target.val) (hout : (m (rs 24).val).val = a.target.val) :
    let s := selectedRegs (boundsRegs p rs) m a
    let fs := .tick :: (rowTrace rs m ++ dispatchEvents (rowNumber rs m).val (tableRow p rs m) bit a)
    Flow.Exec pub st (prepare p) rs m (prepareTrace p fs s m) (publishRegs s) (scratchMemory s m) := by
  let u := boundsRegs p rs
  let s := selectedRegs u m a
  have hv : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hne : u 16 ≠ u 1 := by
    change rs 16 ≠ rs 1
    intro he; rw [he,h1,hv] at hold; omega
  have hsel := Selected.slot (p := p) (rs := u) (m := m) hne hf hs bit a ha
  have hs0 : s 0 = 0 := h0
  have hs5 : (s 5).val = a.target.val := (instructionRegs_fields _ a hw hcap).1
  have hpt : s 0 < s 5 := by rw [hs0]; change 0 < (s 5).val; omega
  exact (prepare_exec_iff p pub st rs m hw hcap h0 h1 _ _ _).mpr
    ⟨by omega,hstate,_,s,hsel,hpt,Fin.ext (hout.trans hs5.symm),rfl,rfl,rfl⟩

theorem prepareTrace_bits (p : Program) (fs : List (Event w)) (s : Regs w 32) (m : Memory w) :
    choiceBits (prepareTrace p fs s m) = choiceBits fs := by
  simp [prepareTrace, choiceBits, Flow.choiceBits_append, choiceBits_ticks, publishTrace]

theorem prepareTrace_probes (p : Program) (fs : List (Event w)) (s : Regs w 32) (m : Memory w) :
    countProbes (prepareTrace p fs s m) = countProbes fs + 6 := by
  have ht : countProbes (ticks (w := w) (p.extra+2)) = 0 := by
    simpa [countProbes] using countProbes_ticks_append (p.extra+2) ([] : List (Event w))
  simp [prepareTrace, countProbes, PrimedStackRAM.probes_append, ht, publishTrace]

theorem prepareTrace_length (p : Program) (fs : List (Event w)) (s : Regs w 32) (m : Memory w) :
    (prepareTrace p fs s m).length = p.extra + 16 + fs.length := by
  simp [prepareTrace, ticks, publishTrace]; omega

/-- The exact bit stream for a successful running slot, including the genuine bit
distinguishing the two slots even when both instructions are identical. -/
theorem prepare_slot_bits (p : Program) (rs : Regs w 32) (m : Memory w) (bit : Bool)
    (a : Instruction p.extra) (s : Regs w 32) :
    choiceBits (prepareTrace p (.tick :: (rowTrace rs m ++
      dispatchEvents (rowNumber rs m).val (tableRow p rs m) bit a)) s m) =
        dispatchBits (tableRow p rs m) bit := by
  simp [prepareTrace_bits, choiceBits, rowTrace, dispatchEvents_bits]

/-- All successful preparing calls make six probes for a carried accepting state
and eight probes for a running source. Only an occupied two-slot row consumes a bit. -/
theorem prepare_cost (p : Program) (pub : Fin 4 → Word w) (st : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (hcap : p.extra+2 ≤ 2^w) (h0 : rs 0 = 0) (h1 : rs 1 = 1)
    {es out m'} (he : Flow.Exec pub st (prepare p) rs m es out m') :
    countProbes es = (if rs 16 = rs 1 then 6 else 8) ∧
      (choiceBits es).length ≤ 1 ∧ es.length ≤ 20*p.extra + 36 := by
  obtain ⟨-, -, fs,s,hsel,-,-,rfl,-,-⟩ := (prepare_exec_iff p pub st rs m hw hcap h0 h1 _ _ _).mp he
  clear he
  rw [prepareTrace_probes, prepareTrace_bits, prepareTrace_length]
  cases hsel with
  | carry he =>
    change rs 16 = rs 1 at he
    simp [he, ticks, countProbes, choiceBits]
    omega
  | slot hn hf hs bit a ha =>
    let u := boundsRegs p rs
    change rs 16 ≠ rs 1 at hn
    have hp : countProbes (dispatchEvents (w := w) (rowNumber u m).val (tableRow p u m) bit a) = 0 := by
      simpa [countProbes] using dispatchEvents_probes_append (rowNumber u m).val (tableRow p u m) bit a
        ([] : List (Event w))
    have hbits : (dispatchBits (tableRow p u m) bit).length ≤ 1 := by
      cases tableRow p u m <;> simp [dispatchBits]
    have hlen := dispatchEvents_bound (w := w) p (rowNumber u m).val bit a ha
    change (dispatchEvents (w := w) (rowNumber u m).val (tableRow p u m) bit a).length ≤ _ at hlen
    simp only [u] at hp hbits hlen
    simp [hn, rowTrace, countProbes, choiceBits, hp, hbits, dispatchEvents_bits]
    omega

/-- If the first head address fits, its machine word is the ordinary
input base plus the state-word offset and the window radius. -/
theorem firstAddress_val (rs : Regs w 32) (h1 : (rs 1).val = 1)
    (hfit : (rs 23).val + 1 + (rs 11).val < 2^w) :
    (firstAddress rs).val = (rs 23).val + 1 + (rs 11).val := by
  simpa only [firstAddress, Fin.val_add, h1, Nat.mod_add_mod] using Nat.mod_eq_of_lt hfit

/-- When the second address fits, the second head lies exactly one window
length after the first head. -/
theorem secondAddress_val (rs : Regs w 32) (h1 : (rs 1).val = 1)
    (hfit : (rs 23).val + 1 + (rs 11).val + (rs 22).val < 2^w) :
    (secondAddress rs).val = (rs 23).val + 1 + (rs 11).val + (rs 22).val := by
  rw [secondAddress, Fin.val_add, firstAddress_val rs h1 (by omega), Nat.mod_eq_of_lt hfit]

/-- The machine computes the natural row index whenever the source state is
a running state and the final index fits. Intermediate products may wrap. -/
theorem rowNumber_val (rs : Regs w 32) (m : Memory w)
    (h2 : (rs 2).val = 2) (h3 : (rs 3).val = 3) (hstate : 2 ≤ (rs 16).val)
    (hfit : ((rs 16).val - 2) * 9 + (firstHead rs m).val * 3 + (secondHead rs m).val < 2^w) :
    (rowNumber rs m).val =
      ((rs 16).val - 2) * 9 + (firstHead rs m).val * 3 + (secondHead rs m).val := by
  have hle : rs 2 ≤ rs 16 := by change (rs 2).val ≤ (rs 16).val; omega
  simpa only [rowNumber, Fin.val_add, Fin.val_mul, Fin.sub_val_of_le hle, h2, h3,
    Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod, Nat.reduceMul] using Nat.mod_eq_of_lt hfit

/-- Unit increments give the ordinary consecutive scratch address whenever it fits. -/
theorem scratchAddress_val (rs : Regs w 32) (h1 : (rs 1).val = 1) (i : ℕ)
    (hfit : (rs 25).val + i < 2 ^ w) :
    (scratchAddress rs i).val = (rs 25).val + i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi := ih (by omega)
    rw [scratchAddress, Fin.val_add_eq_of_add_lt, hi, h1]
    · omega
    · rw [hi, h1]
      omega

/-- At each allocated scratch offset the caller reads the corresponding instruction register. -/
theorem scratchMemory_at (rs : Regs w 32) (m : Memory w) (h1 : (rs 1).val = 1)
    (hfit : (rs 25).val + 5 ≤ 2 ^ w) (i : Fin 5) :
    scratchMemory rs m ((rs 25).val + i.val) = rs ⟨5 + i.val, by omega⟩ := by
  have hv (j : ℕ) (hj : j < 5) : (scratchAddress rs j).val = (rs 25).val + j :=
    scratchAddress_val rs h1 j (by omega)
  fin_cases i <;>
    simp (config := { decide := true }) [scratchMemory, writeMemory, hv]

/-- Publishing leaves every address outside the five-word scratch interval intact. -/
theorem scratchMemory_outside (rs : Regs w 32) (m : Memory w) (h1 : (rs 1).val = 1)
    (hfit : (rs 25).val + 5 ≤ 2 ^ w) (k : ℕ)
    (hk : k < (rs 25).val ∨ (rs 25).val + 5 ≤ k) :
    scratchMemory rs m k = m k := by
  have hne (j : ℕ) (hj : j < 5) : k ≠ (scratchAddress rs j).val := by
    rw [scratchAddress_val rs h1 j (by omega)]
    omega
  simp (config := { decide := true }) [scratchMemory, writeMemory, hne]

/-- Selecting a transition preserves the four constants, window coordinates, source state,
and the registers above the row-calculation workspace. -/
theorem Selected.frame {p : Program} {rs : Regs w 32} {m : Memory w} {es s}
    (h : Selected p rs m es s) (j : Fin 32)
    (hj : j.val < 4 ∨ (10 < j.val ∧ j.val < 17) ∨ 20 < j.val) : s j = rs j := by
  cases h with
  | carry h =>
    simp only [carryRegs]
    repeat rw [Function.update_of_ne (by intro he; subst j; exact (by decide : ¬ _) hj)]
  | slot h hf hs bit a ha =>
    rw [selectedRegs, instructionRegs_other _ _ _ (by omega)]
    simp only [rowRegs]
    repeat rw [Function.update_of_ne (by intro he; subst j; exact (by decide : ¬ _) hj)]

/-- Publication uses only register 10 as its scratch-address cursor. -/
theorem publishRegs_other (rs : Regs w 32) (j : Fin 32) (hj : j ≠ 10) :
    publishRegs rs j = rs j := Function.update_of_ne hj ..

end LiveEvaluatorRAMPrepare

end VPVNP
end Computability
end OAI
