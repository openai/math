import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.LiveEvaluatorRAM
import OAI.Computability.VPVNP.VerifierMachineSimulation

/-!
# The evaluator's fixed row dispatch in a live group

The evaluator program is fixed, so its finite row table is part of the
control graph. Register 4 contains the zero-based row number. Each skipped
row costs a test and a decrement. Only two-slot rows execute a choice, with
false selecting the first slot and true selecting the second. A zero-slot
row or an out-of-range row jumps to the rejecting exit.

Registers 5–9 receive the five fields of the chosen instruction. The target
state is assembled from zero and unit increments. Each tape symbol and move
is a single two-bit literal. Consequently the instruction text is fixed
independently of the word width and live window size.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAMDispatch

open BurstRAM (Word Memory Event choiceBits)
open BurstRAM.PrivateRAM (BinaryOp)
open PrimedInputRAM (Flow)
open PrimedStackRAM (Op Regs)
open UniversalMachine (Program Instruction Branches Symbol chosenInstruction)

variable {w k extra : ℕ}

/-- The four bounded tape fields fit directly in the RAM's literal format. -/
private def literal (v : Symbol) : Word 2 := ⟨v.val, by have := v.isLt; omega⟩

/-- Load a fixed natural number into register 5 using only zero and unit increments. -/
def targetFlow : ℕ → Flow 32 k
  | 0 => .line (.constant 5 0)
  | n + 1 => .seq (targetFlow n) (.line (.binary .add 5 5 1))

private def record (a : Instruction extra) : Flow 32 k :=
  .seq (targetFlow a.target.val) <|
  .seq (.line (.constant 6 (literal a.firstSymbol))) <|
  .seq (.line (.constant 7 (literal a.firstMove))) <|
  .seq (.line (.constant 8 (literal a.secondSymbol)))
       (.line (.constant 9 (literal a.secondMove)))

private def reject : Flow 32 k := .line (.guardLt 0 0)

private def rowFlow : Branches extra → Flow 32 k
  | .stop => reject
  | .one a => record a
  | .two a b => .branch (record b) (record a)

private def scan : List (Branches extra) → Flow 32 k
  | [] => reject
  | b :: bs => .ifEq 4 0 (rowFlow b) (.seq (.line (.binary .sub 4 4 1)) (scan bs))

/-- The native structured flow compiled from a fixed coefficient machine. -/
def dispatch (p : Program) : Flow 32 k := scan p.rows

/-- Registers after writing the instruction's five fields. -/
def instructionRegs (rs : Regs w 32) (a : Instruction extra) : Regs w 32 :=
  let s := Function.update rs 5 (Fin.ofNat (2^w) a.target.val)
  let s := Function.update s 6 (Fin.ofNat (2^w) a.firstSymbol.val)
  let s := Function.update s 7 (Fin.ofNat (2^w) a.firstMove.val)
  let s := Function.update s 8 (Fin.ofNat (2^w) a.secondSymbol.val)
  Function.update s 9 (Fin.ofNat (2^w) a.secondMove.val)

theorem instructionRegs_fields (rs : Regs w 32) (a : Instruction extra)
    (hw : 2 ≤ w) (ht : extra + 2 ≤ 2 ^ w) :
    ((instructionRegs rs a) 5).val = a.target.val ∧
    ((instructionRegs rs a) 6).val = a.firstSymbol.val ∧
    ((instructionRegs rs a) 7).val = a.firstMove.val ∧
    ((instructionRegs rs a) 8).val = a.secondSymbol.val ∧
    ((instructionRegs rs a) 9).val = a.secondMove.val := by
  have h4 : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  simp (config := {decide := true}) [instructionRegs, Function.update, Fin.ofNat,
    Nat.mod_eq_of_lt (a.target.isLt.trans_le ht),
    Nat.mod_eq_of_lt (a.firstSymbol.isLt.trans_le (by omega : 3 ≤ 2 ^ w)),
    Nat.mod_eq_of_lt (a.firstMove.isLt.trans_le (by omega : 3 ≤ 2 ^ w)),
    Nat.mod_eq_of_lt (a.secondSymbol.isLt.trans_le (by omega : 3 ≤ 2 ^ w)),
    Nat.mod_eq_of_lt (a.secondMove.isLt.trans_le (by omega : 3 ≤ 2 ^ w))]

theorem instructionRegs_other (rs : Regs w 32) (a : Instruction extra) (j : Fin 32)
    (hj : j.val < 5 ∨ 9 < j.val) : instructionRegs rs a j = rs j := by
  simp only [instructionRegs]
  repeat rw [Function.update_of_ne (by intro he; subst j; exact (by decide : ¬ _) hj)]

/-- Nondeterministic input consumed by a successful dispatch. -/
def dispatchBits (b : Branches extra) (bit : Bool) : List Bool :=
  match b with
  | .two .. => [bit]
  | _ => []

/-- The consumed RAM bit list uniquely identifies every occupied slot in a given row.
In particular the two copies of a repeated instruction have different encodings. -/
theorem dispatchBits_injective {b : Branches extra} {x y : Bool} {a c : Instruction extra}
    (hx : chosenInstruction b x = some a) (hy : chosenInstruction b y = some c)
    (he : dispatchBits b x = dispatchBits b y) : x = y := by
  cases b <;> cases x <;> cases y <;> simp_all [chosenInstruction, dispatchBits]

/-- A trace of the specified number of local instruction steps in the fixed evaluator row
dispatch. -/
def ticks (n : ℕ) : List (Event w) := List.replicate n .tick

private def rowEvents (b : Branches extra) (bit : Bool) (a : Instruction extra) : List (Event w) :=
  let es := ticks (a.target.val + 5)
  match b with
  | .two .. => .choice bit :: es
  | _ => es

/-- The exact native trace, including each countdown operation and target increment. -/
def dispatchEvents (i : ℕ) (b : Branches extra) (bit : Bool) (a : Instruction extra) :
    List (Event w) :=
  ticks (2*i+1) ++ rowEvents b bit a

theorem choiceBits_ticks (n : ℕ) : choiceBits (ticks (w := w) n) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ticks, List.replicate_succ, choiceBits] using ih

theorem dispatchEvents_bits (i : ℕ) (b : Branches extra) (bit : Bool) (a : Instruction extra) :
    choiceBits (dispatchEvents (w := w) i b bit a) = dispatchBits b bit := by
  cases b <;> simp [dispatchEvents, Flow.choiceBits_append, rowEvents, dispatchBits,
    choiceBits, choiceBits_ticks]

theorem dispatchEvents_length (i : ℕ) (b : Branches extra) (bit : Bool) (a : Instruction extra) :
    (dispatchEvents (w := w) i b bit a).length =
      2*i + 1 + (dispatchBits b bit).length + a.target.val + 5 := by
  cases b <;> simp [dispatchEvents, dispatchBits, rowEvents, ticks] <;> omega

theorem target_exec (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (h1 : rs 1 = 1) (n : ℕ) :
    Flow.Exec pub state (targetFlow n) rs m (ticks (n+1)) (Function.update rs 5 (Fin.ofNat (2^w) n)) m := by
  induction n with
  | zero => exact .line rfl
  | succ n ih =>
    have hadd : Fin.ofNat (2^w) n + 1 = Fin.ofNat (2^w) (n+1) := by
      apply Fin.ext
      exact (Nat.add_mod ..).symm
    have hl : Flow.Exec pub state (.line (.binary .add 5 5 1)) (Function.update rs 5 (Fin.ofNat (2^w) n)) m
        [.tick] (Function.update rs 5 (Fin.ofNat (2^w) n.succ)) m := by
      apply Flow.Exec.line
      simp (config := {decide := true}) [Op.effect, BinaryOp.eval, Function.update_self,
        Function.update_of_ne, Function.update_idem, h1]
      exact congrArg (Function.update rs 5) hadd
    have he := ih.seq hl
    exact (show ticks (w := w) (n.succ+1) = ticks (n+1) ++ [.tick] from
      List.replicate_add (n+1) 1 (Event.tick (w := w))) ▸ he

private theorem record_exec (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (h1 : rs 1 = 1) (a : Instruction extra) :
    Flow.Exec pub state (record a) rs m (ticks (a.target.val + 5)) (instructionRegs rs a) m := by
  have h : ticks (w := w) (a.target.val + 5) =
      ticks (a.target.val+1) ++ [.tick,.tick,.tick,.tick] :=
    List.replicate_add (a.target.val+1) 4 (Event.tick (w := w))
  rw [h]
  exact (target_exec pub state rs m h1 _).seq
    ((Flow.Exec.line rfl).seq ((Flow.Exec.line rfl).seq ((Flow.Exec.line rfl).seq (.line rfl))))

/-- Determinism of the straight-line portion that writes one selected record. -/
private inductive Straight : Flow 32 k → Prop
  | line (op : Op 32 k) : Straight (.line op)
  | seq {f g : Flow 32 k} (hf : Straight f) (hg : Straight g) : Straight (.seq f g)

private theorem Straight.unique {f : Flow 32 k} (h : Straight f) {pub : Fin k → Word w}
    {state rs m es rs' m' fs rs'' m''}
    (x : Flow.Exec pub state f rs m es rs' m') (y : Flow.Exec pub state f rs m fs rs'' m'') :
    es = fs ∧ rs' = rs'' ∧ m' = m'' := by
  induction h generalizing rs m es rs' m' fs rs'' m'' with
  | line op =>
    cases x with
    | line hx =>
      cases y with
      | line hy =>
        have he := Option.some.inj (hx.symm.trans hy)
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl,rfl,rfl⟩ := he
        exact ⟨rfl,rfl,rfl⟩
  | seq _ _ iha ihb =>
    cases x with
    | seq xa xb =>
      cases y with
      | seq ya yb =>
        obtain ⟨rfl,rfl,rfl⟩ := iha xa ya
        obtain ⟨rfl,rfl,rfl⟩ := ihb xb yb
        exact ⟨rfl,rfl,rfl⟩

private theorem target_straight (n : ℕ) : Straight (targetFlow (k := k) n) := by
  induction n with
  | zero => exact .line _
  | succ n ih => exact ih.seq (.line _)

private theorem record_straight (a : Instruction extra) : Straight (record (k := k) a) :=
  (target_straight _).seq ((Straight.line _).seq ((Straight.line _).seq ((Straight.line _).seq (.line _))))

private theorem no_reject_exec {pub : Fin k → Word w} {state rs m es rs' m'} :
    ¬ Flow.Exec pub state reject rs m es rs' m' := by
  intro h
  cases h with
  | line he => simp [Op.effect] at he

private theorem row_exec_iff (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (h1 : rs 1 = 1) (b : Branches extra) (es rs' m') :
    Flow.Exec pub state (rowFlow b) rs m es rs' m' ↔
      ∃ bit a, chosenInstruction b bit = some a ∧ es = rowEvents b bit a ∧
        rs' = instructionRegs rs a ∧ m' = m := by
  constructor
  · intro h
    cases b with
    | stop => exact (no_reject_exec h).elim
    | one a =>
      exact ⟨false, a, rfl, (record_straight a).unique h (record_exec pub state rs m h1 a)⟩
    | two a b =>
      cases h with
      | branchYes he =>
        obtain ⟨rfl,rfl,rfl⟩ := (record_straight b).unique he (record_exec pub state rs m h1 b)
        exact ⟨true,b,rfl,rfl,rfl,rfl⟩
      | branchNo he =>
        obtain ⟨rfl,rfl,rfl⟩ := (record_straight a).unique he (record_exec pub state rs m h1 a)
        exact ⟨false,a,rfl,rfl,rfl,rfl⟩
  · rintro ⟨bit,a,ha,rfl,rfl,rfl⟩
    cases b with
    | stop => contradiction
    | one x =>
      cases bit
      · cases ha
        exact record_exec pub state rs _ h1 _
      · contradiction
    | two x y =>
      cases bit <;> cases ha
      · exact .branchNo (record_exec pub state rs _ h1 _)
      · exact .branchYes (record_exec pub state rs _ h1 _)


private theorem dispatchEvents_succ (i : ℕ) (b : Branches extra) (bit : Bool) (a : Instruction extra) :
    dispatchEvents (w := w) (i+1) b bit a = .tick :: .tick :: dispatchEvents i b bit a := by
  simp only [dispatchEvents, ticks, show 2*(i+1)+1 = (2*i+1)+1+1 by omega,
    List.replicate_succ, List.cons_append]

private theorem scan_exec_iff (pub : Fin k → Word w) (state : Word w) (hw : 2 ≤ w)
    (bs : List (Branches extra)) (rs : Regs w 32) (m : Memory w) (h0 : rs 0 = 0)
    (h1 : rs 1 = 1) (i : ℕ) (hi : (rs 4).val = i) (es rs' m') :
    Flow.Exec pub state (scan bs) rs m es rs' m' ↔
      ∃ bit a, chosenInstruction (bs[i]?.getD .stop) bit = some a ∧
        es = dispatchEvents i (bs[i]?.getD .stop) bit a ∧
        rs' = instructionRegs (Function.update rs 4 0) a ∧ m' = m := by
  induction bs generalizing rs i es with
  | nil =>
    constructor
    · exact fun h => (no_reject_exec h).elim
    · rintro ⟨bit,a,ha,-⟩
      simp [chosenInstruction] at ha
  | cons b bs ih =>
    cases i with
    | zero =>
      have h4 : rs 4 = 0 := Fin.ext hi
      have heq : rs 4 = rs 0 := h4.trans h0.symm
      have hup : Function.update rs 4 0 = rs := by
        conv_lhs => arg 3; rw [← h4]
        exact Function.update_eq_self _ _
      simp only [List.getElem?_cons_zero, Option.getD_some, hup]
      constructor
      · intro h
        cases h with
        | ifEqYes _ hr =>
          obtain ⟨bit,a,ha,rfl,hr,hm⟩ := (row_exec_iff pub state rs m h1 b _ _ _).mp hr
          exact ⟨bit,a,ha,rfl,hr,hm⟩
        | ifEqNo hn _ => contradiction
      · rintro ⟨bit,a,ha,rfl,hr,hm⟩
        exact .ifEqYes heq ((row_exec_iff pub state rs m h1 b _ _ _).mpr ⟨bit,a,ha,rfl,hr,hm⟩)
    | succ i =>
      have hne : rs 4 ≠ rs 0 := by
        rw [h0]; intro hz; rw [hz] at hi; change 0 = i+1 at hi; omega
      let q := Function.update rs 4 (rs 4 - rs 1)
      have hq0 : q 0 = 0 := by simpa [q, Function.update_of_ne (by decide : (0 : Fin 32) ≠ 4)] using h0
      have hq1 : q 1 = 1 := by simpa [q, Function.update_of_ne (by decide : (1 : Fin 32) ≠ 4)] using h1
      have hv : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
      have hle : (1 : Word w) ≤ rs 4 := by change (1 : Word w).val ≤ (rs 4).val; rw [hv, hi]; omega
      have hq4 : (q 4).val = i := by
        simp only [q, Function.update_self, h1, Fin.sub_val_of_le hle, hv, hi, Nat.succ_sub_one]
      have hline : Flow.Exec pub state (.line (.binary .sub 4 4 1)) rs m [.tick] q m := .line rfl
      have hup : Function.update q 4 0 = Function.update rs 4 0 := Function.update_idem _ _ _
      simp only [List.getElem?_cons_succ, dispatchEvents_succ]
      constructor
      · intro h
        cases h with
        | ifEqYes heq _ => contradiction
        | ifEqNo _ hskip =>
          cases hskip with
          | seq hdec htail =>
            obtain ⟨rfl,rfl,rfl⟩ := (Straight.line _).unique hdec hline
            obtain ⟨bit,a,ha,hes,hr,hm⟩ := (ih _ hq0 hq1 _ hq4 _).mp htail
            exact ⟨bit,a,ha,by simp [hes],hup ▸ hr,hm⟩
      · rintro ⟨bit,a,ha,rfl,hr,hm⟩
        exact .ifEqNo hne (hline.seq ((ih _ hq0 hq1 _ hq4 _).mpr
          ⟨bit,a,ha,rfl,hup.symm ▸ hr,hm⟩))

/-- Successful dispatches are precisely the occupied slots of the indexed
row. This also describes the whole event log and register frame. -/
theorem dispatch_exec_iff (p : Program) (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (h0 : rs 0 = 0) (h1 : rs 1 = 1) (es rs' m') :
    Flow.Exec pub state (dispatch p) rs m es rs' m' ↔
      ∃ bit a, chosenInstruction (p.rows[(rs 4).val]?.getD .stop) bit = some a ∧
        es = dispatchEvents (rs 4).val (p.rows[(rs 4).val]?.getD .stop) bit a ∧
        rs' = instructionRegs (Function.update rs 4 0) a ∧ m' = m :=
  scan_exec_iff pub state hw p.rows rs m h0 h1 _ rfl es rs' m'

/-- Construct the native execution for a selected table slot. -/
theorem dispatch_exec (p : Program) (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (h0 : rs 0 = 0) (h1 : rs 1 = 1)
    (bit : Bool) (a : Instruction p.extra)
    (ha : chosenInstruction (p.rows[(rs 4).val]?.getD .stop) bit = some a) :
    Flow.Exec pub state (dispatch p) rs m
      (dispatchEvents (rs 4).val (p.rows[(rs 4).val]?.getD .stop) bit a)
      (instructionRegs (Function.update rs 4 0) a) m :=
  (dispatch_exec_iff p pub state rs m hw h0 h1 _ _ _).mpr ⟨bit,a,ha,rfl,rfl,rfl⟩

/-- The instruction budget is uniform in the word width, input and live window size. -/
theorem dispatchEvents_bound (p : Program) (i : ℕ) (bit : Bool) (a : Instruction p.extra)
    (ha : chosenInstruction (p.rows[i]?.getD .stop) bit = some a) :
    (dispatchEvents (w := w) i (p.rows[i]?.getD .stop) bit a).length ≤ 19 * p.extra + 6 := by
  have hi : i < p.rows.length := by
    by_contra! hn
    rw [List.getElem?_eq_none hn] at ha
    contradiction
  have hb : (dispatchBits (p.rows[i]?.getD .stop) bit).length ≤ 1 := by
    cases p.rows[i]?.getD .stop <;> simp [dispatchBits]
  rw [dispatchEvents_length]
  rw [p.rows_length] at hi
  have ht := a.target.isLt
  omega

/-- A stop row has no successful native execution for any amount of fuel
or any branch stream. This includes out-of-range row indices. -/
theorem dispatch_rejects (p : Program) (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (hw : 2 ≤ w) (h0 : rs 0 = 0) (h1 : rs 1 = 1)
    (hstop : p.rows[(rs 4).val]?.getD .stop = .stop) (result : Option (Fin 32))
    (priv : Word w → Word w) (fuel : ℕ) (bits : List Bool) :
    let f : Flow 32 k := dispatch p
    BurstRAM.execute ((f.template result).instantiate w pub).program fuel
      ⟨f.pc f.entry,state,rs,priv⟩ m bits = none := by
  dsimp only
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro out hout
  obtain ⟨rs',m',he,-⟩ := (Flow.template_execute_iff _ _ _ _ _ _ _ _ _ _).mp hout
  obtain ⟨bit,a,ha,-⟩ := (dispatch_exec_iff p pub state rs m hw h0 h1 _ rs' m').mp he
  rw [hstop] at ha
  contradiction

theorem target_loopFree (n : ℕ) : LiveEvaluatorRAM.loopFree (targetFlow (k := k) n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [targetFlow, LiveEvaluatorRAM.loopFree, ih]

theorem dispatch_loopFree (p : Program) : LiveEvaluatorRAM.loopFree (dispatch (k := k) p) = true := by
  have hrec (a : Instruction p.extra) : LiveEvaluatorRAM.loopFree (record (k := k) a) = true := by
    simp [record, LiveEvaluatorRAM.loopFree, target_loopFree]
  have hr (b : Branches p.extra) : LiveEvaluatorRAM.loopFree (rowFlow (k := k) b) = true := by
    cases b <;> simp [rowFlow, reject, LiveEvaluatorRAM.loopFree, hrec]
  unfold dispatch
  induction p.rows with
  | nil => rfl
  | cons b bs ih => simp [scan, LiveEvaluatorRAM.loopFree, hr, ih]

theorem countProbes_ticks_append (n : ℕ) (es : List (Event w)) :
    BurstRAM.countProbes (ticks n ++ es) = BurstRAM.countProbes es := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ticks, List.replicate_succ, BurstRAM.countProbes] using ih

theorem dispatchEvents_probes_append (i : ℕ) (b : Branches extra) (bit : Bool) (a : Instruction extra)
    (es : List (Event w)) :
    BurstRAM.countProbes (dispatchEvents i b bit a ++ es) = BurstRAM.countProbes es := by
  cases b <;> simp [dispatchEvents, List.append_assoc, rowEvents, countProbes_ticks_append,
    BurstRAM.countProbes]

/-- The fixed natural loader has no other successful execution. -/
theorem target_exec_iff (pub : Fin k → Word w) (state : Word w) (rs : Regs w 32)
    (m : Memory w) (h1 : rs 1 = 1) (n : ℕ) (es rs' m') :
    Flow.Exec pub state (targetFlow n) rs m es rs' m' ↔
      es = ticks (n+1) ∧ rs' = Function.update rs 5 (Fin.ofNat (2^w) n) ∧ m' = m := by
  constructor
  · exact fun h => (target_straight n).unique h (target_exec pub state rs m h1 n)
  · rintro ⟨rfl,rfl,rfl⟩
    exact target_exec pub state rs _ h1 n

end LiveEvaluatorRAMDispatch

end VPVNP
end Computability
end OAI
