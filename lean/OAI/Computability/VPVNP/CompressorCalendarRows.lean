import OAI.Computability.VPVNP.CompressorRecordsCursorCapacity
import OAI.Computability.VPVNP.RAMParameters

/-!
# Computing the online descriptor calendar's row count

A fixed burst-RAM program raises the input length to the numerator of the
compression rate and repeatedly divides by the radix determined by its
denominator. It writes the resulting affine row count at workspace offset
eight. Only this final instruction accesses external memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CalendarRows

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Parameters for the calendar's row count as an initial count plus a fixed number of rows per
complete block. -/
structure Spec where
  /-- Numerator of the ratio controlling the logarithmic number of complete compressor blocks. -/
  p : ℕ
  /-- Denominator of the block-count ratio, used as the exponent in the repeated division by a
  power of two. -/
  q : ℕ
  /-- Number of directory rows occupied before the first repeated compressor block. -/
  initialRows : ℕ
  /-- Number of directory rows contributed by one complete compressor block. -/
  phaseRows : ℕ

/-- Total chronological row count for an input length, including startup and all complete
repeated blocks. -/
def rows (D : Spec) (n : ℕ) := D.initialRows + D.phaseRows * roundedDown D.p D.q n

theorem rows_eq (D : Spec) (n : ℕ) :
    rows D n = D.initialRows + D.phaseRows * Compression.blockCount ((D.p : ℝ) / D.q) n := by
  rw [rows, roundedDown_eq]

/-- Private instructions through address calculation, including all loop tests. -/
def ticks (D : Spec) (n : ℕ) := 14 + 3 * D.p + 3 * roundedDown D.p D.q n

private def bound (D : Spec) := D.p + 2^D.q + D.initialRows + D.phaseRows + 9
private def lit (D : Spec) (a : ℕ) : Word (Nat.clog 2 (bound D)) := Fin.ofNat _ a

private theorem lit_val (D : Spec) (a : ℕ) (ha : a < bound D) : (lit D a).val = a :=
  Nat.mod_eq_of_lt (ha.trans_le (Nat.le_pow_clog (by decide) _))

/-- Registers zero and seven retain one and zero. Register two counts down the
multiplications. Register three holds the power and then the running quotient.
Register four counts divisions and subsequently holds the affine row count. -/
def table (D : Spec) : Template 20 8 11 where
  literalWidth := Nat.clog 2 (bound D)
  entry := 0
  code
    | 0 => .constant 0 (lit D 1) 1
    | 1 => .publicWord 1 6 2
    | 2 => .constant 2 (lit D D.p) 3
    | 3 => .copy 3 0 4
    | 4 => .jumpEq 2 7 7 5
    | 5 => .binary .mul 3 3 1 6
    | 6 => .binary .sub 2 2 0 4
    | 7 => .constant 1 (lit D (2^D.q)) 8
    | 8 => .jumpLt 3 1 11 9
    | 9 => .binary .div 3 3 1 10
    | 10 => .binary .add 4 4 0 8
    | 11 => .constant 1 (lit D D.phaseRows) 12
    | 12 => .binary .mul 4 4 1 13
    | 13 => .constant 1 (lit D D.initialRows) 14
    | 14 => .binary .add 4 4 1 15
    | 15 => .publicWord 2 2 16
    | 16 => .constant 1 (lit D 8) 17
    | 17 => .binary .add 2 2 1 18
    | 18 => .writeExternal 2 4 19
    | _ => .accept

private abbrev machine (D : Spec) (pub : Fin 11 → Word w) := (table D).instantiate w pub

private def transcript (t : ℕ) (addr value : Word w) : Report w :=
  ⟨List.replicate t .tick ++ [.write addr value], none⟩

/-- The native report that computes the row count and writes it at offset eight of the
workspace. -/
def report (D : Spec) (pub : Fin 11 → Word w) (n : ℕ) : Report w :=
  transcript (ticks D n) (pub 2 + 8) (rows D n)

private def answer (bs : List Bool) (t : ℕ) (addr value : Word w) :=
  if bs = [] then some (transcript t addr value) else none

private theorem more (bs : List Bool) (t : ℕ) (addr value : Word w) :
    (answer bs t addr value).map (Report.prepend .tick) = answer bs (t+1) addr value := by
  by_cases h : bs = [] <;> simp [answer, h, transcript, List.replicate_succ, Report.prepend]

set_option maxRecDepth 4096 in
private theorem finish (D : Spec) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (f : ℕ) (rs : Fin 8 → Word w) :
    execute (machine D pub).program (f+9) ⟨11,s,rs,fun _ ↦ 0⟩ m bs =
      answer bs 7 (pub 2+8) ((D.initialRows : Word w) + (D.phaseRows : Word w) * rs 4) := by
  have h₁ := lit_val D D.phaseRows (by unfold bound; have := Nat.zero_le (2^D.q); omega)
  have h₂ := lit_val D D.initialRows (by unfold bound; have := Nat.zero_le (2^D.q); omega)
  have h₃ := lit_val D 8 (by unfold bound; have := Nat.zero_le (2^D.q); omega)
  by_cases h : bs = [] <;>
    simp (config := {decide := true}) [execute, Machine.program, machine, Template.instantiate, table,
      Instr.resize, Instr.run, Config.put, BinaryOp.eval, h₁, h₂, h₃, h, answer, transcript,
      List.replicate_succ, Report.prepend, add_comm, mul_comm]

private theorem log_run (D : Spec) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (f x : ℕ) (rs : Fin 8 → Word w)
    (hx : (rs 3).val = x) (hr : (rs 1).val = 2^D.q) (ho : rs 0 = 1) (hbase : 1 < 2^D.q) :
    execute (machine D pub).program (f+10+3*Nat.log (2^D.q) x) ⟨8,s,rs,fun _ ↦ 0⟩ m bs =
      answer bs (8+3*Nat.log (2^D.q) x) (pub 2+8)
        ((D.initialRows : Word w) + (D.phaseRows : Word w) * (rs 4 + (Nat.log (2^D.q) x : Word w))) := by
  induction x using Nat.strong_induction_on generalizing rs with
  | h x ih =>
    by_cases small : x < 2^D.q
    · have test : rs 3 < rs 1 := by change (rs 3).val < (rs 1).val; omega
      simp only [Nat.log_of_lt small, Nat.mul_zero, Nat.cast_zero, add_zero]
      change (execute (machine D pub).program (f+9)
        ⟨if rs 3 < rs 1 then 11 else 9,s,rs,fun _ ↦ 0⟩ m bs).map (Report.prepend .tick) = _
      rw [ite_eq_left test, finish D pub s m bs f rs, more]
    · let b := 2^D.q
      have log_step : Nat.log b x = Nat.log b (x/b) + 1 :=
        Nat.log_of_one_lt_of_le hbase (by omega)
      have test : ¬ rs 3 < rs 1 := by change ¬ (rs 3).val < (rs 1).val; omega
      let next := Function.update (Function.update rs (3 : Fin 8) (BinaryOp.div.eval (rs 3) (rs 1)))
        (4 : Fin 8) (rs 4+rs 0)
      have half : (next 3).val = x/b := by
        change _ = x/(2^D.q)
        have fit := (Nat.div_le_self (rs 3).val (rs 1).val).trans_lt (rs 3).isLt
        simp (config := {decide := true}) [next, BinaryOp.eval, hx, hr,
          Nat.mod_eq_of_lt (show x / 2^D.q < 2^w from hx ▸ hr ▸ fit)]
      have recur := ih (x/b) (Nat.div_lt_self (by omega) hbase) next half
        (by simpa (config := {decide := true}) [next] using hr)
        (by simpa (config := {decide := true}) [next] using ho)
      rw [show f+10+3*Nat.log (2^D.q) x = (f+10+3*Nat.log b (x/b))+3 by
        change f+10+3*Nat.log b x = _; omega]
      change (Option.map (Report.prepend .tick) (execute (machine D pub).program _
        ⟨if rs 3 < rs 1 then 11 else 9,s,rs,fun _ ↦ 0⟩ m bs)) = _
      rw [ite_eq_right test]
      change (((execute (machine D pub).program _ ⟨8,s,next,fun _ ↦ 0⟩ m bs).map
        (Report.prepend .tick)).map (Report.prepend .tick)).map (Report.prepend .tick) = _
      rw [recur, more, more, more]
      change answer bs _ _ _ = answer bs (8+3*Nat.log b x) _ _
      rw [log_step, Nat.cast_add, Nat.cast_one]
      congr 1
      simp only [next, Function.update_self, ho, b]
      ring

private theorem power_run (D : Spec) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (f x k : ℕ) (rs : Fin 8 → Word w)
    (hk : (rs 2).val = k) (hv : rs 3 * rs 1 ^ k = (x : Word w))
    (ho : rs 0 = 1) (hz : rs 7 = 0) (hc : rs 4 = 0)
    (hx : x < 2^w) (hr : 2^D.q < 2^w) (hb : 1 < 2^D.q) :
    execute (machine D pub).program (f+12+3*Nat.log (2^D.q) x+3*k) ⟨4,s,rs,fun _ ↦ 0⟩ m bs =
      answer bs (10+3*Nat.log (2^D.q) x+3*k) (pub 2+8)
        ((D.initialRows : Word w) + (D.phaseRows : Word w) * (Nat.log (2^D.q) x : Word w)) := by
  induction k generalizing rs with
  | zero =>
    have z : rs 2 = rs 7 := by rw [hz]; exact Fin.ext (by simpa using hk)
    have v : (rs 3).val = x := by
      simpa only [pow_zero, mul_one, Fin.val_natCast, Nat.mod_eq_of_lt hx] using congrArg Fin.val hv
    have literal := lit_val D (2^D.q) (by unfold bound; have := Nat.zero_le (2^D.q); omega)
    let next := Function.update rs (1 : Fin 8) ((2^D.q : ℕ) : Word w)
    have run := log_run D pub s m bs f x next (by simpa (config := {decide := true}) [next] using v)
      (by
        change (Function.update rs (1 : Fin 8) ((2^D.q : ℕ) : Word w) 1).val = _
        rw [Function.update_self, Fin.val_natCast, Nat.mod_eq_of_lt hr]) (by simpa (config := {decide := true}) [next] using ho) hb
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [show f+12+3*Nat.log (2^D.q) x = (f+10+3*Nat.log (2^D.q) x)+2 by omega]
    change (execute (machine D pub).program _ ⟨if rs 2 = rs 7 then 7 else 5,s,rs,fun _ ↦ 0⟩ m bs).map
      (Report.prepend .tick) = _
    rw [ite_eq_left z]
    change ((execute (machine D pub).program _ ⟨8,s,Function.update rs 1 (Fin.ofNat _ (lit D (2^D.q)).val),
      fun _ ↦ 0⟩ m bs).map (Report.prepend .tick)).map (Report.prepend .tick) = _
    rw [literal, Fin.ofNat_eq_cast, run, more, more]
    rw [show 8+3*Nat.log (2^D.q) x+1+1 = 10+3*Nat.log (2^D.q) x by omega]
    simp (config := {decide := true}) [next, hc]
  | succ k ih =>
    have nonzero : rs 2 ≠ rs 7 := by
      rw [hz]; intro e; have := congrArg Fin.val e; simp [hk] at this
    let next := Function.update (Function.update rs (3 : Fin 8) (rs 3*rs 1)) (2 : Fin 8) (rs 2-rs 0)
    have one : (1 : Word w).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (hb.trans hr)]
    have count : (next 2).val = k := by
      simp only [next, Function.update_self, ho]
      rw [Fin.sub_val_of_le (by change (1 : Word w).val ≤ (rs 2).val; omega), hk, one]
      omega
    have acc : next 3 * next 1 ^ k = (x : Word w) := by
      simp only [next, Function.update_self, Function.update_of_ne (by decide : (3 : Fin 8) ≠ 2),
        Function.update_of_ne (by decide : (1 : Fin 8) ≠ 2), Function.update_of_ne (by decide : (1 : Fin 8) ≠ 3)]
      rw [mul_assoc, ← pow_succ', hv]
    have recur := ih next count acc (by simpa (config := {decide := true}) [next] using ho)
      (by simpa (config := {decide := true}) [next] using hz)
      (by simpa (config := {decide := true}) [next] using hc)
    rw [show f+12+3*Nat.log (2^D.q) x+3*(k+1) = (f+12+3*Nat.log (2^D.q) x+3*k)+3 by omega]
    change (execute (machine D pub).program _ ⟨if rs 2 = rs 7 then 7 else 5,s,rs,fun _ ↦ 0⟩ m bs).map
      (Report.prepend .tick) = _
    rw [ite_eq_right nonzero]
    change (((execute (machine D pub).program _ ⟨4,s,next,fun _ ↦ 0⟩ m bs).map
      (Report.prepend .tick)).map (Report.prepend .tick)).map (Report.prepend .tick) = _
    rw [recur, more, more, more]
    congr 1

/-- For every sufficient instruction cap the native stage accepts on its
unique empty choice stream and writes the encoded row count. -/
theorem execute_native (D : Spec) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (n : ℕ) (hq : 0 < D.q) (hinput : (pub 6).val = n)
    (hp : D.p < 2^w) (hr : 2^D.q < 2^w) (hx : n^D.p < 2^w)
    {cap : ℕ} (hcap : ticks D n + 2 ≤ cap) :
    let P := ((table D).instantiate w pub).program
    execute P cap (P.start s) m bs = if bs = [] then some (report D pub n) else none := by
  dsimp only
  let x := n^D.p
  let b := 2^D.q
  let f := cap-(ticks D n+2)
  have fuel : cap = (f+12+3*Nat.log b x+3*D.p)+4 := by
    change 14 + 3 * D.p + 3 * Nat.log b x + 2 ≤ cap at hcap
    dsimp [f,ticks,roundedDown,b,x] at *; omega
  let z : Fin 8 → Word w := fun _ ↦ 0
  let start := Function.update (Function.update (Function.update (Function.update z (0 : Fin 8) 1)
    1 (pub 6)) 2 (D.p : Word w)) 3 (1 : Word w)
  have litOne := lit_val D 1 (by unfold bound; have := Nat.zero_le (2^D.q); omega)
  have litP := lit_val D D.p (by unfold bound; have := Nat.zero_le (2^D.q); omega)
  have input : pub 6 = (n : Word w) := Fin.ext (by
    rw [Fin.val_natCast, ← hinput, Nat.mod_eq_of_lt (pub 6).isLt])
  have run := power_run D pub s m bs f x D.p start
    (by simp (config := {decide := true}) [start, Nat.mod_eq_of_lt hp])
    (by simp (config := {decide := true}) [start, x, input, Nat.cast_pow])
    (by simp (config := {decide := true}) [start])
    (by simp (config := {decide := true}) [start,z])
    (by simp (config := {decide := true}) [start,z])
    hx hr (Nat.one_lt_two_pow (by omega))
  rw [fuel]
  change ((((execute (machine D pub).program _ ⟨4,s,Function.update
    (Function.update (Function.update (Function.update z 0 (Fin.ofNat _ (lit D 1).val))
      1 (pub 6)) 2 (Fin.ofNat _ (lit D D.p).val)) 3 (Fin.ofNat _ (lit D 1).val), fun _ ↦ 0⟩
      m bs).map (Report.prepend .tick)).map (Report.prepend .tick)).map
      (Report.prepend .tick)).map (Report.prepend .tick) = _
  rw [litOne,litP,Fin.ofNat_eq_cast,Fin.ofNat_eq_cast, Nat.cast_one, run, more, more, more, more]
  have length : 10+3*Nat.log b x+3*D.p+1+1+1+1 = ticks D n := by
    change 10+3*Nat.log b x+3*D.p+1+1+1+1 = 14+3*D.p+3*Nat.log b x
    omega
  rw [length]
  simp only [answer, report, rows, roundedDown, Nat.cast_add, Nat.cast_mul, x]

private theorem trace_cost (t : ℕ) (a v : Word w) (m : Memory w) :
    after m (transcript t a v).events = writeMemory m a v ∧
      countProbes (transcript t a v).events = 1 ∧ choiceBits (transcript t a v).events = [] := by
  induction t with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ t ih =>
    simpa only [transcript, List.replicate_succ, List.cons_append, after, List.foldl_cons,
      update, countProbes, choiceBits] using ih

theorem after_report (D : Spec) (pub : Fin 11 → Word w) (n : ℕ) (m : Memory w) :
    after m (report D pub n).events = writeMemory m (pub 2 + 8) (rows D n) :=
  (trace_cost ..).1

theorem work (D : Spec) (pub : Fin 11 → Word w) (n : ℕ) :
    (report D pub n).events.length = ticks D n + 1 ∧
      (report D pub n).probes = 1 ∧ choiceBits (report D pub n).events = [] :=
  ⟨by simp [report, transcript], (trace_cost _ _ _ (fun _ ↦ 0)).2⟩

theorem stored_rows (D : Spec) (pub : Fin 11 → Word w) (n : ℕ) (m : Memory w)
    (fit : rows D n < 2^w) :
    (after m (report D pub n).events (pub 2 + 8).val).val =
      D.initialRows + D.phaseRows * Compression.blockCount ((D.p : ℝ) / D.q) n := by
  rw [after_report, ← rows_eq, writeMemory, ite_eq_left rfl, Fin.val_natCast, Nat.mod_eq_of_lt fit]

/-- Each successful division consumes at least one binary digit. -/
theorem ticks_le (D : Spec) (n : ℕ) :
    ticks D n ≤ 14 + 3 * D.p + 3 * (Nat.clog 2 n * D.p) := by
  unfold ticks roundedDown
  rw [Nat.log_pow_left]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply (Nat.div_le_self ..).trans
  have h : n^D.p ≤ 2^(Nat.clog 2 n * D.p) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) n) _
  simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) h

/-- With the paper's live word width, every integer used in a loop guard
and the full natural row count are representable for all sufficiently large lengths. -/
theorem eventually_fits (D : Spec) (B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop,
      D.p < 2^CursorBounds.wordBits B n ∧ 2^D.q < 2^CursorBounds.wordBits B n ∧
      n^D.p < 2^CursorBounds.wordBits B n ∧ rows D n < 2^CursorBounds.wordBits B n := by
  have powers := PolynomiallyBounded.id.pow D.p
  have upper := (PolynomiallyBounded.const D.initialRows).add
    ((PolynomiallyBounded.const D.phaseRows).mul powers)
  filter_upwards [CursorRAM.eventual_word_room B hB (PolynomiallyBounded.const D.p),
    CursorRAM.eventual_word_room B hB (PolynomiallyBounded.const (2^D.q)),
    CursorRAM.eventual_word_room B hB powers, CursorRAM.eventual_word_room B hB upper] with n hp hr hx hu
  refine ⟨hp, hr, hx, lt_of_le_of_lt ?_ hu⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.log_le_self (2^D.q) (n^D.p))) _

end CompressorRecords.CalendarRows

end VPVNP
end Computability
end OAI
