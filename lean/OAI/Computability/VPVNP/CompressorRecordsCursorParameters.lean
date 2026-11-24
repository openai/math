import OAI.Computability.VPVNP.CompressorRecordsCursorInit
import OAI.Computability.VPVNP.CompressorRecordsCursorCapacity
import OAI.Computability.VPVNP.CompressorRecordFrame
import OAI.Computability.VPVNP.RAMVirtualParametersCode
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete

/-!
# Producing the cursor initializer's parameter frame

The virtual-parameter program leaves the site exponent, bucket capacity and
live address width in registers. A fixed suffix splits the exponent, computes
the RAM arc width, and writes the eight words consumed by the scheduler-row
initializer. It uses the integer identity
`width = D * w * (8 + 10 * (D + 1) * H)` for the two mask systems.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorRAM.ParametersInit

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM CursorBounds Compression
open scoped Fin.CommRing

variable {w : ℕ}

private def emit (r : Fin 12) : List (Op 12 8) := [.write 8 r, .binary .add 8 8 0]

/-- Slots are the input length, live address bits, degree exponent, lane
bits, scheduler row address, worker tag, array start and destination frame. -/
def finish : Flow 12 8 :=
  straight (.constant 0 1)
    ([.constant 1 2, .binary .add 2 1 1, .binary .add 3 2 2, .binary .add 4 3 1,
      .binary .add 5 5 4, .binary .mul 5 5 5, .binary .mul 5 5 5,
      .binary .add 6 10 0, .binary .mul 6 6 4, .binary .mul 6 6 7,
      .binary .add 6 6 3, .binary .mul 6 6 10, .binary .mul 6 6 5,
      .publicWord 2 2, .binary .shiftLeft 2 0 2, .publicWord 5 3,
      .binary .sub 4 10 5, .binary .shiftLeft 4 0 4, .binary .shiftLeft 5 0 5,
      .publicWord 8 7, .publicWord 1 4, .publicWord 3 5, .publicWord 7 6,
      .stateWord 9, .binary .add 9 9 0] ++ [1,3,2,10,4,5,6,7].flatMap emit)

/-- Run the virtual-parameter calculation, then split the site exponent and write the cursor
scheduler's eight parameter words. -/
def program : Flow 12 8 := .seq (VirtualParameters.program 0 1) finish

private def bank (pub : Fin 8 → Word w) (rs : Regs w 12) : Fin 8 → Word w :=
  let four := (2 : Word w) + 2
  let eight := four + four
  let ten := eight + 2
  let x := rs 5 + ten
  let z := x * x
  let width := ((rs 10 + 1) * ten * rs 7 + eight) * rs 10 * (z*z)
  let pow2 := @BinaryOp.eval w .shiftLeft 1
  ![pub 4, pub 5, pow2 (pub 2), rs 10, pow2 (rs 10 - pub 3), pow2 (pub 3), width, pub 6]

private def writeLog (base : Word w) : List (Word w) → List (Event w)
  | [] => []
  | x :: xs => .write base x :: .tick :: writeLog (base+1) xs

/-- The local calculation ticks followed by the eight parameter-frame writes at the supplied
base address. -/
def events (n : ℕ) (base : Word w) (fields : Fin 8 → Word w) : List (Event w) :=
  List.replicate (VirtualParameters.ticks n + 26) .tick ++ writeLog base (List.ofFn fields)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 900000 in
private theorem finish_run (pub : Fin 8 → Word w) (s : Word w) (m : Memory w) (rs : Regs w 12) :
    let vs := List.ofFn (bank pub rs)
    ∃ out, Flow.Exec pub s finish rs m (List.replicate 26 .tick ++ writeLog (pub 7) vs)
        out (Greedy.writeRow m (pub 7) vs) ∧ out 9 = s+1 := by
  dsimp only
  have h : ∃ out, Flow.once pub s false finish rs m = some
      (List.replicate 26 .tick ++ writeLog (pub 7) (List.ofFn (bank pub rs)), out,
       Greedy.writeRow m (pub 7) (List.ofFn (bank pub rs))) ∧ out 9 = s+1 := by
    simp (config := {decide := true}) [finish, straight, emit, Flow.once, Op.effect,
      Function.update, BinaryOp.eval, bank, writeLog, Greedy.writeRow, List.replicate_succ]
  obtain ⟨out, he, hr⟩ := h
  exact ⟨out, (Flow.once_sound pub s false finish rs m he).1, hr⟩

private theorem eq_word {x : Word w} {v : ℕ} (h : x.val = v) : x = (v : Word w) := by
  subst v
  exact Fin.ext (Nat.mod_eq_of_lt x.isLt).symm

private theorem power (u : Word w) (h : u.val < w) :
    BinaryOp.shiftLeft.eval (1 : Word w) u = (2^u.val : ℕ) := by
  have small : (1 : ℕ) < 2^w := by have := Nat.lt_two_pow_self (n := w); omega
  have one : (1 : Word w).val = 1 := Nat.mod_eq_of_lt small
  simp only [BinaryOp.eval, ite_eq_left h, one, Nat.shiftLeft_eq, one_mul, Fin.ofNat_eq_cast]

/-- The triangular layer count cancels the factor two in each pair of sort blocks. -/
theorem arc_width (D H w : ℕ) :
    (∑ s : CursorRouting.RAMSystem D, CursorRouting.ramFieldBits H w s) =
      ((D+1)*10*H+8)*D*w := by
  have ht : RAMLayout.layerCount D * 2 = (D+1)*D := by
    rw [RAMLayout.layerCount, Nat.choose_two_right, Nat.div_two_mul_two_of_even
      (Nat.even_mul_pred_self (D+1)), Nat.add_sub_cancel]
  rw [CursorRouting.ramArcWidth, RAMLayout.blockBits]
  calc
    _ = D*(8*w) + RAMLayout.layerCount D * 2 * (10*H*w) := by ring
    _ = _ := by rw [ht]; ring

private theorem bank_exact {pub : Fin 8 → Word w} {rs : Regs w 12} {B n a l : ℕ}
    (r : VirtualParameters.Result n (addressBits B n) rs)
    (ha : (pub 2).val = a) (hl : (pub 3).val = l)
    (hA : a < w) (hL : l ≤ virtualBits B n) :
    bank pub rs = ScheduleInit.inputs (pub 4) (pub 5) (virtualBits B n-l) l a
      (initialWidth B n) (pub 6).val := by
  let D := virtualBits B n
  have hd : (rs 10).val = D := r.siteBits
  have hp : (rs 11).val = 2^D := r.sites
  have hD : D < w := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hp ▸ (rs 11).isLt)
  have hsub : (rs 10 - pub 3).val = D-l := by
    rw [Fin.sub_val_of_le (by change (pub 3).val ≤ (rs 10).val; rwa [hl, hd]), hd, hl]
  have hh : (rs 7).val = virtualBucket n := by
    simpa [virtualBucket, roundedUp_eq] using r.bucket
  have hsite : D-l+l = D := Nat.sub_add_cancel hL
  have hwidth : initialWidth B n = ((D+1)*10*virtualBucket n+8)*D*wordBits B n := arc_width D _ _
  funext i
  fin_cases i
  all_goals first | rfl | skip
  · change BinaryOp.shiftLeft.eval 1 (pub 2) = _
    rw [power _ (by omega), ha]; rfl
  · change rs 10 = encode w (D-l+l)
    rw [hsite]; exact eq_word hd
  · change BinaryOp.shiftLeft.eval 1 (rs 10-pub 3) = _
    rw [power _ (by omega), hsub]; rfl
  · change BinaryOp.shiftLeft.eval 1 (pub 3) = _
    rw [power _ (by omega), hl]; rfl
  · let eight : Word w := (2+2)+(2+2)
    let ten := eight+2
    change ((rs 10+1)*ten*rs 7+eight)*rs 10*((rs 5+ten)*(rs 5+ten)*((rs 5+ten)*(rs 5+ten))) =
      encode w (initialWidth B n)
    simp [hwidth, eq_word hd, eq_word r.addressBits, eq_word hh, encode, CursorBounds.wordBits, eight, ten]
    ring
  · exact eq_word rfl

private theorem ticks_props (t : ℕ) (es : List (Event w)) :
    countProbes (List.replicate t .tick ++ es) = countProbes es ∧
      choiceBits (List.replicate t .tick ++ es) = choiceBits es := by
  induction t with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih => simpa only [List.replicate_succ, List.cons_append, countProbes, choiceBits] using ih

theorem work (n : ℕ) (base : Word w) (fields : Fin 8 → Word w) :
    (events n base fields).length = VirtualParameters.ticks n + 42 ∧
      countProbes (events n base fields) = 8 ∧ choiceBits (events n base fields) = [] := by
  unfold events
  rw [List.length_append, List.length_replicate]
  exact ⟨by change _ + 16 = _; omega, (ticks_props ..).1, (ticks_props ..).2⟩

/-- At normal call entry the virtual program and the parameter suffix compute
the eight scheduler inputs using one deterministic burst. -/
theorem native {pub : Fin 8 → Word w} (state : Word w) (m : Memory w) {B n a l : ℕ}
    (hB : 1 ≤ B) (hn : 2 ≤ n) (hw : w = wordBits B n)
    (hpN : (pub 0).val = n) (hpR : (pub 1).val = addressBits B n)
    (hpA : (pub 2).val = a) (hpL : (pub 3).val = l) (ha : a < w) (hl : l ≤ virtualBits B n) :
    let fields := ScheduleInit.inputs (pub 4) (pub 5) (virtualBits B n-l) l a (initialWidth B n) (pub 6).val
    let es := events n (pub 7) fields
    let M := (program.template (some 9)).instantiate w pub
    execute M.program (VirtualParameters.ticks n+43) (M.program.start state) m [] =
      some ⟨es,some (state+1)⟩ := by
  intro fields es M
  obtain ⟨mid,run,hmid⟩ := VirtualParameters.programRun pub 0 1 state m (fun _ ↦ 0) B n hB hn hw hpN hpR
  have he : bank pub mid = fields := bank_exact hmid hpA hpL ha hl
  obtain ⟨out, finishRun, hret⟩ := finish_run pub state m mid
  rw [he] at finishRun
  have hwork := work n (pub 7) fields
  apply (Flow.template_execute_iff program (some 9) pub state (fun _ ↦ 0) (fun _ ↦ 0) m _ _ _).mpr
  refine ⟨out, Greedy.writeRow m (pub 7) (List.ofFn fields), ?_, by simp [hret], by change es.length < _; dsimp [es]; omega, hwork.2.2⟩
  simpa only [program, es, events, List.replicate_add, List.append_assoc] using run.seq finishRun

private theorem after_writeLog (m : Memory w) (base : Word w) (xs : List (Word w)) :
    after m (writeLog base xs) = Greedy.writeRow m base xs := by
  induction xs generalizing m base with
  | nil => rfl
  | cons x xs ih => exact ih (writeMemory m base x) (base+1)

private theorem after_events (m : Memory w) (n : ℕ) (base : Word w) (fields : Fin 8 → Word w) :
    after m (events n base fields) = Greedy.writeRow m base (List.ofFn fields) := by
  have ticks (t : ℕ) (es : List (Event w)) : after m (List.replicate t .tick ++ es) = after m es := by
    induction t with
    | zero => rfl
    | succ t ih => simpa only [List.replicate_succ, List.cons_append, after, List.foldl_cons, update] using ih
  rw [events, ticks, after_writeLog]

private theorem read_stored (m : Memory w) (xs : List (Word w)) (base : Word w)
    (h : Greedy.Stores m base xs) (i : ℕ) (hi : i < xs.length) :
    m (base + (i : Word w)).val = xs[i] := by
  induction xs generalizing base i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have ht := ih (base+1) h.2 i (by simpa using hi)
      rw [Nat.cast_succ, ← add_assoc, add_right_comm base (i : Word w) 1]
      exact ht

/-- Readback through the real frame loader. Every address outside these eight
cells retains its original word. -/
theorem frame_ready (m : Memory w) (n : ℕ) (base : Word w) (fields : Fin 8 → Word w)
    (fit : base.val+8 ≤ 2^w) :
    let m' := after m (events n base fields)
    Frame.data base m' = fields ∧ ∀ addr, addr < base.val ∨ base.val+8 ≤ addr → m' addr = m addr := by
  dsimp only
  rw [after_events]
  have hfit : base.val+(List.ofFn fields).length ≤ 2^w := by simpa using fit
  refine ⟨?_, fun addr h ↦ Greedy.writeRow_outside _ _ _ addr hfit (by simpa using h)⟩
  funext j
  have hs := Greedy.writeRow_stores m base (List.ofFn fields) hfit
  have hj : j.val < (List.ofFn fields).length := by simpa only [List.length_ofFn] using j.isLt
  exact (read_stored _ _ _ hs j.val hj).trans (List.getElem_ofFn hj)

/-- The next burst loads the generated frame, runs the existing row initializer
and returns the incremented state. Its memory has the exact loop bound and
all eleven cursor-worker parameters, and the framed call costs 22 probes. -/
theorem initialize_from_frame (m : Memory w) (n : ℕ) (base row tag state : Word w) (b l a W start : ℕ)
    (frameFit : base.val+8 ≤ 2^w) (rowFit : row.val+14 ≤ 2^w) :
    let fields := ScheduleInit.inputs row tag b l a W start
    let m' := after m (events n base fields)
    let T := template ScheduleInit.ops 16
    let M := Frame.machine T base
    let r := LiveStageLink.prependLog (Frame.loadEvents base m' 0 8)
      (⟨ScheduleInit.events fields,some (state+1)⟩ : Report w)
    let final := after m' r.events
    execute M.program (1+ScheduleInit.ops.length+4*8) (M.program.start state) m' [] = some r ∧
      final row.val = tag ∧ final (row.val+1) = 0 ∧ final (row.val+2) = encode w (rowCount b l a) ∧
      (∀ j : Fin 11, final (row.val+3+j.val) = publicWords w b l a W start j) ∧
      (∀ addr, (addr < base.val ∨ base.val+8 ≤ addr) → (addr < row.val ∨ row.val+14 ≤ addr) →
        final addr = m addr) ∧ r.events.length = 80 ∧ countProbes r.events = 22 := by
  intro fields m' T M r final
  obtain ⟨hfields, hpres⟩ := frame_ready m n base fields frameFit
  change Frame.data base m' = fields at hfields
  let s : Report w := ⟨ScheduleInit.events fields,some (state+1)⟩
  obtain ⟨hcall, htag, hzero, hbound, hparams, hout, hlen, hprobes, _⟩ :=
    ScheduleInit.initialize_row row tag state b l a W start m' rowFit
  have hc := Frame.frame_cost base m' 0 8 s
  have hfinal : final = after m' (ScheduleInit.events fields) := hc.2.2.2.1
  refine ⟨?_, hfinal ▸ htag, hfinal ▸ hzero, hfinal ▸ hbound, hfinal ▸ hparams, ?_, ?_, ?_⟩
  · change execute (Frame.machine T base).program _ _ _ _ = _
    rw [Frame.execute_frame, hfields, hcall]
    rfl
  · intro addr hbase hrow
    rw [hfinal, hout addr hrow]
    exact hpres addr hbase
  · have hh : s.events.length = 48 := hlen
    exact hc.1.trans (by rw [hh])
  · change r.probes = _
    have hh : s.probes = 14 := hprobes
    exact hc.2.1.trans (by rw [hh])

/-- Two successive native bursts, with their actual external memory transfer
and the fields of the installed cursor scheduler row. -/
def PrefixCorrect (pub : Fin 8 → Word w) (state : Word w) (m : Memory w) (B n a l : ℕ) : Prop :=
  let b := virtualBits B n-l
  let W := initialWidth B n
  let row := pub 4
  let fields := ScheduleInit.inputs row (pub 5) b l a W (pub 6).val
  let es := events n (pub 7) fields
  let m' := after m es
  let M := (program.template (some 9)).instantiate w pub
  let S := Frame.machine (template ScheduleInit.ops 16) (pub 7)
  let r := LiveStageLink.prependLog (Frame.loadEvents (pub 7) m' 0 8)
    (⟨ScheduleInit.events fields,some (state+1+1)⟩ : Report w)
  let out := after m' r.events
  execute M.program (VirtualParameters.ticks n+43) (M.program.start state) m [] = some ⟨es,some (state+1)⟩ ∧
  execute S.program (1+ScheduleInit.ops.length+4*8) (S.program.start (state+1)) m' [] = some r ∧
  out row.val = pub 5 ∧ out (row.val+1) = 0 ∧ out (row.val+2) = encode w (rowCount b l a) ∧
  (∀ j : Fin 11, out (row.val+3+j.val) = publicWords w b l a W (pub 6).val j) ∧
  (∀ addr, (addr < (pub 7).val ∨ (pub 7).val+8 ≤ addr) → (addr < row.val ∨ row.val+14 ≤ addr) →
    out addr = m addr) ∧ countProbes es + countProbes r.events = 30 ∧
  es.length + r.events.length ≤ 12*Nat.clog 2 n+141

/-- The parameter prefix starts from the live length and address-width words.
Its two bursts make thirty external probes and use logarithmically many steps. -/
theorem scheduler_prefix {pub : Fin 8 → Word w} (state : Word w) (m : Memory w) {B n a l : ℕ}
    (hB : 1 ≤ B) (hn : 2 ≤ n) (hw : w = wordBits B n)
    (hpN : (pub 0).val = n) (hpR : (pub 1).val = addressBits B n)
    (hpA : (pub 2).val = a) (hpL : (pub 3).val = l) (ha : a < w) (hl : l ≤ virtualBits B n)
    (frameFit : (pub 7).val+8 ≤ 2^w) (rowFit : (pub 4).val+14 ≤ 2^w) :
    PrefixCorrect pub state m B n a l := by
  let b := virtualBits B n-l
  let W := initialWidth B n
  let fields := ScheduleInit.inputs (pub 4) (pub 5) b l a W (pub 6).val
  obtain ⟨hc, ht, hz, hb, hparams, hkeep, hlen, hprobes⟩ :=
    initialize_from_frame m n (pub 7) (pub 4) (pub 5) (state+1) b l a W (pub 6).val frameFit rowFit
  refine ⟨native state m hB hn hw hpN hpR hpA hpL ha hl, hc, ht, hz, hb, hparams, hkeep, ?_, ?_⟩
  · rw [(work n (pub 7) fields).2.1, hprobes]
  · rw [(work n (pub 7) fields).1, hlen]
    have := VirtualParameters.ticks_le n
    omega

end CompressorRecords.CursorRAM.ParametersInit

end VPVNP
end Computability
end OAI
