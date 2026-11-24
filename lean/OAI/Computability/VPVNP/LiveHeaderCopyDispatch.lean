import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Native dispatch over the seven auxiliary header segments

Each three-word descriptor contains its cumulative end, source base and destination
base. A call uses the persistent cursor to find the first descriptor whose end
exceeds it, copies one word at the corresponding offset, and advances the cursor.
The entire dispatch table is fixed independently of the input length and word size.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderCopyDispatch

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- One entry in the seven-segment auxiliary copy table, specifying its exclusive end and its
two array bases. -/
structure Descriptor (w : ℕ) where
  /-- The cumulative exclusive cursor bound for this copy segment. -/
  endOffset : Word w
  /-- The source address of the first word in this segment. -/
  sourceBase : Word w
  /-- The destination address of the first word in this segment. -/
  targetBase : Word w

/-- Three consecutive descriptor words, addressed in the RAM word arithmetic. -/
def address (base : Word w) (i : Fin 7) (field : Fin 3) : Word w :=
  base + ((3 * i.val + field.val : ℕ) : Word w)

/-- The external table stores the exclusive end, source, and destination for each of the seven
copy descriptors at its assigned addresses. -/
structure Spec (base : Word w) (records : Fin 7 → Descriptor w) (m : Memory w) : Prop where
  ends : ∀ i, m (address base i 0).val = (records i).endOffset
  sources : ∀ i, m (address base i 1).val = (records i).sourceBase
  targets : ∀ i, m (address base i 2).val = (records i).targetBase

/-- The cumulative end of the preceding descriptor, or zero for the first, used to form a
segment-relative offset. -/
def prevEnd (records : Fin 7 → Descriptor w) (i : Fin 7) : Word w :=
  if h : 0 < i.val then (records ⟨i.val - 1, by omega⟩).endOffset else 0

/-- Native header-copy dispatch code over twelve registers and the public descriptor-table
base. -/
abbrev Code := Flow 12 1

/-- Load the persistent cursor and descriptor pointer, initialize the previous end to zero, and
set the word and descriptor strides. -/
def setup : Code :=
  .seq (.line (.stateWord 0)) <| .seq (.line (.publicWord 1 0)) <| .seq (.line (.constant 2 0)) <|
    .seq (.line (.constant 3 1)) (.line (.constant 4 3))

/-- Copy the word at the cursor's relative position in the selected descriptor and compute the
next cursor. -/
def hit : Code :=
  .seq (.line (.binary .sub 6 0 2)) <| .seq (.line (.binary .add 7 1 3)) <| .seq (.line (.read 8 7)) <|
  .seq (.line (.binary .add 7 7 3)) <| .seq (.line (.read 9 7)) <| .seq (.line (.binary .add 8 8 6)) <|
  .seq (.line (.binary .add 9 9 6)) <| .seq (.line (.read 10 8)) <| .seq (.line (.write 9 10))
    (.line (.binary .add 11 0 3))

/-- Remember the current descriptor's end and advance the pointer by three words to inspect the
next descriptor. -/
def skip : Code := .seq (.line (.copy 2 5)) (.line (.binary .add 1 1 4))

/-- An exhausted table rejects by comparing a register strictly with itself. -/
def scan : ℕ → Code
  | 0 => .line (.guardLt 0 0)
  | n + 1 => .seq (.line (.read 5 1)) (.ifLt 0 5 hit (.seq skip (scan n)))

/-- Initialize the copy dispatcher and search its seven descriptors for the segment containing
the cursor. -/
def flow : Code := .seq setup (scan 7)

/-- Instantiate the seven-segment copy dispatcher at the supplied external table base. -/
def program (base : Word w) := ((flow.template (some 11)).instantiate w (fun _ => base)).program

private theorem addr_one (base : Word w) (i : Fin 7) : address base i 0 + 1 = address base i 1 := by
  simp [address, add_assoc]

private theorem addr_two (base : Word w) (i : Fin 7) : address base i 0 + 1 + 1 = address base i 2 := by
  simp [address, add_assoc]
  ring

private theorem addr_next (base : Word w) (i j : Fin 7) (hj : j.val = i.val + 1) :
    address base i 0 + 3 = address base j 0 := by
  simp [address, hj]; ring

private theorem prev_next (records : Fin 7 → Descriptor w) (i j : Fin 7) (hj : j.val = i.val + 1) :
    prevEnd records j = (records i).endOffset := by
  simp [prevEnd, hj]

private theorem hit_exec (pub : Fin 1 → Word w) (state : Word w) (m : Memory w) (rs : Regs w 12)
    (h0 : rs 0 = state) (h3 : rs 3 = 1) (src dst : Word w)
    (hsrc : m (rs 1 + 1).val = src) (hdst : m (rs 1 + 1 + 1).val = dst) :
    let fromAddr := src + (state - rs 2)
    let toAddr := dst + (state - rs 2)
    ∃ es out, Flow.Exec pub state hit rs m es out (writeMemory m toAddr (m fromAddr.val)) ∧
      out 11 = state+1 ∧ after m es = writeMemory m toAddr (m fromAddr.val) ∧
      es.length = 10 ∧ countProbes es = 4 ∧ choiceBits es = [] := by
  dsimp only
  let fromAddr := src + (state-rs 2)
  let toAddr := dst + (state-rs 2)
  let es : List (Event w) := [.tick, .tick, .read (rs 1+1) src, .tick,
    .read (rs 1+1+1) dst, .tick, .tick, .read fromAddr (m fromAddr.val), .write toAddr (m fromAddr.val), .tick]
  have exec : ∃ out, Flow.once pub state false hit rs m = some (es, out, writeMemory m toAddr (m fromAddr.val)) ∧
      out 11 = state+1 := by
    simp (config := { decide := true }) [hit, Flow.once, Op.effect, Function.update,
      show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
      show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl, h0, h3, hsrc, hdst,
      es, fromAddr, toAddr]
  obtain ⟨out, hx, hout⟩ := exec
  exact ⟨es, out, (Flow.once_sound _ _ _ _ _ _ hx).1, hout, rfl, rfl, rfl, rfl⟩

private theorem scan_exec (base : Word w) (records : Fin 7 → Descriptor w) (state : Word w)
    (m : Memory w) (spec : Spec base records m) (i : Fin 7)
    (hskip : ∀ j, j < i → (records j).endOffset ≤ state) (hhit : state < (records i).endOffset)
    (n : ℕ) (j : Fin 7) (hj : j ≤ i) (hn : i.val < j.val + n) (rs : Regs w 12)
    (h0 : rs 0 = state) (h1 : rs 1 = address base j 0) (h2 : rs 2 = prevEnd records j)
    (h3 : rs 3 = 1) (h4 : rs 4 = 3) :
    let src := (records i).sourceBase + (state - prevEnd records i)
    let dst := (records i).targetBase + (state - prevEnd records i)
    ∃ es out, Flow.Exec (fun _ => base) state (scan n) rs m es out (writeMemory m dst (m src.val)) ∧
      out 11 = state+1 ∧ after m es = writeMemory m dst (m src.val) ∧
      es.length = 4 * (i.val-j.val) + 12 ∧ countProbes es = i.val-j.val+5 ∧ choiceBits es = [] := by
  dsimp only
  induction n generalizing j rs with
  | zero => have := Fin.le_iff_val_le_val.mp hj; omega
  | succ n ih =>
    let r := Function.update rs (5 : Fin 12) (records j).endOffset
    let e := Event.read (address base j 0) (records j).endOffset
    have rd : Flow.Exec (fun _ : Fin 1 => base) state (.line (.read 5 1)) rs m [e] r m := by
      apply Flow.Exec.line
      simp [Op.effect, e, r, h1, spec.ends]
    have r0 : r 0 = state := h0
    have r1 : r 1 = address base j 0 := h1
    have r2 : r 2 = prevEnd records j := h2
    have r3 : r 3 = 1 := h3
    have r4 : r 4 = 3 := h4
    have r5 : r 5 = (records j).endOffset := Function.update_self ..
    by_cases hi : j = i
    · subst j
      obtain ⟨es, out, he, hret, hmem, hlen, hprobe, hbits⟩ := hit_exec (fun _ => base) state m r r0 r3
        (records i).sourceBase (records i).targetBase (by rw [r1, addr_one, spec.sources])
        (by rw [r1, addr_two, spec.targets])
      rw [r2] at he hmem
      refine ⟨e :: .tick :: es, out, rd.seq (.ifLtYes (by rwa [r0, r5]) he), hret, hmem, ?_, ?_, hbits⟩
      · simp [hlen]
      · simp [e, countProbes, hprobe]
    · have hlt := lt_of_le_of_ne hj hi
      let j' : Fin 7 := ⟨j.val+1, Nat.lt_of_le_of_lt hlt i.isLt⟩
      have hj' : j' ≤ i := hlt
      have hn' : i.val < j'.val+n := by change i.val < (j.val+1)+n; omega
      let next := Function.update (Function.update r (2 : Fin 12) (r 5)) (1 : Fin 12) (r 1+r 4)
      have hs : Flow.Exec (fun _ => base) state skip r m [.tick,.tick] next m :=
        (Flow.once_sound _ _ false skip r m rfl).1
      have n1 : next 1 = address base j' 0 := by
        change r 1 + r 4 = _
        rw [r1, r4, addr_next base j j' rfl]
      have n2 : next 2 = prevEnd records j' := by
        change r 5 = _
        rw [r5, prev_next records j j' rfl]
      obtain ⟨es, out, he, hret, hmem, hlen, hprobe, hbits⟩ := ih j' hj' hn' next r0 n1 n2 r3 r4
      refine ⟨e :: .tick :: .tick :: .tick :: es, out,
        rd.seq (.ifLtNo (by rw [r0,r5]; exact not_lt.mpr (hskip j hlt)) (hs.seq he)),
        hret, hmem, ?_, ?_, hbits⟩
      have hv : j.val < i.val := hlt
      · simp only [List.length_cons, hlen, j']; omega
      · simp only [e, countProbes, hprobe, j']; omega

/-- The first descriptor ending strictly above the cursor performs one word copy.
At most eleven probes are needed, including the descriptor reads and the data access. -/
theorem row_native (base : Word w) (records : Fin 7 → Descriptor w) (state : Word w) (m : Memory w)
    (hspec : Spec base records m) (i : Fin 7) (hskip : ∀ j, j < i → (records j).endOffset ≤ state)
    (hhit : state < (records i).endOffset) :
    let src := (records i).sourceBase + (state - prevEnd records i)
    let dst := (records i).targetBase + (state - prevEnd records i)
    ∃ es, execute (program base) 64 ((program base).start state) m [] = some ⟨es, some (state+1)⟩ ∧
      after m es = writeMemory m dst (m src.val) ∧ es.length < 64 ∧ countProbes es ≤ 11 ∧ choiceBits es = [] := by
  dsimp only
  let regs : Regs w 12 := ![state, base, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0]
  have init : Flow.Exec (fun _ => base) state setup (fun _ => 0) m (List.replicate 5 .tick) regs m := by
    apply (Flow.once_sound _ _ false setup _ _ ?_).1
    simp (config := { decide := true }) [setup, Flow.once, Op.effect, regs]
    funext k
    fin_cases k <;> rfl
  obtain ⟨es, out, he, hret, hmem, hlen, hprobe, hbits⟩ :=
    scan_exec base records state m hspec i hskip hhit 7 0 (Fin.zero_le _) (by simp) regs
      rfl (by simp [regs,address]) (by simp [regs,prevEnd]) rfl rfl
  let log := List.replicate 5 (.tick : Event w) ++ es
  have len : log.length < 64 := by simp [log, hlen]; have := i.isLt; omega
  have bits : choiceBits log = [] := hbits
  refine ⟨log, ?_, hmem, len, ?_, bits⟩
  · apply (Flow.template_execute_iff flow (some 11) (fun _ => base) state (fun _ => 0) (fun _ => 0) m _ _ _).2
    exact ⟨out, _, init.seq he, congrArg some hret.symm, len, bits⟩
  · change countProbes es ≤ 11
    simp only [hprobe, Fin.val_zero, Nat.sub_zero]
    have := i.isLt
    omega

private theorem scan_reject {pub : Fin 1 → Word w} {state : Word w} {m m' : Memory w}
    {rs out : Regs w 12} {es : List (Event w)} (n : ℕ) (stride : rs 4 = 3)
    (ends : ∀ j < n, m (rs 1 + ((3 * j : ℕ) : Word w)).val ≤ rs 0) :
    ¬ Flow.Exec pub state (scan n) rs m es out m' := by
  induction n generalizing rs es with
  | zero =>
    intro he
    cases he with
    | line h => simp [Op.effect] at h
  | succ n ih =>
    intro he
    cases he with
    | seq first branch =>
      cases first with
      | line hread =>
        simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at hread
        obtain ⟨rfl, rfl, rfl⟩ := hread
        cases branch with
        | ifLtYes h _ =>
          have h₀ := ends 0 (by omega)
          simp only [Nat.mul_zero, Nat.cast_zero, add_zero] at h₀
          exact (not_lt_of_ge h₀) (by simpa (config := {decide := true}) [Function.update] using h)
        | ifLtNo _ skipped =>
          cases skipped with
          | seq prep rest =>
            cases prep with
            | seq copied moved =>
              cases copied with
              | line hc =>
                simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at hc
                obtain ⟨rfl,rfl,rfl⟩ := hc
                cases moved with
                | line hm =>
                  simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl,rfl,rfl⟩ := hm
                  apply ih _ _ rest
                  · simpa (config := {decide := true}) [Function.update] using stride
                  · intro j hj
                    have h := ends (j+1) (by omega)
                    simpa (config := {decide := true}) [Function.update, BinaryOp.eval, stride,
                      Nat.mul_add, add_assoc, add_left_comm, add_comm] using h

/-- No successful structured execution starts beyond the cumulative ends. -/
theorem flow_reject {base state : Word w} {records : Fin 7 → Descriptor w} {m : Memory w}
    (layout : Spec base records m) (outside : ∀ i, (records i).endOffset ≤ state)
    (rs out : Regs w 12) (es : List (Event w)) (m' : Memory w) :
    ¬ Flow.Exec (fun _ => base) state flow rs m es out m' := by
  intro he
  cases he with
  | seq prep tail =>
    unfold setup at prep
    iterate 4
      cases prep
      rename_i head prep
      cases head
      rename_i h
      simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
    cases prep
    rename_i h
    simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    apply scan_reject 7 (by rfl) _ tail
    intro j hj
    let i : Fin 7 := ⟨j,hj⟩
    change m (address base i 0).val ≤ state
    rw [layout.ends]
    exact outside i

/-- Every state past the last occupied descriptor fails, including with arbitrary
fuel and an arbitrary branch tape. The rejecting comparison also covers an empty sweep. -/
theorem reject_outside (base state : Word w) (records : Fin 7 → Descriptor w) (m : Memory w)
    (layout : Spec base records m) (outside : ∀ i, (records i).endOffset ≤ state)
    (fuel : ℕ) (bits : List Bool) :
    execute (program base) fuel ((program base).start state) m bits = none := by
  cases h : execute (program base) fuel ((program base).start state) m bits with
  | none => rfl
  | some rep =>
    have hh := (Flow.template_execute_iff flow (some 11) (fun _ => base) state
      (fun _ => 0) (fun _ => 0) m fuel bits rep).mp h
    obtain ⟨out,m',he,_⟩ := hh
    exact False.elim (flow_reject layout outside _ _ _ _ he)

/-- For cumulative ends in order, the last end is the exclusive upper bound on the cursor. -/
theorem reject_ge_last (base state : Word w) (records : Fin 7 → Descriptor w) (m : Memory w)
    (layout : Spec base records m) (ordered : Monotone fun i => (records i).endOffset)
    (past : (records (Fin.last 6)).endOffset ≤ state) (fuel : ℕ) (bits : List Bool) :
    execute (program base) fuel ((program base).start state) m bits = none :=
  reject_outside base state records m layout (fun i => (ordered (Fin.le_last i)).trans past) fuel bits

end LiveHeaderCopyDispatch

end VPVNP
end Computability
end OAI
