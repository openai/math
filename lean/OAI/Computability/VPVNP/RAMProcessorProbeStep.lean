import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.RAMProcessorGraphProbe
import OAI.Computability.VPVNP.RAMProcessorGraphProbeEmit
import OAI.Computability.VPVNP.RAMProcessorGraphCredit

/-!
# Executing one charged probe inside the physical call

The four transfers from the instruction callback to the next instruction
charge the budgets, stage the address and value, append the record, and
advance its ordinal. The recorded address is always read from the original
register bank, including when a read overwrites its own address register.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

/-- One external read or write with its successor instruction. A read also specifies the
guessed word and the choice suffix left after consuming it. -/
inductive ProbeStep (w p r : ℕ) where
  | read (dst addr : Fin r) (next : Fin p) (v : Word w) (tail : List Bool)
  | write (addr src : Fin r) (next : Fin p)

namespace ProbeStep

/-- Private program counter at which execution resumes after the read or write. -/
def next : ProbeStep w p r → Fin p
  | .read _ _ pc _ _ | .write _ _ pc => pc

/-- Interpreter callback for the probe, retaining its register operands and successor
instruction. -/
def callback : ProbeStep w p r → ISA.Callback p r
  | .read d a pc _ _ => .read d a pc
  | .write a v pc => .write a v pc

/-- Choice-stream condition for staging a probe. A read requires the encoded guessed word
followed by the declared suffix, and every write satisfies the condition. -/
def accepts (a : ProbeStep w p r) (s : Snapshot w p r k) : Prop :=
  match a with
  | .read _ _ _ v tail => s.choices = BurstRAM.wordBits v ++ tail
  | .write .. => True

/-- Five-word record of the probe, with operation tag, original address, read or write value,
call start and current ordinal. -/
def record (a : ProbeStep w p r) (s : Snapshot w p r k) (start ord : Word w) : WordRecord w :=
  match a with
  | .read _ addr _ v _ => ⟨.read,s.cfg.reg addr,v,start,ord⟩
  | .write addr src _ => ⟨.write,s.cfg.reg addr,s.cfg.reg src,start,ord⟩

/-- Stage the probe payload and advance the private program counter. A read also installs the
guessed word in its destination and consumes the corresponding choice bits. -/
def stage (a : ProbeStep w p r) (s : Snapshot w p r k) : Snapshot w p r k :=
  match a with
  | .read d addr pc v tail => s.afterRead d addr pc v tail
  | .write addr src pc => s.afterWrite addr src pc

/-- Complete the probe by charging its cost, staging the payload, emitting the timestamped
record and incrementing the ordinal. -/
def finish (a : ProbeStep w p r) (s : Snapshot w p r k) (hw : 2 ≤ w) (start ord : Word w)
    (hc : s.cost.val+1 < 2^w) (ho : ord.val+1 < 2^w) : Snapshot w p r k :=
  ((a.stage (s.afterCharge hc)).afterEmit hw (a.record s start ord)).afterIncrement ord ho

end ProbeStep

variable {s : Snapshot w p r k} {ys : List (WordRecord w)} {start ord : Word w}

theorem InCall.costRoom (h : InCall hw H F s ys start ord) (hp : 0 < allowance s) : s.cost.val+1 < 2^w := by
  have hb := h.global rfl
  have hg : 0 < s.globalLeft.val := by unfold allowance at hp; omega
  have hc := s.cap.isLt
  omega

theorem InCall.ordRoom (h : InCall hw H F s ys start ord) : ord.val+1 < 2^w := by
  have ht := h.timestamp
  have hc := s.cost.isLt
  omega

namespace ProbeStep

variable (a : ProbeStep w p r)

theorem finish_allowance (s : Snapshot w p r k) (hw : 2 ≤ w) (start ord : Word w) (hc ho)
    (hp : 0 < allowance s) : allowance (a.finish s hw start ord hc ho) = allowance s - 1 := by
  cases a <;> change min (s.callLeft-1) (min (s.globalLeft.val-1) (s.siteLeft-1)) = allowance s - 1
  all_goals unfold allowance at *; omega

private theorem stage_buffer (hc) (h : RecordBuffer.Holds hw H ys s.records) :
    RecordBuffer.Holds hw H ys (a.stage (s.afterCharge hc)).records := by
  cases a <;> exact ⟨h.fit,rfl,rfl,h.remaining,h.buffer,h.output⟩

private theorem staged_fields (hc) (hs : s.savedStart = BurstRAM.wordBits start)
    (ho : s.ordinal = BurstRAM.wordBits ord) (j : Fin 5) :
    (a.stage (s.afterCharge hc)).records (.field j) =
      BurstRAM.wordBits ((recordFormat hw).words (some (a.record s start ord)) j) := by
  have hfour : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  cases a <;> fin_cases j <;> try first | rfl | exact hs | exact ho
  all_goals
    apply congrArg BurstRAM.wordBits
    apply Fin.ext
    exact Nat.mod_eq_of_lt (by first | exact (by decide : 2 < 4).trans_le hfour | exact (by decide : 3 < 4).trans_le hfour)

private theorem finish_inCall (hin : InCall hw H F s ys start ord) (hp : 0 < allowance s)
    (hb : RecordBuffer.Holds hw H (ys++[a.record s start ord])
      ((a.stage (s.afterCharge (hin.costRoom hp))).afterEmit hw (a.record s start ord)).records) :
    InCall hw H F (a.finish s hw start ord (hin.costRoom hp) hin.ordRoom) (ys++[a.record s start ord])
      start ⟨ord.val+1,hin.ordRoom⟩ := by
  have hroom := hin.room
  have ht := hin.timestamp
  have hg := hin.global rfl
  have hl : 0 < s.siteLeft := by unfold allowance at hp; omega
  have hgpos : 0 < s.globalLeft.val := by unfold allowance at hp; omega
  cases a <;>
    refine ⟨?_,hin.savedEq,rfl,by change start.val + (1+(ord.val+1)) = s.cost.val+1; omega⟩ <;>
    refine ⟨hin.publicH,hin.publicFuel,hin.positive,hin.boundary,?_,?_,hin.privateClock,?_,hin.saved,?_,?_,?_,?_,?_,?_,⟩
  all_goals first
    | (change (ys++[_]).length + (s.siteLeft-1) ≤ _; simp only [List.length_append, List.length_singleton]; omega)
    | exact ⟨hb.fit,rfl,rfl,hb.remaining,hb.buffer,hb.output⟩
    | exact (Nat.sub_le _ _).trans hin.callCredit
    | exact (BurstRAM.length_wordBits _).le
    | (intro _; change s.globalLeft.val-1+(s.cost.val+1) = s.cap.val; omega)
    | (intro h; contradiction)

/-- One external action on the literal graph from the callback to the next
instruction, including the emitted record and both timestamp fields. -/
theorem run (T : Template p r k) (hin : InCall hw H F s ys start ord)
    (hpos : 0 < allowance s) (hbits : a.accepts s) :
    let u := a.finish s hw start ord (hin.costRoom hpos) hin.ordRoom
    ∃ t ≤ 200*(w+1), StackRuns (table T) t (atLabel T (.callback a.callback)) s.bank
      (atLabel T (.segment a.next)) u.bank ∧
      InCall hw H F u (ys++[a.record s start ord]) start ⟨ord.val+1,hin.ordRoom⟩ := by
  let c := s.afterCharge (hin.costRoom hpos)
  let b := a.stage c
  let recd := a.record s start ord
  let e := b.afterEmit hw recd
  have hglobal : 0 < s.globalLeft.val := by unfold allowance at hpos; omega
  have hcall : 0 < s.callLeft := by unfold allowance at hpos; omega
  have hsite : 0 < s.siteLeft := by unfold allowance at hpos; omega
  have hroom := hin.room
  have hbuf := a.stage_buffer (hin.costRoom hpos) hin.buffer
  have ⟨emit,hout⟩ := emit_run T b hw a.next hbuf (by omega) recd
    (a.staged_fields (hin.costRoom hpos) hin.savedEq hin.ordinalEq)
  have he : e.ordinal = BurstRAM.wordBits ord := by cases a <;> exact hin.ordinalEq
  have inc := increment_run T e a.next ord he hin.ordRoom
  have hin' := a.finish_inCall hin hpos hout
  have ht := hin.tag
  have hv := hin.value
  have ha := hin.address
  cases a with
  | read dst addr pc v tail =>
    have charge := precharge_run T s (l := .callback (.read dst addr pc)) (next := .read dst addr pc)
      rfl (hin.costRoom hpos) hglobal hcall hsite
    have payload := read_run T c dst addr pc v tail hbits
    refine ⟨_, ?_, ((charge.trans payload).trans emit).trans inc, hin'⟩
    change 8*w+6 + (s.value.length+s.tag.length+s.address.length+30*w+13) + (25*w+12) + (4*w+2) ≤ _
    omega
  | write addr src pc =>
    have charge := precharge_run T s (l := .callback (.write addr src pc)) (next := .write addr src pc)
      rfl (hin.costRoom hpos) hglobal hcall hsite
    have payload := write_run T c addr src pc
    refine ⟨_, ?_, ((charge.trans payload).trans emit).trans inc, hin'⟩
    change 8*w+6 + (s.tag.length+s.address.length+s.value.length+21*w+9) + (25*w+12) + (4*w+2) ≤ _
    omega

end ProbeStep
end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
