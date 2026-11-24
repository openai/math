import OAI.Computability.VPVNP.PrimedCounterData
import OAI.Computability.VPVNP.PrimedCounterAdminRun
import OAI.Computability.VPVNP.PrimedCounterDispatchRun

/-!
# Native and logical results of a scheduled parser call

The native call emits private ticks before and after the selected routine.
Replaying its report therefore produces the same memory as the routine. A
successful call retains the nomination words below the scratch base and its
probe count charges only reads and writes inside the routine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open BurstRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

variable {L : Lengths} {n r H s w : ℕ} {Q : Layout L n r H w}

/-- The logical and native call reject together or return corresponding parser state and
memory, with the expected control, preserved lower addresses and at most fourteen probes. -/
inductive ItemAgreement (D : Data Q s) (shared : Internal L r H w → Bool)
    (mem : Memory w) (next : Option (Word w)) :
    Option (VisitState n n s) → Option (Report w) → Prop
  | reject : ItemAgreement D shared mem next none none
  | accept {st : VisitState n n s} {out : Report w}
      (holds : D.Holds shared st (after mem out.events))
      (prefixWords : ∀ a < D.base, after mem out.events a = mem a)
      (probes : out.probes ≤ 14) (control : out.result = next) :
      ItemAgreement D shared mem next (some st) (some out)

namespace ItemAgreement

variable {D : Data Q s} {shared : Internal L r H w → Bool} {k : ℕ}
variable {pub : Fin k → Word w} {state : Word w} {small : Flow 16 k}
variable {regs : Regs w 16} {mem : Memory w} {bits : List Bool}
variable {native : Option (Report w)} {next : Option (Word w)} {overhead fuel : ℕ}

/-- The dispatcher's exact report specification for the selected routine. -/
def Framed (native : Option (Report w)) (next : Option (Word w)) (overhead fuel : ℕ)
    (pub : Fin k → Word w) (state : Word w) (small : Flow 16 k)
    (regs : Regs w 16) (mem : Memory w) (bits : List Bool) : Prop :=
  ∀ out, native = some out ↔ ∃ es rs m', Flow.Exec pub state small regs mem es rs m' ∧
    overhead + es.length + 2 ≤ fuel ∧ choiceBits es = bits ∧
    out.events = (List.replicate overhead .tick ++ es) ++ [.tick] ∧
    out.result = next ∧ after mem out.events = m'

theorem reject_of_framed (fr : Framed native next overhead fuel pub state small regs mem bits)
    (he : ∀ es rs m', Flow.Exec pub state small regs mem es rs m' → choiceBits es ≠ bits) :
    ItemAgreement D shared mem next none native := by
  cases hn : native with
  | none => exact .reject
  | some rep =>
    obtain ⟨es,rs,m',hx,_,hb,_⟩ := (fr rep).mp hn
    exact (he es rs m' hx hb).elim

private theorem after_framed (es : List (Event w)) (k : ℕ) (mem : Memory w) :
    after mem ((List.replicate k .tick ++ es) ++ [.tick]) = after mem es := by
  induction k with
  | zero => simp [after, update]
  | succ k ih => simpa [List.replicate_succ, after, update] using ih

theorem accept_of_framed (fr : Framed native next overhead fuel pub state small regs mem bits)
    {st : VisitState n n s} {es : List (Event w)} {rs : Regs w 16} {m' : Memory w}
    (hx : Flow.Exec pub state small regs mem es rs m') (hlen : overhead + es.length + 2 ≤ fuel)
    (hbits : choiceBits es = bits) (hf : D.Fits) (hheld : PrimedStackRAM.Holds D.base (D.input shared) st m')
    (hnom : D.Nominated mem) (hbelow : ∀ a < D.base, m' a = mem a) (hp : countProbes es ≤ 14) :
    ItemAgreement D shared mem next (some st) native := by
  let rep : Report w := ⟨(List.replicate overhead .tick ++ es) ++ [.tick], next⟩
  have hm : after mem rep.events = m' := (after_framed ..).trans (Call.exec_memory hx)
  rw [(fr rep).mpr ⟨es,rs,m',hx,hlen,hbits,rfl,rfl,hm⟩]
  apply accept
  · rw [hm]
    refine ⟨hheld, ?_⟩
    intro j
    have hj : Header.count L + j.val < Q.scratchBase := (Nat.add_lt_add_left j.isLt _).trans_le hf.headers
    rw [hbelow _ (hj.trans_le (Nat.le_add_right ..)), hnom]
  · rwa [hm]
  · change countProbes ((List.replicate overhead .tick ++ es) ++ [.tick]) ≤ 14
    rwa [Dispatch.probes_framed]
  · rfl

/-- A deterministic administrative routine rejects every surplus tape bit. -/
theorem reject_nonempty {ops : List (Op 16 k)} {hne : ops ≠ []}
    (fr : Framed native next overhead fuel pub state (lines ops hne) regs mem bits)
    (hb : bits ≠ []) : ItemAgreement D shared mem next none native := by
  apply reject_of_framed fr
  intro es rs m' hx
  rw [Admin.trace_choiceBits ((Admin.exec_lines_iff_trace hne).mp hx)]
  exact Ne.symm hb

end ItemAgreement
end PrimedCounter

end VPVNP
end Computability
end OAI
