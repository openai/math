import OAI.Computability.VPVNP.RAMProcessorProbeReturn

/-!
# Rejection before or during an external read

An exhausted minimum allowance reaches the charging routine's rejecting row
before any read guess or emitted record. A permitted read with too few guess
bits reaches the physical read routine's rejection. Both cases have the
same native output on arbitrary incident data.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

theorem read_no_word {bs : List Bool} (h : takeWord w bs = none) : bs.length < w := by
  induction w generalizing bs with
  | zero => simp [takeWord] at h
  | succ w ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      cases he : takeWord w bs with
      | none => simpa using ih he
      | some z => simp [takeWord, he] at h

private theorem exhausted {s : Snapshot w p r k} (h : allowance s = 0) :
    s.callLeft = 0 ∨ s.siteLeft = 0 ∨ s.globalLeft.val = 0 ∨ 2^w ≤ s.cost.val+1 := by
  unfold allowance at h
  omega

theorem read_no_credit (T : Template p r k) (s : Snapshot w p r k) (ys : List (WordRecord w))
    (start ord : Word w) (dst addr : Fin r) (next : Fin p) (h : allowance s = 0) :
    ∃ t ≤ 200*(w+1), Meets T hw H F s ys start ord (.callback (.read dst addr next))
      (pending T s (.read dst addr next)) t := by
  have hr := precharge_reject T s (l := .callback (.read dst addr next)) (next := .read dst addr next) rfl (exhausted h)
  refine ⟨Charges.failureTicks s.callLeft s.siteLeft s.globalLeft, (Charges.failureTicks_le s.callLeft s.siteLeft s.globalLeft).trans (by omega), ?_⟩
  simpa only [Meets, pending, LocalProcessor.resume, ISA.Callback.action, h] using hr

theorem write_no_credit (T : Template p r k) (s : Snapshot w p r k) (ys : List (WordRecord w))
    (start ord : Word w) (addr src : Fin r) (next : Fin p) (h : allowance s = 0) :
    ∃ t ≤ 200*(w+1), Meets T hw H F s ys start ord (.callback (.write addr src next))
      (pending T s (.write addr src next)) t := by
  have hr := precharge_reject T s (l := .callback (.write addr src next)) (next := .write addr src next) rfl (exhausted h)
  refine ⟨Charges.failureTicks s.callLeft s.siteLeft s.globalLeft, (Charges.failureTicks_le s.callLeft s.siteLeft s.globalLeft).trans (by omega), ?_⟩
  simpa only [Meets, pending, LocalProcessor.resume, ISA.Callback.action, h] using hr

theorem read_no_guess (T : Template p r k) {s : Snapshot w p r k} {ys start ord}
    (hin : InCall hw H F s ys start ord) (dst addr : Fin r) (next : Fin p)
    (hc : 0 < allowance s) (hb : takeWord w s.choices = none) :
    ∃ t ≤ 200*(w+1), Meets T hw H F s ys start ord (.callback (.read dst addr next))
      (pending T s (.read dst addr next)) t := by
  have hglobal := hin.global rfl
  have hcredits : 0 < s.callLeft ∧ 0 < s.globalLeft.val ∧ 0 < s.siteLeft := by
    unfold allowance at hc
    omega
  have hcost : s.cost.val+1 < 2^w := by have := s.cap.isLt; omega
  have charged := precharge_run T s (l := .callback (.read dst addr next)) (next := .read dst addr next) rfl
    hcost hcredits.2.1 hcredits.1 hcredits.2.2
  have hlen := read_no_word hb
  have fail := read_short T (s.afterCharge hcost) dst addr next hlen
  have he : allowance s = (allowance s-1)+1 := by omega
  have hp : pending T s (.read dst addr next) = none := by
    unfold pending LocalProcessor.resume
    rw [he]
    simp only [ISA.Callback.action, hb, Option.bind_none]
  rw [hp]
  refine ⟨_, ?_, charged.thenReject fail⟩
  have hv := hin.value
  change 8*w+6 + (s.value.length+4*s.choices.length+3) ≤ _
  omega

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
