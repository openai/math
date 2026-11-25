import OAI.Hierarchy.ProtocolRAMBelow
import OAI.Hierarchy.ProtocolRAMCalendarRun

namespace OAI
/-! # Selectors beyond a stage's high address cannot affect tests, audits or mode receipts -/

namespace Hierarchy.ProtocolRAM.Calendar.Below
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open PurchaseStage
open scoped Classical Fin.CommRing
variable {w q d cut : ℕ} {m n : Memory w}

theorem check (h : Below cut m n) (c : AttemptGate.Check) (ready : c.Ready m) (before : c.out≤cut) :
    Below cut (c.after m) (c.after n) := by
  have score : c.score m=c.score n := funext fun i=>
    congrArg Fin.val (h.expr c.term (i.val:Word w) ready.1 before)
  exact h.fill c.out _ _ _ (fun _ _ _ _=>by rw [score])

theorem tests (h : Below cut m n) (B : Repair q d) (ready : TestsReady B m)
    (x : B.tests.excess.out≤cut) (p : B.tests.payload.out≤cut) (d' : B.tests.discrepancy.out≤cut) :
    Below cut (B.tests.after m) (B.tests.after n) :=
  ((h.check _ ready.1 x).check _ ready.2.1 p).check _ ready.2.2 d'

theorem snapshot (h : Below cut m n) (L : Dispatch) (B : Repair q d) (ready : TestsReady B m)
    (x : B.tests.excess.out≤cut) (p : B.tests.payload.out≤cut) (d' : B.tests.discrepancy.out≤cut)
    (fit : (repairMask B).Fits w B.repairBits.base) (mask : B.repairBits.base≤cut) :
    Below cut (postSnapshot L B m) (postSnapshot L B n) :=
  (h.tests _ ready x p d').scan _ _ _ fit mask

private theorem count_same (h : Below cut m n) (base : ℕ) (key : ℕ→ℕ) (i : ℕ) :
    Below cut (ProtocolRAMScalarCounts.accumulated base key m i)
      (ProtocolRAMScalarCounts.accumulated base key n i) := by
  induction i with
  | zero => exact h
  | succ i ih =>
    intro a ha
    simp only [ProtocolRAMScalarCounts.accumulated]
    split <;> rw [ih a ha]

private theorem key_word (c : Inspection) (m : Memory w) (r : ℕ) (fit : c.Fits w) :
    (invalidExpr c.batch).eval m (r:Word w)=(badKey c.batch m r:Word w) := by
  simp only [invalidExpr,Batch.eval_ifAdmitted _ _ _ _ _ fit.2.2.2.1 fit.2.2.2.2.1 fit.2.2.2.2.2,
    badKey,Batch.valid]
  split <;> split_ifs <;> rfl

theorem inspection (h : Below cut m n) (c : Inspection) (fit : c.Fits w) (bound : c.keys≤cut) :
    Below cut (admissionMemory c.batch c.keys c.tally c.rows m)
      (admissionMemory c.batch c.keys c.tally c.rows n) := by
  have keys : badKey c.batch m=badKey c.batch n := by
    funext u
    have hw := h.expr (invalidExpr c.batch) (u:Word w) fit.1 bound
    rw [key_word _ _ _ fit,key_word _ _ _ fit] at hw
    have large : 1<2^w := by have := fit.2.2.1;omega
    have small (v : Memory w) : badKey c.batch v u<2^w := by unfold badKey;split <;> omega
    simpa only [Fin.val_cast_of_lt (small m),Fin.val_cast_of_lt (small n)] using congrArg Fin.val hw
  unfold admissionMemory
  rw [keys]
  exact count_same ((h.scan _ _ _ fit.1 bound).fill _ _ _ _ (fun _ _ _ _=>rfl)) _ _ _

private theorem auditedColumns (h : Below cut m n) (ps : List Pass) (ready : AuditReady (columns ps) m)
    (bounds : ∀p∈ps,p.out≤cut) : Below cut (auditOut (columns ps) m) (auditOut (columns ps) n) := by
  induction ps generalizing m n with
  | nil => exact h
  | cons p ps ih =>
    exact ih (h.pass p ready.1 (bounds p (List.mem_cons_self ..))) ready.2
      (fun a ha=>bounds a (List.mem_cons_of_mem _ ha))

theorem verdict (h : Below cut m n) (L : Dispatch) (B : Repair q d) (ready : AuditReady (audits L B) m)
    (keyBound : B.keys≤cut) (bounds : ∀p∈writes L B,p.out≤cut)
    (valid : (ProtocolRAM.verdict (audits L B)).Fits w B.verdict) (flag : B.verdict≤cut) :
    Below cut (verdictMemory B.verdict (audits L B) m) (verdictMemory B.verdict (audits L B) n) :=
  (auditedColumns (h.inspection _ ready.1 keyBound) _ ready.2 bounds).scan _ _ _ valid flag

end Hierarchy.ProtocolRAM.Calendar.Below

end OAI
