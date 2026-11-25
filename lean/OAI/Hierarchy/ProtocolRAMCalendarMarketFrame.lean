import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # Two-sided protection of the work ranges of a chronological market event -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure PurchaseStage
open scoped Fin.CommRing Classical
noncomputable section
variable {w q d : ℕ}

/-- An address before or after a half-open native write interval. -/
def apart (x base rows : ℕ) : Prop := x<base ∨ base+rows≤x

private theorem segment_apart (x base rows : ℕ) (word : ℕ→Word w) (m : Memory w)
    (away : apart x base rows) : fillSegment base rows word m x=m x := by
  have h : ¬(base≤x ∧ x<base+rows) := by unfold apart at away;omega
  simp only [fillSegment,ite_eq_right h]

private theorem pass_apart (p : Pass) (m : Memory w) (x : ℕ) (away : apart x p.out p.rows) :
    p.apply m x=m x := by
  unfold Pass.apply image
  exact segment_apart x p.out p.rows (fun addr=>p.term.eval m ((addr:Word w)-(p.out:Word w))) m away

def auditOutside (x : ℕ) : Audit→Prop
  | .native (.column p) => apart x p.out p.rows
  | .native (.conflicts b n d) => apart x (ProtocolConflictPack.Native.dst b n d) n
  | .check c => apart x c.keys c.rows ∧ apart x c.tally 2

private theorem audit_frame (x : ℕ) (s : Audit) (m : Memory w) (safe : auditOutside x s) :
    s.out m x=m x := by
  cases s with
  | native stage =>
    cases stage with
    | column p => exact pass_apart p m x safe
    | conflicts b n d => exact segment_apart _ _ _ _ m safe
  | check c =>
    rcases safe with ⟨keys,tally⟩
    have keep (i : ℕ) : x≠c.tally+badKey c.batch m i := by
      have bin : badKey c.batch m i<2 := by unfold badKey;split <;> decide
      unfold apart at tally
      omega
    have noinc (v : Memory w) (n : ℕ) :
        ProtocolRAMScalarCounts.accumulated c.tally (badKey c.batch m) v n x=v x := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [ProtocolRAMScalarCounts.accumulated,ite_eq_right (keep n),ih]
    change admissionMemory c.batch c.keys c.tally c.rows m x=m x
    rw [admissionMemory,noinc,segment_apart _ _ _ _ _ tally]
    exact segment_apart _ _ _ _ m keys

private theorem audits_frame (x : ℕ) (ss : List Audit) (m : Memory w) (safe : ∀s∈ss,auditOutside x s) :
    auditOut ss m x=m x := by
  induction ss generalizing m with
  | nil => rfl
  | cons s ss ih =>
    exact (ih (s.out m) (fun z hz=>safe z (List.mem_cons_of_mem _ hz))).trans
      (audit_frame x s m (safe s (List.mem_cons_self ..)))

/-- Explicit event write footprints. The test arrays each include their flag,
and an audit admission touches a key array and its two accumulator bins. -/
def outside (C : Chart w q d) (x : ℕ) : Event→Prop
  | .attempt a =>
    let B := repair C a
    let L := C.layout a
    apart x (C.stopAt a) 1 ∧ (x<(C.frozen a).start ∨ (C.frozen a).stop≤x) ∧
      apart x B.tests.excess.out (B.tests.excess.rows+1) ∧
      apart x B.tests.payload.out (B.tests.payload.rows+1) ∧
      apart x B.tests.discrepancy.out (B.tests.discrepancy.rows+1) ∧
      apart x B.repairBits.base L.candidates ∧ (∀s∈audits L B,auditOutside x s) ∧
      apart x B.verdict 1 ∧ (C.commit a).keeps x
  | .feed b => ∀p∈feedPasses C b,apart x p.out p.rows

private theorem passes_frame (x : ℕ) (ps : List Pass) (m : Memory w) (safe : ∀p∈ps,apart x p.out p.rows) :
    result ps m x=m x := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (p.apply m) (fun z hz=>safe z (List.mem_cons_of_mem _ hz))).trans
      (pass_apart p m x (safe p (List.mem_cons_self ..)))

theorem after_outside (C : Chart w q d) (e : Event) (m : Memory w) (x : ℕ)
    (h : ready C e m) (safe : outside C x e) : after C e m x=m x := by
  cases e with
  | feed b => exact passes_frame _ _ _ safe
  | attempt a =>
    let B := repair C a
    let L := C.layout a
    let v := prepared C a m
    rcases safe with ⟨hg,hf,hx,hy,hz,hm,ha,hv,hc⟩
    rcases h with ⟨_,fr,_,_,_,_,_,_,_,_,final,_,_⟩
    rw [after,(C.commit a).frame _ _ final hc]
    change verdictMemory B.verdict (audits L B) (postSnapshot L B v) x=m x
    rw [verdictMemory,image,segment_apart _ _ _ _ _ hv,audits_frame _ _ _ ha]
    change image B.repairBits.base _ _ (B.tests.after v) x=m x
    rw [image,segment_apart _ _ _ _ _ hm]
    change B.tests.discrepancy.after (B.tests.payload.after (B.tests.excess.after v)) x=m x
    rw [AttemptGate.Check.after,segment_apart _ _ _ _ _ hz,
      AttemptGate.Check.after,segment_apart _ _ _ _ _ hy,
      AttemptGate.Check.after,segment_apart _ _ _ _ _ hx]
    change (C.frozen a).after ((guard C a).apply m) x=m x
    rw [(C.frozen a).frame _ _ fr hf]
    exact pass_apart (guard C a) m x hg

theorem run_outside (C : Chart w q d) (es : List Event) (m : Memory w) (x : ℕ)
    (h : mounted C es m) (keep : ∀e∈es,outside C x e) : run C es m x=m x := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
    exact (ih (after C e m) h.2 (fun f hf=>keep f (List.mem_cons_of_mem _ hf))).trans
      (after_outside C e m x h.1 (keep e (List.mem_cons_self ..)))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
