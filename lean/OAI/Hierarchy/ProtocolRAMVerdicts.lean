import OAI.Hierarchy.ProtocolRAMStages
import OAI.Hierarchy.ProtocolRAMAdmission

namespace OAI
/-! # Chronological admission of each replacement at the inventory it consumes -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing Classical

/-- A check has one key per candidate, followed by two zero-initialized counter words. -/
structure Inspection where
  letters : ℕ
  ports : ℕ
  batch : Batch letters ports
  keys : ℕ
  tally : ℕ
  rows : ℕ

def Inspection.Fits (w : ℕ) (c : Inspection) : Prop :=
  (invalidExpr c.batch).Fits w c.keys ∧ c.keys+c.rows ≤ c.tally ∧ c.tally+2 < 2^w ∧
    c.letters ≤ 2^w ∧ c.batch.copies < 2^w ∧ c.letters*c.batch.copies < 2^w

inductive Audit where
  | native (stage : Stage)
  | check (c : Inspection)

def Audit.low : Audit → ℕ
  | .native (.column p) => p.out
  | .native (.conflicts b n d) => ProtocolConflictPack.Native.dst b n d
  | .check c => c.keys

noncomputable def Audit.out {w : ℕ} : Audit → Memory w → Memory w
  | .native s,m => s.image m
  | .check c,m => admissionMemory c.batch c.keys c.tally c.rows m

def Audit.ready {w : ℕ} : Audit → Memory w → Prop
  | .native s,m => s.Ready m
  | .check c,_ => c.Fits w

def Audit.code (w : ℕ) : Audit → Procedure w
  | .native s => s.procedure w
  | .check c => admission w c.keys c.tally c.rows c.batch

def Audit.ticks : Audit → ℕ
  | .native s => s.clock
  | .check c => (4+c.rows*(2*(invalidExpr c.batch).work+4))+(7+6*2+11*c.rows)

def Audit.accepts {w : ℕ} : Audit → Memory w → Prop
  | .native _,_ => True
  | .check c,m => ∀ i<c.rows,c.batch.valid m (i:Word w)

theorem Audit.exec {w : ℕ} (s : Audit) (m : Memory w) (ok : s.ready m) :
    (s.code w).Exec m (s.out m) s.ticks := by
  cases s with
  | native s => exact s.exec m ok
  | check c => exact admission_exec _ _ _ _ _ ok.1 ok.2.1 ok.2.2.1 ok.2.2.2.1 ok.2.2.2.2.1 ok.2.2.2.2.2

theorem Audit.below {w : ℕ} (s : Audit) (m : Memory w) (ok : s.ready m)
    (x : ℕ) (low : x<s.low) : s.out m x=m x := by
  cases s with
  | native s =>
    cases s with
    | column p =>
      change x<p.out at low
      simp [out,Stage.image,Pass.apply,image,fillSegment,not_le.mpr low]
    | conflicts b n d =>
      change x<ProtocolConflictPack.Native.dst b n d at low
      simp [out,Stage.image,fillSegment,not_le.mpr low]
  | check c =>
    change x<c.keys at low
    have apart := ok.2.1
    have lt : x<c.tally := by omega
    simp [out,admissionMemory,ProtocolRAMScalarCounts.below _ _ _ _ x lt,
      fillSegment,not_le.mpr lt,image,not_le.mpr low]

def auditCode (w : ℕ) : List Audit → Procedure w
  | [] => program w []
  | s::ss => (s.code w).seq (auditCode w ss)

noncomputable def auditOut {w : ℕ} : List Audit → Memory w → Memory w
  | [],m => m
  | s::ss,m => auditOut ss (s.out m)

def auditTicks : List Audit → ℕ
  | [] => 4
  | s::ss => s.ticks + auditTicks ss

def AuditReady {w : ℕ} : List Audit → Memory w → Prop
  | [],_ => True
  | s::ss,m => s.ready m ∧ AuditReady ss (s.out m)

def AllAdmitted {w : ℕ} : List Audit → Memory w → Prop
  | [],_ => True
  | s::ss,m => s.accepts m ∧ AllAdmitted ss (s.out m)

theorem audit_exec {w : ℕ} (ss : List Audit) (m : Memory w) (ok : AuditReady ss m) :
    (auditCode w ss).Exec m (auditOut ss m) (auditTicks ss) := by
  induction ss generalizing m with
  | nil => exact program_exec [] m (by simp)
  | cons s ss ih =>
    apply Procedure.Exec.then (s.exec m ok.1)
    intro P R K M pc reg pub exit rom data cfg start entry same
    exact ih (s.out m) ok.2 M pc reg pub exit rom data cfg start entry same

theorem audit_below {w : ℕ} (ss : List Audit) (m : Memory w) (ok : AuditReady ss m)
    (x : ℕ) (lo : ∀s∈ss,x<s.low) : auditOut ss m x=m x := by
  induction ss generalizing m with
  | nil => rfl
  | cons s ss ih =>
    exact (ih (s.out m) ok.2 (fun t ht=>lo t (List.mem_cons_of_mem _ ht))).trans
      (s.below m ok.1 x (lo s (List.mem_cons_self ..)))

def verdict : List Audit → Expr
  | [] => .lit 0
  | .native _::ss => verdict ss
  | .check c::ss => .branch .eq (.lookup ⟨c.tally+1,0⟩ (.lit 0)) (.lit 0) (verdict ss) (.lit 1)

/-- Each historical tally must remain visible until the single final verdict read. -/
def OrderedTallies : List Audit → Prop
  | [] => True
  | .native _::ss => OrderedTallies ss
  | .check c::ss => (∀ s∈ss,c.tally+1<s.low) ∧ OrderedTallies ss

/-- The single returned zero means every selected packet had a valid histogram at
the instant of its stock check, and all inactive selector fields were canonical. -/
theorem verdict_zero {w : ℕ} (ss : List Audit) (m : Memory w) (ok : AuditReady ss m)
    (order : OrderedTallies ss) (wide : 0<w) (r : Word w) :
    (verdict ss).eval (auditOut ss m) r = 0 ↔ AllAdmitted ss m := by
  induction ss generalizing m with
  | nil => simp [verdict,Expr.eval,AllAdmitted]
  | cons s ss ih =>
    cases s with
    | native s =>
      simpa [verdict,AllAdmitted,Audit.accepts,auditOut,Audit.out] using ih (s.image m) ok.2 order
    | check c =>
      let n := admissionMemory c.batch c.keys c.tally c.rows m
      have stored : auditOut ss n (c.tally+1)=n (c.tally+1) :=
        audit_below ss n ok.2 _ order.1
      have space := ok.1.2.1
      have cap := ok.1.2.2.1
      have valid := admissionMemory_flag c.batch c.keys c.tally c.rows m (by omega)
      have tail := ih n ok.2 order.2
      have one : (1:Word w)≠0 := by
        intro eqn
        have hn := congrArg Fin.val eqn
        rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at hn
        exact Nat.one_ne_zero hn
      change (if Comparison.eq.test (Bank.read ⟨c.tally+1,0⟩ (auditOut ss n) 0) 0
        then (verdict ss).eval (auditOut ss n) r else (1:Word w))=0 ↔
        (∀ i<c.rows,c.batch.valid m (i:Word w)) ∧ AllAdmitted ss n
      simp only [Bank.read,Fin.val_zero,Nat.zero_mod,Nat.add_zero,stored,Comparison.test,beq_iff_eq]
      change n (c.tally+1)=0 ↔ _ at valid
      by_cases zero : n (c.tally+1)=0 <;> simp_all

theorem audit_cheap (w : ℕ) (ss : List Audit) : CheapCode (auditCode w ss) := by
  induction ss with
  | nil => exact program_cheap w []
  | cons s ss ih =>
    refine cheap_seq (A:=s.code w) (B:=auditCode w ss) ?_ @ih
    cases s with
    | native stage =>
      cases stage with
      | column p => exact scan_cheap w p.out p.rows p.term
      | conflicts b n d => exact ProtocolConflictPack.Native.scan_cheap w b n d
    | check c =>
      change CheapCode (admission w c.keys c.tally c.rows c.batch)
      refine cheap_seq (A:=scan w c.keys c.rows (invalidExpr c.batch))
        (B:=(ProtocolRAMScalarCounts.clear w c.tally 2).seq (ProtocolRAMScalarCounts.counting w c.keys c.tally c.rows))
        (scan_cheap w c.keys c.rows (invalidExpr c.batch)) ?_
      apply cheap_seq (A:=ProtocolRAMScalarCounts.clear w c.tally 2) (B:=ProtocolRAMScalarCounts.counting w c.keys c.tally c.rows)
      · exact writing_cheap _ _ _ _ (by trivial)
      · intro P R K pc reg pub exit i
        change Fin 13 at i
        fin_cases i <;> first | trivial

def finalVerdict (w flag : ℕ) (ss : List Audit) :=
  (auditCode w ss).seq (scan w flag 1 (verdict ss))

noncomputable def verdictMemory {w : ℕ} (flag : ℕ) (ss : List Audit) (m : Memory w) :=
  image flag 1 (verdict ss) (auditOut ss m)

theorem finalVerdict_exec {w : ℕ} (ss : List Audit) (flag : ℕ) (m : Memory w)
    (ok : AuditReady ss m) (inputs : (verdict ss).Fits w flag) (space : flag+1<2^w) :
    (finalVerdict w flag ss).Exec m (verdictMemory flag ss m)
      (auditTicks ss+(4+1*(2*(verdict ss).work+4))) := by
  apply Procedure.Exec.then (audit_exec ss m ok)
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact scan_exec flag 1 (verdict ss) _ inputs space M pc reg pub exit rom data cfg start entry same

theorem finalVerdict_flag {w : ℕ} (ss : List Audit) (flag : ℕ) (m : Memory w)
    (ok : AuditReady ss m) (order : OrderedTallies ss) (wide : 0<w) :
    verdictMemory flag ss m flag=0 ↔ AllAdmitted ss m := by
  simp only [verdictMemory,image,fillSegment,le_refl,Nat.lt_succ_self,and_self,ite_true,sub_self]
  exact verdict_zero ss m ok order wide 0

theorem finalVerdict_cheap (w flag : ℕ) (ss : List Audit) : CheapCode (finalVerdict w flag ss) :=
  cheap_seq (A:=auditCode w ss) (B:=scan w flag 1 (verdict ss)) (audit_cheap w ss) (scan_cheap w flag 1 (verdict ss))


end Hierarchy.ProtocolRAM

end OAI
