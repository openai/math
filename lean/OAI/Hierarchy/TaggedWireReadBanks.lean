import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.ProtocolRAMRunMemory

namespace OAI
/-! # Independence of a native computation from its future selector fields -/

namespace Hierarchy.WireTelescope.ReadBanks
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
variable {W : ℕ}

/-- Full memory equality outside the (possibly scattered) future selector cells. -/
def Agree (future : ℕ → Prop) (left right : Memory W) : Prop :=
  ∀ a, ¬future a → left a=right a

def PublicBank (future : ℕ → Prop) (bank : Bank) : Prop :=
  ∀ a,bank.base≤a → a<bank.base+bank.size → ¬future a

def NoFuture (future : ℕ → Prop) : Expr → Prop
  | .row | .lit _ => True
  | .lookup bank index => PublicBank future bank ∧ NoFuture future index
  | .op _ x y => NoFuture future x ∧ NoFuture future y
  | .branch _ x y yes no => NoFuture future x ∧ NoFuture future y ∧ NoFuture future yes ∧ NoFuture future no

theorem bank_read (bank : Bank) {m m' : Memory W} {future : ℕ→Prop}
    (same : Agree future m m') («public» : PublicBank future bank) (value : Word W) :
    bank.read m value=bank.read m' value := by
  have small := Nat.mod_lt value.val (Nat.two_pow_pos bank.bits)
  exact same _ («public» _ (Nat.le_add_right ..) (by
    change bank.base+value.val % 2^bank.bits < bank.base+2^bank.bits
    omega))

theorem eval (e : Expr) {future : ℕ→Prop} {m m' : Memory W} (same : Agree future m m')
    (ok : NoFuture future e) (r : Word W) : e.eval m r=e.eval m' r := by
  induction e with
  | row | lit => rfl
  | lookup b i ih =>
    rw [Expr.eval,Expr.eval,ih ok.2]
    exact bank_read b same ok.1 _
  | op _ _ _ hx hy => simp only [Expr.eval,hx ok.1,hy ok.2]
  | branch _ _ _ _ _ hx hy ha hb => simp only [Expr.eval,hx ok.1,hy ok.2.1,ha ok.2.2.1,hb ok.2.2.2]

/-- Lookup footprints can be checked on the exact native indices. This
allows later passes to discard frozen solver scratch while keeping its
published decision and trajectory columns. -/
def Observed (live : ℕ→Prop) (m : Memory W) (r : Word W) : Expr → Prop
  | .row | .lit _=>True
  | .lookup bank i=>Observed live m r i ∧ live (bank.base+(i.eval m r).val%bank.size)
  | .op _ x y=>Observed live m r x ∧ Observed live m r y
  | .branch c x y yes no=>Observed live m r x ∧ Observed live m r y ∧
      (if c.test (x.eval m r) (y.eval m r) then Observed live m r yes else Observed live m r no)

theorem eval_observed (live : ℕ→Prop) (m m' : Memory W) (same : ∀a,live a→m a=m' a)
    (e : Expr) (r : Word W) (read : Observed live m r e) : e.eval m r=e.eval m' r := by
  induction e with
  | row | lit => rfl
  | lookup b i ih =>
    rw [Expr.eval,Expr.eval,←ih read.1]
    exact same _ read.2
  | op _ x y hx hy => simp only [Expr.eval,hx read.1,hy read.2]
  | branch c x y yes no hx hy ha hb =>
    rcases read with ⟨rx,ry,branch⟩
    simp only [Expr.eval,←hx rx,←hy ry]
    split at branch <;> rename_i flag
    · simpa only [ite_eq_left flag] using ha branch
    · simpa only [ite_eq_right flag] using hb branch

/-- Two genuine frozen runs export the same locations and agree off their
work slab, up to the unobserved future histogram words. This is the exact
live set passed to the next batch. -/
theorem published {m m' out out' : Memory W} {future : ℕ→Prop} (lo hi : ℕ)
    (records : ℕ→Prop) (same : Agree future m m')
    (left : ∀a,a<lo ∨ hi≤a → out a=m a) (right : ∀a,a<lo ∨ hi≤a → out' a=m' a)
    (rows : ∀a,records a→ out a=out' a) : ∀a,
      ((¬future a ∧ (a<lo ∨ hi≤a)) ∨ records a) → out a=out' a := by
  rintro a (⟨seen,off⟩|record)
  · exact (left a off).trans ((same a seen).trans (right a off).symm)
  · exact rows a record

/-- Back-propagate one requested output word through a native scan. The
computed row needs only its actual lookup addresses, and an untouched
output needs only its own old value. -/
theorem pass_word (p : Pass) (live : ℕ→Prop) (m m' : Memory W)
    (same : ∀a,live a→m a=m' a) (a : ℕ)
    (inputs : if p.out≤a ∧ a<p.out+p.rows then Observed live m ((a:Word W)-(p.out:Word W)) p.term else live a) :
    p.apply m a = p.apply m' a := by
  unfold Pass.apply image fillSegment
  split at inputs <;> rename_i inside
  · simpa only [ite_eq_left inside] using eval_observed live m m' same p.term _ inputs
  · simpa only [ite_eq_right inside] using same a inputs

theorem scan (out n : ℕ) (e : Expr) {future : ℕ→Prop} {m m' : Memory W}
    (same : Agree future m m') (ok : NoFuture future e) :
    Agree future (image out n e m) (image out n e m') := by
  intro a «public»
  simp only [image,fillSegment]
  split
  · exact eval e same ok _
  · exact same a «public»

theorem passes (list : List Pass) {future : ℕ→Prop} {m m' : Memory W} (same : Agree future m m')
    (ok : ∀p∈list,NoFuture future p.term) : Agree future (result list m) (result list m') := by
  induction list generalizing m m' with
  | nil => exact same
  | cons p ps ih =>
    exact ih (scan p.out p.rows p.term same (ok p (by simp))) (fun z hz=>ok z (List.mem_cons_of_mem p hz))

/-- A trace certificate identifies every actual dynamic read address. Writes
may be anywhere, since identical instructions store identical public values. -/
def PublicReads {C : Type*} (future : ℕ→Prop) (P : Program W C) : ℕ→C→Memory W→Prop
  | 0,_,_ => True
  | t+1,c,m => match P.step c with
    | .localStep next => PublicReads future P t next m
    | .read a next => ¬future a.val ∧ PublicReads future P t (next (m a.val)) m
    | .write a v next => PublicReads future P t next (writeMemory m a v)
    | _ => True

theorem write {m m' : Memory W} {future : ℕ→Prop} (a v : Word W) (same : Agree future m m') :
    Agree future (writeMemory m a v) (writeMemory m' a v) := by
  intro x «public»
  simp only [writeMemory]
  split
  · rfl
  · exact same x «public»

theorem replay {C : Type*} (future : ℕ→Prop) (P : Program W C) (t : ℕ) (start : C)
    (m m' : Memory W) (same : Agree future m m') (ok : PublicReads future P t start m) :
    Agree future (memoryAfter P t start m) (memoryAfter P t start m') := by
  induction t generalizing start m m' with
  | zero => exact same
  | succ t ih =>
    cases step : P.step start with
    | localStep next =>
      simp only [PublicReads,step] at ok
      simpa only [memoryAfter,step] using ih next m m' same ok
    | read a next =>
      simp only [PublicReads,step] at ok
      have value := same a.val ok.1
      simpa only [memoryAfter,step,←value] using ih (next (m a.val)) m m' same ok.2
    | write a v next =>
      simp only [PublicReads,step] at ok
      simpa only [memoryAfter,step] using ih next _ _ (write a v same) ok
    | branch | finish | reject => simpa only [memoryAfter,step] using same

/-- Close the very instruction block used by the standard native executor. -/
def traceProgram (A : Procedure W) :=
  (ContinuationLink.close A.block (0:Fin 1) (fun _ _=>.accept) A.publicData).program

def ProcedureReads (future : ℕ→Prop) (A : Procedure W) (ticks : ℕ) (m : Memory W) : Prop :=
  PublicReads future (traceProgram A) ticks ((traceProgram A).start 0) m

theorem executed (A : Procedure W) {future : ℕ→Prop} (ticks : ℕ) {m v out out' : Memory W}
    (same : Agree future m v) (safe : ProcedureReads future A ticks m)
    (left : A.Exec m out ticks) (right : A.Exec v out' ticks) : Agree future out out' := by
  rw [←ProtocolRAM.runMemory_eq A ticks m out left,←ProtocolRAM.runMemory_eq A ticks v out' right]
  exact replay future (traceProgram A) ticks ((traceProgram A).start 0) m v same safe

end Hierarchy.WireTelescope.ReadBanks

end OAI
