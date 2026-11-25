import OAI.Hierarchy.ProtocolRAMCalendarRun

namespace OAI
/-! # A single emitted approval flag for all chronological attempts -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open PurchaseStage
open scoped Fin.CommRing Classical
noncomputable section
variable {w q d : ℕ}

def «protected» (C : Chart w q d) (x : ℕ) : Event→Prop
  | .attempt a =>
    let B := repair C a
    let L := C.layout a
    x<C.stopAt a ∧ (x<(C.frozen a).start ∨ (C.frozen a).stop≤x) ∧ x<B.tests.excess.out ∧
      x<B.tests.payload.out ∧ x<B.tests.discrepancy.out ∧ x<B.repairBits.base ∧
      (∀ u∈audits L B,x<u.low) ∧ x<B.verdict ∧ (C.commit a).keeps x
  | .feed b => ∀ p∈feedPasses C b,x<p.out

notation:max "protected" => Hierarchy.ProtocolRAM.Calendar.«protected»

theorem after_frame (C : Chart w q d) (e : Event) (m : Memory w) (x : ℕ)
    (h : ready C e m) (safe : protected C x e) : after C e m x=m x := by
  cases e with
  | feed b => exact result_below _ _ _ safe
  | attempt a =>
    let B := repair C a
    let L := C.layout a
    let v := prepared C a m
    rcases safe with ⟨hg,hf,hx,hy,hz,hm,ha,hv,hc⟩
    rcases h with ⟨_,fr,_,_,_,_,ok,_,_,_,final,_,_⟩
    rw [after,(C.commit a).frame _ _ final hc]
    change verdictMemory B.verdict (audits L B) (postSnapshot L B v) x=m x
    have outside : ¬ (B.verdict≤x ∧ x<B.verdict+1) := fun cell=>(Nat.not_le.mpr hv) cell.1
    simp only [verdictMemory,image,fillSegment,ite_eq_right outside]
    rw [audit_below _ _ ok x ha]
    change postSnapshot L B v x=m x
    unfold postSnapshot
    have notMask : ¬ (B.repairBits.base≤x ∧ x<B.repairBits.base+L.candidates) := fun cell=>(Nat.not_le.mpr hm) cell.1
    simp only [image,fillSegment,ite_eq_right notMask,AttemptGate.TestBoard.after]
    rw [B.tests.discrepancy.frame _ x hz,B.tests.payload.frame _ x hy,B.tests.excess.frame _ x hx]
    change (C.frozen a).after ((guard C a).apply m) x=m x
    rw [(C.frozen a).frame _ _ fr hf]
    simp [guard,Pass.apply,image,fillSegment,not_le.mpr hg]

theorem run_frame (C : Chart w q d) (es : List Event) (m : Memory w) (x : ℕ)
    (h : mounted C es m) (safe : ∀ e∈es,protected C x e) : run C es m x=m x := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
    exact (ih (after C e m) h.2 (fun f hf=>safe f (by simp [hf]))).trans
      (after_frame C e m x h.1 (safe e (by simp)))

def separated (C : Chart w q d) : List Event→Prop
  | [] => True
  | .attempt a::es => (∀ e∈es,protected C (repair C a).verdict e) ∧ separated C es
  | .feed _::es => separated C es

def admissible (C : Chart w q d) : List Event→Memory w→Prop
  | [],_ => True
  | e::es,m => accepted C e m ∧ admissible C es (after C e m)

/-- Emitted zero on exactly the admitted chronological trajectory. This disjunction
performs no modular addition of decision words. -/
def historyFlag (C : Chart w q d) : List Event→Expr
  | [] => .lit 0
  | .attempt a::es => .branch .eq (word (repair C a).verdict) (.lit 0) (historyFlag C es) (.lit 1)
  | .feed _::es => historyFlag C es

theorem historyFlag_zero (C : Chart w q d) (es : List Event) (m : Memory w) (r : Word w)
    (h : mounted C es m) (ord : separated C es) (wide : 0<w) :
    (historyFlag C es).eval (run C es m) r=0 ↔ admissible C es m := by
  have nonzero : (1:Word w)≠0 := by
    intro same
    have k := congrArg Fin.val same
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at k
    simp at k
  induction es generalizing m with
  | nil => simp [historyFlag,Expr.eval,admissible]
  | cons e es ih =>
    cases e with
    | feed b =>
      simpa [historyFlag,run,admissible,accepted] using ih (after C (.feed b) m) h.2 ord
    | attempt a =>
      have saved := run_frame C es (after C (.attempt a) m) (repair C a).verdict h.2 ord.1
      have flag := attempt_verdict C a m h.1
      simp only [historyFlag,Expr.eval,word_eval,Comparison.test,beq_iff_eq,Nat.cast_zero,
        Nat.cast_one,run,saved,admissible]
      split_ifs with good
      · simp [flag.mp good,ih _ h.2 ord.2]
      · simp [nonzero,show ¬accepted C (.attempt a) m from fun hn=>good (flag.mpr hn)]

def checked (C : Chart w q d) (out : ℕ) :=
  (code C (events C.mesh)).seq (scan w out 1 (historyFlag C (events C.mesh)))

def checkedOut (C : Chart w q d) (out : ℕ) (m : Memory w) :=
  image out 1 (historyFlag C (events C.mesh)) (run C (events C.mesh) m)

def checkedCost (C : Chart w q d) :=
  cost C (events C.mesh)+(4+1*(2*(historyFlag C (events C.mesh)).work+4))

theorem checked_exec (C : Chart w q d) (out : ℕ) (m : Memory w) (h : mounted C (events C.mesh) m)
    (fit : (historyFlag C (events C.mesh)).Fits w out) (room : out+1<2^w) :
    (checked C out).Exec m (checkedOut C out m) (checkedCost C) := by
  apply Procedure.Exec.then (run_exec C _ m h)
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact scan_exec out 1 _ _ fit room M pc reg pub exit rom data cfg start entry same

theorem checked_read (C : Chart w q d) (out : ℕ) (m : Memory w) (h : mounted C (events C.mesh) m)
    (ord : separated C (events C.mesh)) (wide : 0<w) :
    checkedOut C out m out=0 ↔ admissible C (events C.mesh) m := by
  simp only [checkedOut,image,fillSegment,le_refl,Nat.lt_succ_self,and_self,ite_true,sub_self]
  exact historyFlag_zero C _ m _ h ord wide

attribute [local irreducible] CheapCode

theorem checked_cheap (C : Chart w q d) (out : ℕ) : CheapCode (checked C out) :=
  cheap_seq (run_cheap C (events C.mesh)) (scan_cheap w out 1 (historyFlag C (events C.mesh)))


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
