import OAI.Hierarchy.ProtocolRAMBatch
import OAI.Hierarchy.ProtocolRAMScalarCounts

namespace OAI
/-! # One final acceptance count for all selector fields in a physical batch -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical

variable {w q d : ℕ}

def Batch.valid (b : Batch q d) (m : Memory w) (r : Word w) : Prop :=
  if b.selected m r then b.withinPacket m r ∧ (∑ i, ((b.field i).eval m r).val) = b.copies
  else ∀ i, (b.field i).eval m r = 0

def invalidExpr (b : Batch q d) := b.ifAdmitted (.lit 0) (.lit 1)

noncomputable def badKey (b : Batch q d) (m : Memory w) (i : ℕ) : ℕ :=
  if b.valid m (i : Word w) then 0 else 1

private theorem key_source (b : Batch q d) (m : Memory w) (src n i : ℕ) (hi : i<n)
    (qFit : q≤2^w) (copiesFit : b.copies<2^w) (bounds : q*b.copies<2^w) :
    image src n (invalidExpr b) m (src+i) = (badKey b m i : Word w) := by
  have inside : src≤ src+i ∧ src+i<src+n := by omega
  simp only [image,fillSegment,ite_eq_left inside,Nat.cast_add,add_sub_cancel_left,invalidExpr,
    Batch.eval_ifAdmitted _ _ _ _ _ qFit copiesFit bounds,badKey,Batch.valid]
  split <;> split_ifs <;> rfl

def admission (w src base n : ℕ) (b : Batch q d) : Procedure w :=
  (scan w src n (invalidExpr b)).seq
    ((ProtocolRAMScalarCounts.clear w base 2).seq (ProtocolRAMScalarCounts.counting w src base n))

noncomputable def admissionMemory (b : Batch q d) (src base n : ℕ) (m : Memory w) : Memory w :=
  ProtocolRAMScalarCounts.accumulated base (badKey b m)
    (fillSegment base 2 (fun _=>0) (image src n (invalidExpr b) m)) n

theorem admission_exec (b : Batch q d) (src base n : ℕ) (m : Memory w)
    (fit : (invalidExpr b).Fits w src) (apart : src+n≤base) (limit : base+2<2^w)
    (qFit : q≤2^w) (copiesFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    (admission w src base n b).Exec m (admissionMemory b src base n m)
      ((4+n*(2*(invalidExpr b).work+4))+(7+6*2+11*n)) := by
  let first := image src n (invalidExpr b) m
  let clear := fillSegment base 2 (fun _=>0) first
  have mask : (scan w src n (invalidExpr b)).Exec m first (4+n*(2*(invalidExpr b).work+4)) := scan_exec src n (invalidExpr b) m fit (by omega)
  have erases : (ProtocolRAMScalarCounts.clear w base 2).Exec first clear (4+6*2) := by
    let e : Term w 0 1 := .literal 0
    have spec : (ProtocolRAMScalarCounts.clear w base 2).Spec (fun _=>True)
        (fun a o=>o=fillSegment base 2 (fun _=>0) a) (4+6*2) := PhysicalInputPhases.writing_spec e Fin.elim0 base 2 limit
      (fun _=>True) (fun _=>0) (fun _ _ _ _ _ _ _=>Term.eval_literal ..)
    intro P R K M pc reg pub exit rom data cfg start entry same
    subst start
    exact spec M pc reg pub exit rom data cfg first entry trivial
  have key : ∀ i<n, clear (src+i)=(badKey b m i : Word w) := by
    intro i hi
    have low : src+i<base := by omega
    simpa only [clear,fillSegment,not_le.mpr low,false_and,ite_false,first] using
      key_source b m src n i hi qFit copiesFit sumFit
  have hkey : ∀ i<n,badKey b m i<2 := by
    intro i _
    unfold badKey
    split <;> decide
  have count : (ProtocolRAMScalarCounts.counting w src base n).Exec clear (admissionMemory b src base n m)
      (3+11*n) := by
    intro P R K M pc reg pub exit rom data cfg start entry same
    subst start
    exact ProtocolRAMScalarCounts.run src base 2 n (badKey b m) apart limit (by omega) hkey
      M pc reg pub exit rom data cfg clear entry key
  rw [show 7+6*2+11*n=(4+6*2)+(3+11*n) by omega]
  apply Procedure.Exec.then mask
  apply Procedure.Exec.then erases
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact count M pc reg pub exit rom data cfg start entry same

theorem admissionMemory_flag (b : Batch q d) (src base n : ℕ) (m : Memory w)
    (smallN : n<2^w) :
    admissionMemory b src base n m (base+1)=0 ↔ ∀ i<n,b.valid m (i:Word w) := by
  classical
  let count : ℕ := ∑ j ∈ Finset.range n, if badKey b m j=1 then 1 else 0
  have selected : base ≤ base+1 ∧ base+1<base+2 := by omega
  have eqn : admissionMemory b src base n m (base+1) = (count : Word w) := by
    simp only [admissionMemory,ProtocolRAMScalarCounts.bin,fillSegment,ite_eq_left selected,zero_add,count]
  have small : count ≤ n := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n, 1 := Finset.sum_le_sum fun j _=> by split <;> decide
      _ = n := by simp
  rw [eqn,Fin.ext_iff,Fin.val_cast_of_lt (show count<2^w by omega)]
  change count=0 ↔ _
  rw [show count=0 ↔ ∀ i∈Finset.range n, (if badKey b m i=1 then 1 else 0 : ℕ)=0 from
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)]
  simp [badKey]


/-- The result word is zero precisely when every selected histogram is valid
and every unused field is zero. All counts are bounded even on malformed selectors. -/
theorem admission_spec (b : Batch q d) (src base n : ℕ) (fit : (invalidExpr b).Fits w src)
    (apart : src+n≤base) (limit : base+2<2^w)
    (qFit : q≤2^w) (copiesFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    (admission w src base n b).Spec (fun _=>True)
      (fun m out => out (base+1)=0 ↔ ∀ i<n,b.valid m (i:Word w))
      ((4+n*(2*(invalidExpr b).work+4))+(7+6*2+11*n)) := by
  intro P R K M pc reg pub exit rom data c m entry _
  obtain ⟨t,ht,done,out,ran,stop,eqn⟩ :=
    admission_exec b src base n m fit apart limit qFit copiesFit sumFit
      M pc reg pub exit rom data c m entry rfl
  exact ⟨t,ht,done,out,ran,stop,by rw [eqn]; exact admissionMemory_flag b src base n m (by omega)⟩


end Hierarchy.ProtocolRAM

end OAI
