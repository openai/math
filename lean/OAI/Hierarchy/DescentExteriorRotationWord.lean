import OAI.Hierarchy.DescentExteriorSelectedMatrix
import OAI.Hierarchy.DescentColonyMultipliers
import OAI.Hierarchy.DescentMultiplierSeeds
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Recording the literal chosen ordinary multiplier or reset row basis at a date -/
namespace Hierarchy.DescentExteriorRotationWord
open DescentExterior DescentGL DescentColonies ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentPackedColony.Phase.Arena
open scoped Classical Fin.CommRing
noncomputable section
variable {w k : ℕ}

def ordinary (value : ℕ) (table : Bank) : Expr := .lookup table (.lookup ⟨value,0⟩ (.lit 0))
def sheet (hk : 0 < k) (base : ℕ) : Image w :=
  ⟨base,base+(2^k-1),fun a=>if h : a-base < 2^k-1 then
    ((matrixCode (multiplier hk (seedAt k ⟨a-base,h⟩))).val:Word w) else 0⟩

theorem ordinary_run (value out : ℕ) (table : Bank) (m : Memory w) (fit : table.Fits w out)
    (low : value < out) (space : out+1 < 2^w) :
    (scan w out 1 (ordinary value table)).Exec m (ProtocolRAM.image out 1 (ordinary value table) m) 30 ∧
      CheapCode (scan w out 1 (ordinary value table)) := by
  have key : (⟨value,0⟩:Bank).Fits w out:=⟨show 0 < 2^0 by decide,by change 1 < 2^w;omega,by change value+1 ≤ out;omega⟩
  have fits : (ordinary value table).Fits w out := ⟨fit,key,trivial⟩
  exact ⟨scan_exec out 1 (ordinary value table) m fits space,@scan_cheap _ _ _ _⟩

theorem ordinary_read (hk : 0 < k) (value out : ℕ) (table : Bank) (m : Memory w)
    (i : Fin (2^k-1)) (fit : table.Fits w out) (rows : 2^k-1 ≤ table.size)
    (selected : m value=(i.val:Word w)) (rom : (sheet hk table.base).Resident m) :
    ProtocolRAM.image out 1 (ordinary value table) m out=((matrixCode (multiplier hk (seedAt k i))).val:Word w) := by
  have small:=i.isLt
  have shift : table.base+i.val-table.base=i.val:=by omega
  have stored:=rom (table.base+i.val) (Nat.le_add_right ..) (by change table.base+i.val < table.base+(2^k-1);omega)
  have literal : m (table.base+i.val)=((matrixCode (multiplier hk (seedAt k i))).val:Word w) := by
    simpa only [sheet,shift,dite_eq_left small] using stored
  simpa [ProtocolRAM.image,fillSegment,ordinary,Expr.eval,Bank.read,selected,
    Fin.val_cast_of_lt ((i.isLt.trans_le rows).trans fit.2.1),Nat.mod_eq_of_lt (i.isLt.trans_le rows)] using literal

def reset (offset table : Bank) (ptr : Fin k→ℕ) : Expr :=
  .lookup table (DescentExteriorSelectedMatrix.expr offset k ptr)

/-- Control-independent decode and radix-shift words, stored as a single literal interval. -/
def resetSheet (k w origin : ℕ) : Image w :=
  let n:=(2^k)^k
  ⟨origin,origin+n+n,fun a=>if a-origin < n then ((2^k*(a-origin):ℕ):Word w)
    else if h : a-(origin+n) < n then ((DescentExteriorSelectedMatrix.decode k ⟨a-(origin+n),h⟩).val:Word w)
    else 0⟩

theorem reset_run (out : ℕ) (off table : Bank) (ptr : Fin k→ℕ) (m : Memory w)
    (ofit : off.Fits w out) (tfit : table.Fits w out) (before : ∀i,ptr i < out) (space : out+1 < 2^w) :
    (scan w out 1 (reset off table ptr)).Exec m (ProtocolRAM.image out 1 (reset off table ptr) m) (20+24*k) ∧
      CheapCode (scan w out 1 (reset off table ptr)) := by
  have ok : (reset off table ptr).Fits w out:=
    ⟨tfit,DescentExteriorSelectedMatrix.expr_fits off ofit (by omega) k ptr before⟩
  have wk : (reset off table ptr).work=1+12*k+5:=by rw [reset,Expr.work,DescentExteriorSelectedMatrix.expr_work]
  have clock : 4+1*(2*(reset off table ptr).work+4)=20+24*k := by rw [wk]; omega
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  rw [←clock]
  exact scan_exec out 1 (reset off table ptr) m ok space

theorem reset_read (origin out : ℕ) (off table : Bank) (ptr : Fin k→ℕ) (m : Memory w) (μ : Layout k)
    (ofit : off.Fits w out) (tfit : table.Fits w out) (os : (2^k)^k ≤ off.size) (ts : (2^k)^k ≤ table.size)
    (left : off.base=origin) (right : table.base=origin+(2^k)^k)
    (rom : (resetSheet k w origin).Resident m) (selected : DescentGLPermutationRAM.stored ptr m μ) :
    ProtocolRAM.image out 1 (reset off table ptr) m out=((matrixCode μ).val:Word w) := by
  have shifts (i : Fin ((2^k)^k)) : m (off.base+i.val)=((2^k*i.val:ℕ):Word w) := by
    rw [left]
    have bound:=i.isLt
    have delta : origin+i.val-origin=i.val:=by omega
    have got:=rom (origin+i.val) (Nat.le_add_right ..)
      (by change origin+i.val < origin+(2^k)^k+(2^k)^k; omega)
    simpa only [resetSheet,delta,ite_eq_left bound] using got
  have words (i : Fin ((2^k)^k)) : m (table.base+i.val)=((DescentExteriorSelectedMatrix.decode k i).val:Word w) := by
    rw [right]
    have bound:=i.isLt
    have delta : origin+(2^k)^k+i.val-(origin+(2^k)^k)=i.val:=by omega
    have high : ¬ origin+(2^k)^k+i.val-origin < (2^k)^k:=by omega
    have got:=rom (origin+(2^k)^k+i.val) (by change origin ≤ _; omega)
      (by change _ < origin+(2^k)^k+(2^k)^k; omega)
    simpa only [resetSheet,ite_eq_right high,delta,dite_eq_left bound] using got
  simpa only [reset,ProtocolRAM.image,fillSegment,Nat.le_refl,Nat.lt_add_one,and_self,ite_true,sub_self] using
    DescentExteriorSelectedMatrix.program_read off table ofit tfit os ts m shifts words ptr μ selected (0:Word w)

theorem record_frame (out a : ℕ) (m : Memory w) (op : Expr) (apart : out ≠ a) :
    ProtocolRAM.image out 1 op m a=m a := by
  have miss : ¬(out ≤ a ∧ a < out+1):=by omega
  simp only [ProtocolRAM.image,fillSegment,ite_eq_right miss]

/-- A caller can append this whole job in a fresh high interval, including its fixed multiplier advice. -/
theorem ordinary_fresh (hk : 0 < k) (value base : ℕ) (m : Memory w)
    (before : value < base) (space : base+2^k+1 < 2^w) :
    let I:=sheet (w:=w) hk base
    let table : Bank:=⟨base,k⟩
    let out:=base+2^k
    let op:=ordinary value table
    let final:=ProtocolRAM.image out 1 op (I.output m)
    (I.program.seq (scan w out 1 op)).Exec m final ((4+10*(2^k-1))+30) ∧
    CheapCode (I.program.seq (scan w out 1 op)) ∧
    (∀i : Fin (2^k-1),m value=(i.val:Word w)→final out=((matrixCode (multiplier hk (seedAt k i))).val:Word w)) ∧
    ∀a,a < base ∨ out+1 ≤ a→final a=m a := by
  intro I table out op final
  have len : I.length=2^k-1:=by change base+(2^k-1)-base=_;omega
  have rows : 2^k-1 ≤ 2^k := Nat.sub_le _ _
  have baseBefore : base ≤ out := Nat.le_add_right base _
  have endBefore : I.stop ≤ out := Nat.add_le_add_left rows base
  have outRoom : out < 2^w := (Nat.le_succ out).trans_lt space
  have mountRoom : base+I.length < 2^w := (Nat.add_le_add_left (len.le.trans rows) base).trans_lt outRoom
  obtain ⟨write,resident,unchanged⟩:=I.issue m mountRoom
  have fit : table.Fits w out:=⟨Nat.two_pow_pos _,(Nat.le_add_left (2^k) base).trans_lt outRoom,le_rfl⟩
  have low : value < out:=before.trans_le baseBefore
  have save:=ordinary_run value out table (I.output m) fit low space
  rw [len] at write
  refine ⟨(by intro P R C machine; exact Procedure.Exec.then write save.1 machine),
    cheap_seq I.hardware.1 save.2,?_,?_⟩
  · intro i read
    exact ordinary_read hk value out table _ i fit rows
      ((unchanged _ (.inl before)).trans read) resident
  · intro a outside
    have away : out ≠ a := outside.elim (fun lo => ne_of_gt (lo.trans_le baseBefore))
      (fun hi => ne_of_lt (Nat.lt_of_succ_le hi))
    exact (record_frame out a _ op away).trans
      (unchanged a (outside.imp id (fun hi => endBefore.trans ((Nat.le_succ out).trans hi))))

theorem reset_fresh (k : ℕ) (base : ℕ) (ptr : Fin k→ℕ) (m : Memory w)
    (before : ∀i,ptr i < base) (space : base+(2^k)^k+(2^k)^k+1 < 2^w) :
    let n:=(2^k)^k
    let I:=resetSheet k w base
    let off : Bank:=⟨base,k*k⟩
    let table : Bank:=⟨base+n,k*k⟩
    let out:=base+n+n
    let op:=reset off table ptr
    let final:=ProtocolRAM.image out 1 op (I.output m)
    (I.program.seq (scan w out 1 op)).Exec m final ((4+10*(n+n))+(20+24*k)) ∧
    CheapCode (I.program.seq (scan w out 1 op)) ∧
    (∀μ : Layout k,DescentGLPermutationRAM.stored ptr m μ→final out=((matrixCode μ).val:Word w)) ∧
    ∀a,a < base ∨ out+1 ≤ a→final a=m a := by
  intro n I off table out op final
  have len : I.length=n+n:=by change base+n+n-base=_;omega
  obtain ⟨write,resident,unchanged⟩:=I.issue m (by change base+I.length < 2^w;omega)
  have offsize : off.size=n:=by change 2^(k*k)=(2^k)^k;rw [pow_mul]
  have tsize : table.size=n:=offsize
  have positive : 0 < n:=Nat.pow_pos (Nat.two_pow_pos _)
  have ofit : off.Fits w out:=by
    refine ⟨offsize.symm ▸ positive,?_,?_⟩
    · rw [offsize];omega
    · change base+off.size ≤ base+n+n;rw [offsize];omega
  have tfit : table.Fits w out:=by
    refine ⟨tsize.symm ▸ positive,?_,?_⟩
    · rw [tsize];omega
    · change base+n+table.size ≤ base+n+n;rw [tsize]
  have save:=reset_run out off table ptr (I.output m) ofit tfit (fun i=>by
    have h:=before i;change ptr i < base+n+n;omega) space
  rw [len] at write
  refine ⟨(by intro P R C machine; exact Procedure.Exec.then write save.1 machine),
    cheap_seq I.hardware.1 save.2,?_,?_⟩
  · intro μ read
    exact reset_read base out off table ptr _ μ ofit tfit offsize.ge tsize.ge rfl rfl resident
      (fun i=>(unchanged _ (.inl (before i))).trans (read i))
  · intro a outside
    have away : out ≠ a:=by dsimp [out] at *;omega
    exact (record_frame out a _ op away).trans (unchanged _ (by change a < base ∨ base+n+n ≤ a;dsimp [out] at outside;omega))


end
end Hierarchy.DescentExteriorRotationWord

end OAI
