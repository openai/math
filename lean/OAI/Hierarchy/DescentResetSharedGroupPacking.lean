import OAI.Hierarchy.DescentResetStemGroupRanks
import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentGLScoreRAM
import OAI.Hierarchy.DescentSparseBinLookup

namespace OAI
/-! # Packing an observed reset-group permutation once for the whole host array -/
namespace Hierarchy.DescentResetSharedGroupPacking
open DescentSIMDLookup DescentPackedZip DescentPackedFlowBatch DescentGLScoreRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {G M b w H Q : ℕ}

def lane (b : ℕ) (src : Fin G→Expr) (c : ℕ) (j : Fin M) : Expr :=
  if live:c*M+j.val<G then
    DescentPacking.SparseBinRAM.scale ((2^b)^j.val) (src ⟨_,live⟩)
  else .lit 0

def expr (M b : ℕ) (src : Fin G→Expr) (c : ℕ) := sumExpr M (lane b src c)

def panel (out : Bank) (n : ℕ) : Expr := .lookup out (.op .mask .row (.lit (2^n-1)))

theorem panel_work (out : Bank) (n : ℕ) : (panel out n).work=9 := rfl

theorem run (out : Bank) (src : Fin G→Expr) (val : Fin G→Cell b) (mem : Memory w)
    (fit : ∀g,(src g).Fits w out.base) (early : ∀g,(src g).eval mem 0=((val g).val:Word w))
    (space : out.base+chunks G M<2^w) :
    let ps:=passes out.base 1 1 (expr M b src) 0 (chunks G M)
    let dst:=result ps mem
    (program w ps).Exec mem dst (clock ps) ∧ CheapCode (program w ps) ∧
    (∀c : Fin (chunks G M),dst (out.base+c.val)=((data (fun (_ : Fin 1) g=>val g) (0,c)).val:Word w)) ∧
    (∀t,t<out.base ∨ out.base+chunks G M≤t→dst t=mem t) := by
  intro ps dst
  have fitted (c : ℕ) : (expr M b src c).Fits w out.base := by
    apply sumExpr_fits
    intro j;unfold lane;split
    · exact DescentPacking.SparseBinRAM.scale_fits _ _ (fit _)
    · trivial
  obtain ⟨exe,read,low⟩:=execute out.base 1 1 (chunks G M) (expr M b src) mem (fun c _=>fitted c)
    (by simpa only [Nat.mul_one] using space) le_rfl
  refine ⟨exe,program_cheap _ _,?_,?_⟩
  · intro c
    have rd:=read c 0
    simp only [Nat.mul_one,Fin.val_zero,Nat.add_zero,Nat.cast_zero] at rd
    dsimp only [dst,ps]
    rw [rd,expr,sumExpr_eval,DescentPackedSumWords.lanes_val,Nat.cast_sum]
    apply Finset.sum_congr rfl;intro j _
    by_cases live:c.val*M+j.val<G
    · simp only [lane,dite_eq_left live,DescentPacking.SparseBinRAM.scale_eval,early,Nat.cast_mul]
      apply mul_comm
    · simp [lane,live,Expr.eval]
  · intro t past
    rcases past with lo|hi
    · exact low t lo
    · exact above out.base 1 1 _ mem 0 (chunks G M) t le_rfl (by simpa only [Nat.zero_add,Nat.mul_one] using hi)

theorem tariff_bound (base u : ℕ) (src : Fin G→Expr) (limit : ∀i,(src i).work≤u) :
    clock (passes base 1 1 (expr M b src) 0 (chunks G M)) ≤
      4+chunks G M*(4+1*(2*(1+M*(1+2^(b*M)*(u+1)+1))+4)) := by
  apply DescentPackedFlowBatch.tariff
  intro c _
  apply sumExpr_work
  intro j
  by_cases hit:c*M+j.val<G
  · simp only [lane,dite_eq_left hit,DescentPacking.SparseBinRAM.scale_work]
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul
    · rw [←pow_mul]
      exact Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_left b j.isLt.le)
    · exact Nat.add_le_add_right (limit _) 1
  · simp [lane,hit,Expr.work]

/-- A single constant-work expression projects the already completed shared
chunk at each host. The actual common row has a dyadic number of chunks. -/
theorem source (out : Bank) (mem : Memory w) (val : Fin G→Cell b) {floor n : ℕ}
    (before : out.Fits w floor) (rows : H*chunks G M≤2^w) (shape : chunks G M=2^n)
    (available : chunks G M≤out.size)
    (stored : ∀c : Fin (chunks G M),mem (out.base+c.val)=((data (fun (_ : Fin 1) g=>val g) (0,c)).val:Word w)) :
    (panel out n).Fits w floor ∧ Source (panel out n) (fun (_ : Fin H) g=>val g) M mem := by
  refine ⟨⟨before,trivial,trivial⟩,?_⟩
  intro p
  let c:=p.2
  let v:=row H G M p
  have cn:c.val<2^n:=shape ▸ c.isLt
  have cs:2^n≤out.size:=shape ▸ available
  have vv:v.val=p.1.val*2^n+c.val:=by
    change p.2.val+chunks G M*p.1.val=_
    calc
      _ = p.1.val*chunks G M+c.val := by change c.val+chunks G M*p.1.val=_; ac_rfl
      _ = _ := congrArg (fun q : ℕ => p.1.val*q+c.val) shape
  have mask:2^n-1<2^w:=(Nat.sub_le ..).trans_lt (cs.trans_lt before.2.1)
  have readKey:BinaryOp.bitAnd.eval (v.val:Word w) ((2^n-1:ℕ):Word w)=(c.val:Word w):=by
    change ((((v.val:Word w).val &&& ((2^n-1:ℕ):Word w).val):ℕ):Word w)=_
    rw [Fin.val_cast_of_lt (v.isLt.trans_le rows),Fin.val_cast_of_lt mask,vv,Nat.and_two_pow_sub_one_eq_mod,Nat.mul_add_mod_of_lt cn]
  change out.read mem (BinaryOp.bitAnd.eval (v.val:Word w) ((2^n-1:ℕ):Word w))=_
  rw [readKey,bank_read out mem (c.isLt.trans_le available) before,stored];rfl

def atGroup (src : Bank) (indexAt : Fin G→Fin Q) (g : Fin G) : Expr := .lookup src (.lit (indexAt g).val)

theorem atGroup_read {Q floor : ℕ} (src : Bank) (indexAt : Fin G→Fin Q) (v : Fin Q→Cell b) (mem : Memory w)
    (fit : src.Fits w floor) (avail : Q≤ src.size) (read : ∀z : Fin Q,mem (src.base+z.val)=((v z).val:Word w))
    (g : Fin G) : (atGroup src indexAt g).Fits w floor ∧ (atGroup src indexAt g).eval mem 0=((v (indexAt g)).val:Word w) := by
  exact ⟨⟨fit,trivial⟩,(bank_read src mem ((indexAt g).isLt.trans_le avail) fit).trans (read _)⟩
/-- The original fine-block digit is read from the same moved full word as
the source group. The index and mask are literal and the data are measured. -/
def lowAt (src : Bank) (indexAt : Fin G→Fin Q) (k : ℕ) (g : Fin G) : Expr :=
  .op .mask (atGroup src indexAt g) (.lit (2^k-1))

theorem lowAt_read {Q floor k : ℕ} (src : Bank) (indexAt : Fin G→Fin Q) (v : Fin Q→ℕ) (mem : Memory w)
    (fit : src.Fits w floor) (avail : Q≤ src.size) (small : ∀z,v z<2^w) (narrow : 2^k≤2^w)
    (read : ∀z : Fin Q,mem (src.base+z.val)=(v z:Word w))
    (g : Fin G) : (lowAt src indexAt k g).Fits w floor ∧
      (lowAt src indexAt k g).eval mem 0=((v (indexAt g)%2^k:ℕ):Word w) := by
  refine ⟨⟨⟨fit,trivial⟩,trivial⟩,?_⟩
  have key: (atGroup src indexAt g).eval mem 0=(v (indexAt g):Word w):=
    (bank_read src mem ((indexAt g).isLt.trans_le avail) fit).trans (read _)
  change BinaryOp.bitAnd.eval ((atGroup src indexAt g).eval mem 0) ((2^k-1:ℕ):Word w)=_
  rw [key]
  change ((((v (indexAt g):Word w).val &&& ((2^k-1:ℕ):Word w).val):ℕ):Word w)=_
  rw [Fin.val_cast_of_lt (small _),Fin.val_cast_of_lt (by have:=Nat.two_pow_pos k;omega),
    Nat.and_two_pow_sub_one_eq_mod]

end
end Hierarchy.DescentResetSharedGroupPacking

end OAI
