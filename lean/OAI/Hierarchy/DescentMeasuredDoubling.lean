import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # A cheap-code multiplier by the actual dyadic depth of each row -/

namespace Hierarchy.DescentMeasuredDoubling
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
variable {w n b : ℕ}

def column (base b j : ℕ) : Bank := ⟨base+j*2^b,b⟩

def step (base b j : ℕ) (depth : Expr) : Expr :=
  let x:=Expr.lookup (column base b j) .row
  .branch .lt (.lit j) depth (.op .add x x) x

def program (w base b n : ℕ) (value depth : Expr) : ℕ→Procedure w
  | 0=>scan w base n value
  | j+1=>(program w base b n value depth j).seq (scan w (column base b (j+1)).base n (step base b j depth))

def elapsed (n : ℕ) (value depth : Expr) : ℕ→ℕ
  | 0=>4+n*(2*value.work+4)
  | j+1=>elapsed n value depth j+(4+n*(2*(step 0 0 j depth).work+4))

def output (base b n : ℕ) (value depth : Expr) (m : Memory w) : ℕ→Memory w
  | 0=>ProtocolRAM.image base n value m
  | j+1=>ProtocolRAM.image (column base b (j+1)).base n (step base b j depth) (output base b n value depth m j)

theorem cheap (w base b n : ℕ) (value depth : Expr) (k : ℕ) :
    CheapCode (program w base b n value depth k) := by
  induction k with
  | zero=>exact @scan_cheap w base n value
  | succ j ih=>
    exact @cheap_seq w (program w base b n value depth j)
      (scan w (column base b (j+1)).base n (step base b j depth)) (@ih)
      (@scan_cheap w (column base b (j+1)).base n (step base b j depth))

theorem run (base k : ℕ) (value depth : Expr) (raw d : Fin n→ℕ) (m : Memory w)
    (rows : n≤2^b) (width : 2^b<2^w) (endFit : (column base b k).base+n<2^w)
    (vf : value.Fits w base) (df : depth.Fits w base) (digit : ∀i,d i<2^w) (kw : k<2^w)
    (values : ∀i : Fin n,value.eval m (i.val:Word w)=(raw i:Word w))
    (depths : ∀i : Fin n,depth.eval m (i.val:Word w)=(d i:Word w)) :
    let out:=output base b n value depth m k
    (program w base b n value depth k).Exec m out (elapsed n value depth k) ∧
      (∀i : Fin n,out ((column base b k).base+i.val)=((2^min k (d i)*raw i:ℕ):Word w)) ∧
      ∀a<base,out a=m a := by
  induction k with
  | zero=>
    refine ⟨scan_exec _ _ _ m vf (by simpa [column] using endFit),fun i=>?_,?_⟩
    · simpa [output,column,values i] using ProtocolRAMGeneratedWrite.read_image base n value m i
    · exact fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha)
  | succ k ih=>
    have next : (column base b (k+1)).base=(column base b k).base+2^b := by
      simp [column,Nat.add_mul,Nat.add_assoc]
    have st : base≤(column base b k).base := by simp [column]
    have prevFit : (column base b k).base+n<2^w := by rw [next] at endFit;omega
    obtain ⟨prior,previous,unchanged⟩:=ih prevFit (by omega)
    let before:=output base b n value depth m k
    have room : (Expr.lookup (column base b k) .row).Fits w (column base b (k+1)).base :=
      ⟨⟨by simp [Bank.size,column],width,by rw [next];rfl⟩,trivial⟩
    have fits : (step base b k depth).Fits w (column base b (k+1)).base :=
      ⟨trivial,ProtocolRAMGeneratedWrite.fits_mono _ (by rw [next];omega) df,⟨room,room⟩,room⟩
    refine ⟨Procedure.Exec.then (A:=program w base b n value depth k)
      (B:=scan w (column base b (k+1)).base n (step base b k depth))
      prior (scan_exec _ _ _ before fits endFit),?_,?_⟩
    · intro i
      rw [show output base b n value depth m (k+1) ((column base b (k+1)).base+i.val)=
        (step base b k depth).eval before (i.val:Word w) from ProtocolRAMGeneratedWrite.read_image _ _ _ _ i]
      have old : (column base b k).read before (i.val:Word w)=((2^min k (d i)*raw i:ℕ):Word w) := by
        simpa only [Bank.read,Bank.size,column,Fin.val_cast_of_lt ((i.isLt.trans_le rows).trans width),
          Nat.mod_eq_of_lt (i.isLt.trans_le rows)] using previous i
      have dep : depth.eval before (i.val:Word w)=(d i:Word w) :=
        (eval_below depth _ m before df unchanged).trans (depths i)
      simp only [step,Expr.eval,old,dep,Comparison.test,decide_eq_true_eq,Fin.lt_def,
        Fin.val_cast_of_lt (by omega : k<2^w),Fin.val_cast_of_lt (digit i),RowOp.opcode,BinaryOp.eval]
      by_cases inc : k<d i
      · have doubled : 2^k*raw i + 2^k*raw i = 2^(k+1)*raw i := by rw [pow_succ]; ring
        simpa only [ite_eq_left inc,min_eq_left inc.le,min_eq_left (Nat.succ_le_of_lt inc),Nat.cast_add]
          using congrArg (fun z : ℕ => (z : Word w)) doubled
      · have full : d i≤k := Nat.le_of_not_gt inc
        simp only [ite_eq_right inc,min_eq_right full,min_eq_right (full.trans (Nat.le_succ k))]
    · intro a low
      exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by rw [next];omega))).trans (unchanged a low)

end Hierarchy.DescentMeasuredDoubling

end OAI
