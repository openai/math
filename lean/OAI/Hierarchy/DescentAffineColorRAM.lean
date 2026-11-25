import OAI.Hierarchy.DescentAffineColors
import OAI.Hierarchy.DescentGLPermutationRAM
import OAI.Hierarchy.DescentGLScoreRAM
import OAI.Hierarchy.DescentFirstMinimumRAM
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Physical common affine coloring of the selected colony slabs

The candidate and block ordinals are the public binary coordinates. Only the
actual outgoing amounts of the winning colonies occur in the input memory.
The three passes write the score bank, the first winner and then all paint bits.
-/

namespace Hierarchy.DescentAffineColors.RAM
open DescentColonies ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open DescentGLScoreRAM
open scoped BigOperators Fin.CommRing Classical
noncomputable section

variable {w k C : ℕ}
private abbrev r (k : ℕ) := 2^k
private abbrev nr (k : ℕ) := 2^(k+1)

/-- Low bits are peeled in unsigned order. These are the literal public
coordinates used by the score and paint pages. -/
def unpack : (n : ℕ) → Block n → DescentGL.Bits n
  | 0,_ => Fin.elim0
  | n+1,x =>
    let h : Block n := ⟨x.val/2,(Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (by simpa [pow_succ] using x.isLt)⟩
    Fin.snoc (α:=fun _=>ZMod 2) (unpack n h) ((x.val%2 : ℕ) : ZMod 2)

private theorem unpack_value (n : ℕ) (x : Block n) : value n (unpack n x)=x.val := by
  induction n with
  | zero =>
    have h := x.isLt
    change x.val<1 at h
    change 0=x.val
    omega
  | succ n ih =>
    let h : Block n := ⟨x.val/2,(Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (by simpa [pow_succ] using x.isLt)⟩
    have tail : DescentGL.headRows (Nat.le_succ n) (unpack (n+1) x)=unpack n h := by
      funext i
      change Fin.snoc (α:=fun _=>ZMod 2) (unpack n h) ((x.val%2:ℕ):ZMod 2) (i.castSucc)=unpack n h i
      rw [Fin.snoc_castSucc]
    rw [DescentColonies.value,tail,ih]
    change 2*(x.val/2)+(Fin.snoc (α:=fun _=>ZMod 2) (unpack n h) ((x.val%2:ℕ):ZMod 2) (Fin.last n)).val=x.val
    rw [Fin.snoc_last,ZMod.val_cast_of_lt (Nat.mod_lt _ (by decide : 0<2))]
    omega

theorem unpack_read (n : ℕ) (x : Block n) : unpack n x=(address n).symm x :=
  (address n).eq_symm_apply.symm.mp (Fin.ext (unpack_value n x))

def wordBit (j : Candidate k) (i : Block k) : Bool :=
  let digits := unpack (k+1) j
  decide ((∑ t : Fin k, digits t.castSucc * unpack k i t) + digits (Fin.last k)=0)

@[simp] theorem wordBit_eq (j : Candidate k) (i : Block k) : wordBit j i=thick j i := by
  simp only [wordBit,unpack_read,thick,linear,offset,DescentWalshTables.binaryRow_apply]; rfl

def amount (k base : ℕ) (side : Bool) (i : Block k) : Expr :=
  let bit := lookupRow (nr k) (fun j => (wordBit j i).toNat)
  .branch .eq bit (.lit side.toNat) (.lookup ⟨base,k⟩ (.lit i.val)) (.lit 0)

def half (k base : ℕ) (s : Bool) := sumExpr (r k) (amount k base s)

def deviation (k base : ℕ) : Expr :=
  let a := half k base true
  let b := half k base false
  .branch .lt a b (.op .sub b a) (.op .sub a b)

def scoreExpr (k : ℕ) (ptr : Fin C→ℕ) := sumExpr C (fun c=>deviation k (ptr c))

def scores (base : ℕ) := Bank.mk base (k+1)
def choices (k base : ℕ) := base+nr k
def chosen (k base : ℕ) := choices k base+(nr k-1)
def paint (k base : ℕ) := choices k base+nr k

/-- The signs in the public table depend only on the two binary ordinals.
The winning ordinal is read from the first-minimum pass. -/
def paintExpr (k ptr : ℕ) :=
  chooseField (nr k) 0 (fun j=>lookupRow (r k) (fun i=>(wordBit j i).toNat))
    (.lookup ⟨ptr,0⟩ (.lit 0))

def run (w k base : ℕ) (ptr : Fin C→ℕ) : Procedure w :=
  ((scan w base (nr k) (scoreExpr k ptr)).seq
    (DescentFirstMinimumRAM.code w (choices k base) (scores (k:=k) base) (List.range (nr k)))).seq
      (scan w (paint k base) (r k) (paintExpr k (chosen k base)))

def ticks (k base : ℕ) (ptr : Fin C→ℕ) : ℕ :=
  ((4+nr k*(2*(scoreExpr k ptr).work+4))+
    DescentFirstMinimumRAM.ticks (choices k base) (scores (k:=k) base) (List.range (nr k)))+
    (4+r k*(2*(paintExpr k (chosen k base)).work+4))

private theorem half_eval (m : Memory w) (k base : ℕ) (weights : Block k→ℕ)
    (read : ∀i:Block k,m (base+i.val)=(weights i:Word w)) (bound : nr k<2^w)
    (j : Candidate k) (s : Bool) :
    (half k base s).eval m (j.val:Word w)=(side weights j s:Word w) := by
  have sr : r k<2^w := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_succ k)).trans_lt bound
  have wide : 1<2^w := (show 1≤r k from Nat.two_pow_pos k).trans_lt sr
  have bitEq (a b : Bool) : ((a.toNat:ℕ):Word w)=(b.toNat:Word w) ↔ a=b := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (by cases a <;> simp_all),
      Fin.val_cast_of_lt (by cases b <;> simp_all)]
    cases a <;> cases b <;> decide
  rw [half,sumExpr_eval,side,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [amount,Expr.eval,lookupRow_eval m _ bound.le j,Comparison.test,beq_iff_eq,bitEq,
    wordBit_eq,Bank.read,Bank.size,Fin.val_cast_of_lt (i.isLt.trans sr),Nat.mod_eq_of_lt i.isLt,read,Nat.cast_ite,Nat.cast_zero]

private theorem score_eval (m : Memory w) (ptr : Fin C→ℕ) (A : Fin C→Block k→ℕ)
    (read : ∀ c (i:Block k),m (ptr c+i.val)=(A c i:Word w))
    (bound : nr k<2^w) (cap : ∑c,∑i,A c i<2^w) (j : Candidate k) :
    (scoreExpr k ptr).eval m (j.val:Word w)=(score A j:Word w) := by
  rw [scoreExpr,sumExpr_eval,score,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  let a := side (A c) j true
  let b := side (A c) j false
  have lim : (∑i,A c i)<2^w :=
    (Finset.single_le_sum (f:=fun c=>∑i,A c i) (fun _ _=>Nat.zero_le _) (Finset.mem_univ c)).trans_lt cap
  have ha := (side_le (A c) j true).trans_lt lim
  have hb := (side_le (A c) j false).trans_lt lim
  have lt : (a:Word w)<(b:Word w) ↔ a<b := by
    rw [Fin.lt_def,Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]
  simp only [deviation,Expr.eval,half_eval m k (ptr c) (A c) (read c) bound,
    RowOp.opcode,BinaryOp.eval,Comparison.test,decide_eq_true_eq]
  change (if (a:Word w)<(b:Word w) then (b:Word w)-(a:Word w) else (a:Word w)-(b:Word w)) =
    ((difference a b:ℕ):Word w)
  unfold difference
  rcases lt_trichotomy a b with less | equal | more
  · simp [lt.mpr less,less.le,Nat.cast_sub less.le]
  · simp [equal]
  · have off : ¬((a:Word w)<(b:Word w)) := fun h=>not_lt_of_ge more.le (lt.mp h)
    simp only [ite_eq_right off,ite_eq_right (not_le.mpr more),Nat.cast_sub more.le]

private theorem score_fits (ptr : Fin C→ℕ) (base : ℕ)
    (fit : ∀ c,(Bank.mk (ptr c) k).Fits w base) : (scoreExpr k ptr).Fits w base := by
  have side (c : Fin C) (s : Bool) : (half k (ptr c) s).Fits w base :=
    sumExpr_fits _ (fun i=>⟨lookupRow_fits ..,trivial,⟨fit c,trivial⟩,trivial⟩)
  exact sumExpr_fits _ fun c=>⟨side c true,side c false,⟨side c false,side c true⟩,
    ⟨side c true,side c false⟩⟩

private theorem paint_read (m : Memory w) (ptr : ℕ) {j : Candidate k}
    (key : m ptr=(j.val:Word w)) (bound : nr k<2^w) (i : Block k) :
    (paintExpr k ptr).eval m (i.val:Word w) = ((thick j i).toNat:Word w) := by
  unfold paintExpr
  rw [eval_chooseField _ _ _ _ m _ j (by simpa only [Nat.zero_add,nr] using bound.le) (by
    change (m (ptr+((0:Word w).val%2^0))).val=_
    simp [key,Fin.val_cast_of_lt (j.isLt.trans bound)])]
  simpa only [wordBit_eq] using lookupRow_eval m (fun i=> (wordBit j i).toNat)
    ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_succ k)).trans bound.le) i

/-- The true chronological scan computes the scores, records the first minimum
including ties, and physically writes the selected thick/thin paint at each block. -/
theorem execution (base : ℕ) (ptr : Fin C→ℕ) (m : Memory w) (A : Fin C→Block k→ℕ)
    (prior : ∀c,ptr c+r k≤base) (room : paint k base+r k<2^w)
    (cap : ∑c,∑i,A c i<2^w) (input : ∀ c (i : Block k),m (ptr c+i.val)=(A c i:Word w)) :
    ∃ out : Memory w, ∃ j : Candidate k,
      (run w k base ptr).Exec m out (ticks k base ptr) ∧
      (scanMinimum (scoreAt A) (List.range (nr k))).1=some (j.val,score A j) ∧
      (∀u,score A j ≤ score A u) ∧ out (chosen k base)=(j.val:Word w) ∧
      (∀ i : Block k,out (paint k base+i.val)=((thick j i).toNat:Word w)) ∧
      ∀ a<base,out a=m a := by
  let e := scoreExpr k ptr
  let b := scores (k:=k) base
  let mem := image base (nr k) e m
  let ks := List.range (nr k)
  let priorMin := DescentFirstMinimumRAM.after (choices k base) b mem ks
  have sizes : base+nr k<2^w ∧ choices k base+nr k<2^w := by
    dsimp [paint,choices] at room ⊢
    omega
  have range : nr k<2^w := by omega
  have block : r k<2^w := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_succ k)).trans_lt range
  have wide : 1<2^w := (show 1≤r k from Nat.two_pow_pos k).trans_lt block
  have coeff : ∀ j : Candidate k,mem (base+j.val)=(score A j:Word w) := by
    intro j
    rw [show mem (base+j.val)=e.eval m (j.val:Word w) from ProtocolRAMGeneratedWrite.read_image ..]
    exact score_eval m ptr A input range cap j
  have fit : b.Fits w (choices k base) := ⟨Nat.two_pow_pos _,range,le_rfl⟩
  have before : chosen k base<paint k base := by
    have := Nat.two_pow_pos (k+1)
    dsimp [chosen,paint,nr]; omega
  obtain ⟨j,win,best⟩ := first A
  have selected : priorMin (chosen k base)=(j.val:Word w) := by
    change DescentFirstMinimumRAM.after _ _ _ _ (choices k base+(nr k-1))=_
    rw [show nr k=ks.length by simp [ks]]
    apply DescentFirstMinimumRAM.winner b mem (scoreAt A) ks fit _ _ _ win
    · intro u hu; exact List.mem_range.mp hu
    · intro u hu
      have valid := List.mem_range.mp hu
      simpa [scoreAt,valid,b,scores] using coeff ⟨u,valid⟩
    · intro u hu
      have valid := List.mem_range.mp hu
      simpa [scoreAt,valid] using (score_le A ⟨u,valid⟩).trans_lt cap
  let col := paintExpr k (chosen k base)
  let result := image (paint k base) (r k) col priorMin
  refine ⟨result,j,?_,win,best,?_,?_,?_⟩
  · apply Procedure.Exec.then (Procedure.Exec.then
      (scan_exec base (nr k) e m (score_fits ptr base (fun c=>⟨Nat.two_pow_pos _,block,prior c⟩)) sizes.1)
      (DescentFirstMinimumRAM.exec b mem ks fit (by simpa [ks] using sizes.2) wide))
    have safe : col.Fits w (paint k base) := DescentGLPermutationRAM.fits_choose _ _ _ _
      ⟨⟨Nat.two_pow_pos 0,wide,Nat.succ_le_of_lt before⟩,trivial⟩ (fun _=>lookupRow_fits ..)
    exact @scan_exec w (paint k base) (r k) col priorMin safe room
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl before)).trans selected
  · intro i
    exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ i).trans (paint_read priorMin _ selected range i)
  · intro a lo
    have earliest : a<choices k base := lo.trans_le (Nat.le_add_right ..)
    have early : a<paint k base := earliest.trans_le (Nat.le_add_right ..)
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl early)).trans
      ((DescentFirstMinimumRAM.frame _ _ _ _ _ earliest).trans
        (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl lo)))

/-- Linear in the number of colony slots. Both additional factors depend
only on the number of block addresses in one group. -/
theorem ticks_le (k base : ℕ) (ptr : Fin C→ℕ) :
    ticks k base ptr ≤ 1000*(C+1)*(r k+1)^4 := by
  have side (c : Fin C) (s : Bool) : (half k (ptr c) s).work≤1+r k*(5*nr k+12) := by
    apply (sumExpr_work (amount k (ptr c) s) (U:=5*nr k+11) _).trans_eq (by ring)
    intro i
    simp [amount,Expr.work,lookupRow_work]
  have block (c : Fin C) : (deviation k (ptr c)).work≤6*(1+r k*(5*nr k+12))+3 := by
    have yes := side c true
    have no := side c false
    simp only [deviation,Expr.work]
    omega
  have cols := sumExpr_work (fun c=>deviation k (ptr c)) block
  have best := DescentFirstMinimumRAM.length_budget (choices k base) (scores (k:=k) base) (List.range (nr k))
  rw [List.length_range] at best
  have coloring : (paintExpr k (chosen k base)).work=1+nr k*(9+5*r k) := by
    rw [paintExpr,DescentGLPermutationRAM.work_choose _ _ _ _ _ (fun j=>lookupRow_work _ _)]
    simp [Expr.work]; ring
  unfold ticks scoreExpr
  rw [coloring]
  apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 cols) 4)) 4) best) le_rfl).trans
  simp only [nr,r,pow_succ]
  generalize 2^k=n
  zify
  apply sub_nonneg.mp
  ring_nf
  positivity

end
end Hierarchy.DescentAffineColors.RAM

end OAI
