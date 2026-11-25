import OAI.Hierarchy.DescentTerminalPopulationDigits
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentColonySplitRAM

namespace OAI
/-! # Terminal population from the paid pages and the already counted cohort headers -/
namespace Hierarchy.DescentTerminalPopulation.RAM
open DescentSIMDLookup DescentPackedZip ProtocolRAM DescentColonies.SplitRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable (H G M a b c lo : ℕ) {w : ℕ}
local notation "J" => chunks G M
local notation "width" => 2^(a*M)
def root : Bank := ⟨lo,Nat.clog 2 H⟩
def broadcast : Bank := ⟨lo+(root H lo).size,c⟩
def tariff (j : Fin J) : Bank := ⟨(broadcast H c lo).base+2^c+j.val*width,a*M⟩
def lease := (root H lo).size+2^c+J*width
def literal (i : ℕ) :=
  if i<(root H lo).size then i*J else
  let j:=i-(root H lo).size
  if j<2^c then common b G j else
  let t:=j-2^c
  if ok:t/width<J then part a b G M ⟨t/width,ok⟩ (Fin.ofNat width (t%width)) else 0

def setup (w : ℕ) := DescentStaticWordColumn.program w lo (literal H G M a b c lo) (lease H G M a c lo)
def ready (m : Memory w) := DescentStaticWordColumn.image lo (literal H G M a b c lo) m (lease H G M a c lo)
local notation "high" => lo+lease H G M a c lo
local notation "warm" => ready H G M a b c lo

private theorem tar_read (j:Fin J) (i:Cell (a*M)) :
    literal H G M a b c lo ((root H lo).size+2^c+j.val*width+i.val)=part a b G M j i := by
  have pos:=Nat.two_pow_pos (a*M)
  have idx:=i.isLt
  have small:=Nat.div_eq_of_lt idx
  have mod_:=Nat.mod_eq_of_lt idx
  have div_:(j.val*width+i.val)/width=j.val:=by rw [Nat.mul_comm j.val width,Nat.mul_add_div pos,small,Nat.add_zero]
  have rem_:(j.val*width+i.val)%width=i.val:=by rw [Nat.mul_add_mod_self_right,mod_]
  have low : ¬ (root H lo).size+(2^c+(j.val*width+i.val)) < (root H lo).size := Nat.not_lt.mpr (Nat.le_add_right ..)
  have mid : ¬ 2^c+(j.val*width+i.val) < 2^c := Nat.not_lt.mpr (Nat.le_add_right ..)
  have cell : Fin.ofNat width i.val = i := Fin.ext (Nat.mod_eq_of_lt idx)
  rw [show (root H lo).size+2^c+j.val*width+i.val = (root H lo).size+(2^c+(j.val*width+i.val)) by ac_rfl]
  simp only [literal,low,mid,ite_false,Nat.add_sub_cancel_left,div_,dite_eq_left j.isLt,rem_,cell]

theorem mount (m:Memory w) (room:high<2^w) :
    (setup H G M a b c lo w).Exec m (warm m) (4+10*lease H G M a c lo) ∧
    (∀h:Fin H,warm m ((root H lo).base+h.val)=((h.val*J:ℕ):Word w)) ∧
    (∀z:Cell c,warm m ((broadcast H c lo).base+z.val)=(common b G z.val:Word w)) ∧
    (∀j:Fin J,∀z:Cell (a*M),warm m ((tariff H G M a c lo j).base+z.val)=(part a b G M j z:Word w)) ∧
    ∀i,i<lo ∨ high≤ i→warm m i=m i := by
  have lease_:(root H lo).size+2^c+J*width=lease H G M a c lo:=rfl
  have blocksPos : 0 < 2^c := Nat.two_pow_pos c
  have hlen:H≤(root H lo).size:=Nat.le_pow_clog (by decide) H
  have read (i : ℕ) (hi : i < lease H G M a c lo) :
      warm m (lo+i) = (literal H G M a b c lo i : Word w) :=
    DescentStaticWordColumn.read lo _ _ m hi
  refine ⟨DescentStaticWordColumn.mount lo (lease H G M a c lo) (literal H G M a b c lo) m room,?_,?_,?_,DescentStaticWordColumn.frame lo (lease H G M a c lo) (literal H G M a b c lo) m⟩
  · intro h;have at_:=h.isLt.trans_le hlen
    exact (read h.val (by omega)).trans (by simp [literal,at_])
  · intro z
    have bound:=z.isLt
    change warm m (lo+(root H lo).size+z.val)=_
    rw [Nat.add_assoc,read ((root H lo).size+z.val) (by omega)]
    have low : ¬ (root H lo).size+z.val < (root H lo).size := Nat.not_lt.mpr (Nat.le_add_right ..)
    simp only [literal,ite_eq_right low,Nat.add_sub_cancel_left,ite_eq_left bound]
  · intro j z
    have cap_:j.val*width+z.val<J*width:=by simpa only [finProdFinEquiv_apply_val,Nat.mul_comm width j.val,Nat.add_comm] using (finProdFinEquiv (j,z)).isLt
    change warm m (lo+(root H lo).size+2^c+j.val*width+z.val)=_
    rw [show lo+(root H lo).size+2^c+j.val*width+z.val=lo+((root H lo).size+2^c+j.val*width+z.val) by ac_rfl,
      read ((root H lo).size+2^c+j.val*width+z.val) (by omega),tar_read]

variable (old ext : Bank)
def bit (j : Fin J) : Expr :=
  .lookup (tariff H G M a c lo j)
    (.lookup old (.op .add (.lookup (root H lo) .row) (.lit j.val)))
def body : Expr := .op .add (.lookup (broadcast H c lo) (.lookup ext .row))
  (total (bit H G M a c lo old) (List.finRange J))

private theorem fold_read {I : Type*} (f : I→Expr) (n : I→ℕ) (m : Memory w) (v : Word w)
    (read : ∀i,(f i).eval m v=(n i:Word w)) (xs : List I) :
    (total f xs).eval m v=((xs.map n).sum:Word w) := by
  induction xs with
  | nil=>rfl
  | cons j xs ih=>simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,read,ih]

section
variable (oldBank extBank : Bank)

structure Fit (out w : ℕ) : Prop where
  old : oldBank.Fits w lo
  ext : extBank.Fits w lo
  rows : H*J≤oldBank.size
  heads : H≤extBank.size
  after : high≤out
  space : out<2^w
end

theorem clear (out : ℕ) (ok : Fit H G M a c lo old ext out w) :
    (body H G M a c lo old ext).Fits w out := by
  have z:=ok.space
  have blocksPos : 0 < 2^c := Nat.two_pow_pos c
  have len:=ok.after
  have page : (root H lo).size+2^c+J*width=lease H G M a c lo:=rfl
  have enough (bank:Bank) (h:bank.base+bank.size≤out) : bank.Fits w out:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (h.trans_lt z),h⟩
  have rootOk:(root H lo).Fits w out:=enough _ (by change lo+(root H lo).size≤_;omega)
  have prior:old.Fits w out:=⟨ok.old.1,ok.old.2.1,(ok.old.2.2).trans (by omega)⟩
  refine ⟨⟨enough _ (by change lo+(root H lo).size+2^c≤_;omega),⟨enough ext (ok.ext.2.2.trans (by omega)),trivial⟩⟩,?_⟩
  apply fits_total
  intro j
  have upper: j.val*width+width≤J*width:=by simpa [Nat.succ_mul] using Nat.mul_le_mul_right width j.isLt
  exact ⟨enough _ (by change lo+(root H lo).size+2^c+j.val*width+width≤_;omega),⟨prior,⟨⟨rootOk,trivial⟩,trivial⟩⟩⟩

theorem body_read (out : ℕ) (ok : Fit H G M a c lo old ext out w) (m : Memory w)
    (paid : Fin H→Fin G→Cell a) (counts : Fin H→Cell c)
    (prior : ∀p : Row H G M,m (old.base+(row H G M p).val)=((data paid p).val:Word w))
    (cohorts : ∀h:Fin H,m (ext.base+h.val)=((counts h).val:Word w)) (h:Fin H) :
    (body H G M a c lo old ext).eval (warm m) (h.val:Word w)=(words (M:=M) b paid (fun v=>(counts v).val) h:Word w) := by
  let curr:=warm m
  have len:=ok.after
  have fit:=clear H G M a c lo old ext out ok
  obtain ⟨_,heads,outer,pieces,keep⟩:=mount H G M a b c lo m (len.trans_lt ok.space)
  have cellFit (j:Fin J) : (bit H G M a c lo old j).Fits w out:=by
    let parts:=clear H G M a c lo old ext out ok
    have upper: j.val*width+width≤J*width:=by simpa [Nat.succ_mul] using Nat.mul_le_mul_right width j.isLt
    have blocksPos : 0 < 2^c := Nat.two_pow_pos c
    have high_:=ok.after
    have z:=ok.space
    have big : lo+(root H lo).size+2^c+J*width≤out:=by simpa [lease,Nat.add_assoc] using high_
    have enough (B:Bank) (h:B.base+B.size≤out):B.Fits w out:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (h.trans_lt z),h⟩
    exact ⟨enough _ (by change lo+(root H lo).size+2^c+j.val*width+width≤_;omega),
      ⟨enough _ (ok.old.2.2.trans (by omega)),⟨⟨enough _ (by change lo+(root H lo).size≤_;omega),trivial⟩,trivial⟩⟩⟩
  have read (j:Fin J) : (bit H G M a c lo old j).eval curr (h.val:Word w)=
      (part a b G M j (data paid (h,j)):Word w) := by
    have all:=cellFit j
    have hlen : h.val<(root H lo).size:=h.isLt.trans_le (Nat.le_pow_clog (by decide) H)
    have key:=bank_read (root H lo) curr hlen all.2.2.1.1
    have rowval : (row H G M (h,j)).val=h.val*J+j.val:=by simp [row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have room : (row H G M (h,j)).val<old.size:=(row H G M (h,j)).isLt.trans_le ok.rows
    have data_ := (bank_read old curr room ok.old).trans ((keep _ (.inl ((Nat.add_lt_add_left room _).trans_le ok.old.2.2))).trans (prior (h,j)))
    have part_:=bank_read (tariff H G M a c lo j) curr (data paid (h,j)).isLt all.1
    change (tariff H G M a c lo j).read curr
        (old.read curr ((root H lo).read curr (h.val : Word w) + (j.val : Word w))) = _
    rw [key.trans (heads h),←Nat.cast_add,←rowval,data_]
    exact part_.trans (pieces j _)
  have real:=(bank_read ext curr (h.isLt.trans_le ok.heads) ok.ext).trans
    ((keep _ (.inl ((Nat.add_lt_add_left (h.isLt.trans_le ok.heads) _).trans_le ok.ext.2.2))).trans (cohorts h))
  have ext_ := (bank_read (broadcast H c lo) curr (counts h).isLt fit.1.1).trans (outer (counts h))
  have sum:=fold_read (bit H G M a c lo old) (fun j=>part a b G M j (data paid (h,j))) curr (h.val:Word w) read (List.finRange J)
  rw [←List.ofFn_eq_map,List.sum_ofFn] at sum
  change (body H G M a c lo old ext).eval curr (h.val : Word w) = _
  simp only [body,Expr.eval,RowOp.opcode,BinaryOp.eval,real,ext_,sum,words,Nat.cast_add]

theorem work (old ext : Bank) : (body H G M a c lo old ext).work≤35+30*J := by
  have all:=work_total (bit H G M a c lo old) 25 (fun j=>by simp [bit,Expr.work]) (List.finRange J)
  simp only [List.length_finRange] at all
  simp only [body,Expr.work]
  omega

end
end Hierarchy.DescentTerminalPopulation.RAM

end OAI
