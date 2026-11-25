import OAI.Hierarchy.DescentTerminalFrozenRoster
import OAI.Hierarchy.DescentTerminalPacketSlotRAM

namespace OAI
/-! # A word per surviving exterior cohort builds the short list for all local operands -/
namespace Hierarchy.DescentTerminalFrozenRoster
open DescentCensusRAM Computability.BorderVNP.FragmentBucket ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
structure Shelf where
  sorted : Bank
  homes : Bank
  rank : Bank
  frozen : Bank
  offsets : Bank
  product : Bank

def owner (L:Shelf) : Expr := .lookup L.homes (.lookup L.sorted .row)
def tag (L:Shelf) (base H : ℕ) : Expr :=
  .op .add (.lit base) (.branch .lt (owner L) (.lit H) (owner L) (.lit H))
def value (L:Shelf) : Expr :=
  .lookup L.product (.op .add (.lookup L.offsets (.lookup L.rank .row)) (.lookup L.frozen (.lookup L.sorted .row)))
def program {w n H:ℕ} (S:Banks w n (H+1)) (L:Shelf) := tally S (tag L S.bins H) (value L)

theorem clocks {w n H:ℕ} (S:Banks w n (H+1)) (L:Shelf) :
    tallyCost S (tag L S.bins H) (value L)≤512*(n+H+1) := by
  simp only [tallyCost,addCost,issueCost,ProtocolRAMGeneratedWrite.work,slot,tag,owner,value,Expr.work]
  omega

structure Old {n H f w:ℕ} (home:Fin n→Fin H) (frozen:Fin n→Fin (2^f)) (L:Shelf) (m:Memory w) : Prop where
  sorted : ∀i:Fin n,L.sorted.read m (i.val:Word w)=(((dest home).symm i).val:Word w)
  homes : ∀u:Fin n,L.homes.read m (u.val:Word w)=((home u).val:Word w)
  rank : ∀i:Fin n,let u:=(dest home).symm i
    L.rank.read m (i.val:Word w)=(prior home u.val (home u):Word w)
  frozenDigit : ∀u:Fin n,L.frozen.read m (u.val:Word w)=((frozen u).val:Word w)

structure Literals {w:ℕ} (f K:ℕ) (L:Shelf) (m:Memory w) : Prop where
  offset : ∀r<K,L.offsets.read m (r:Word w)=((r*2^f:ℕ):Word w)
  product : ∀r<K,∀x:Fin (2^f),L.product.read m ((r*2^f+x.val:ℕ):Word w)=((x.val+1)*(2^(f+1))^r:ℕ)

variable {n H f w:ℕ} (S:Banks w n (H+1)) (L:Shelf) (m:Memory w)
variable (kf : (tag L S.bins H).Fits w S.first) (vf : (value L).Fits w S.first)

def selected (u:Fin H) : Fin (H+1) := u.castSucc
include kf vf in
theorem any :
    ∃out,(program S L).Exec m out (tallyCost S (tag L S.bins H) (value L)) ∧ CheapCode (program S L) := by
  let t (i:Fin n) : Fin (H+1) := ⟨min ((owner L).eval m (i.val:Word w)).val H,by omega⟩
  have fit : H<2^w := by have last:=S.finish; omega
  have keys (i:Fin n) : (tag L S.bins H).eval m (i.val:Word w)=((S.bins+(t i).val:ℕ):Word w) := by
    let x := (owner L).eval m (i.val:Word w)
    have tested : DescriptorExpr.Comparison.lt.test x (H:Word w)=true ↔ x.val<H := by
      simp only [DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt fit]
    change (S.bins:Word w)+(if DescriptorExpr.Comparison.lt.test x (H:Word w) then x else (H:Word w)) =
      ((S.bins+min x.val H:ℕ):Word w)
    by_cases small : x.val<H
    · simp only [ite_eq_left (tested.mpr small),min_eq_left small.le,Nat.cast_add,Fin.cast_val_eq_self]
    · simp only [ite_eq_right (mt tested.mp small),min_eq_right (le_of_not_gt small),Nat.cast_add]
  obtain ⟨out,run,_⟩:=tally_exec S (tag L S.bins H) (value L) t (fun i=>((value L).eval m (i.val:Word w)).val)
    m kf vf keys (fun i=>(Fin.cast_val_eq_self _).symm)
  exact ⟨out,run,@tally_cheap w n (H+1) S (tag L S.bins H) (value L)⟩

include kf vf in
theorem published (home:Fin n→Fin H) (frozen:Fin n→Fin (2^f)) (K:ℕ)
    (width:∀s,count home s≤K) (old:Old home frozen L m) (lits:Literals f K L m) :
    ∃out,(program S L).Exec m out (tallyCost S (tag L S.bins H) (value L)) ∧
      (∀s:Fin H,out (S.bins+s.val)=((book home frozen s).val:Word w)) ∧ ∀a<S.first,out a=m a := by
  let get:=(dest home).symm
  have hH : H<2^w:=by have:=S.finish;omega
  have keys (i:Fin n) : (tag L S.bins H).eval m (i.val:Word w)=((S.bins+(selected (home (get i))).val:ℕ):Word w) := by
    have small: (home (get i)).val<2^w:=(home (get i)).isLt.trans hH
    have inside : DescriptorExpr.Comparison.lt.test ((home (get i)).val:Word w) (H:Word w)=true := by
      simpa only [DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt small,
        Fin.val_cast_of_lt hH] using (home (get i)).isLt
    simp only [tag,owner,Expr.eval,old.sorted,old.homes,RowOp.opcode,BinaryOp.eval]
    change (S.bins:Word w)+(if DescriptorExpr.Comparison.lt.test ((home (get i)).val:Word w) (H:Word w)
        then ((home (get i)).val:Word w) else (H:Word w)) = ((S.bins+(home (get i)).val:ℕ):Word w)
    rw [ite_eq_left inside,Nat.cast_add]
  have values (i:Fin n) : (value L).eval m (i.val:Word w)=(weight home frozen (get i):Word w) := by
    let u:=get i
    have bound:prior home u.val (home u)<K:=(DescentTerminalPacketSlotRAM.ordinal_lt home u).trans_le (width _)
    simp only [value,Expr.eval,old.rank,old.sorted,old.frozenDigit,RowOp.opcode,BinaryOp.eval]
    change L.product.read m (L.offsets.read m (prior home u.val (home u):Word w)+(↑(frozen u).val:Word w)) = _
    rw [lits.offset _ bound,←Nat.cast_add]
    exact lits.product _ bound (frozen u)
  obtain ⟨out,run,read,frame⟩:=tally_exec S (tag L S.bins H) (value L) (fun i=>selected (home (get i)))
    (fun i=>weight home frozen (get i)) m kf vf keys values
  refine ⟨out,run,fun s=>?_,frame⟩
  have mass : sumAt (fun i=>selected (home (get i))) (fun i=>weight home frozen (get i)) (selected s) =
      sumAt home (weight home frozen) s := by
    unfold sumAt
    simpa only [selected,Fin.castSucc_inj] using
      (get.sum_comp (fun i=>if home i=s then weight home frozen i else 0))
  exact (read (selected s)).trans (congrArg (fun k:ℕ=>(k:Word w)) (mass.trans (sum_read home frozen s)))
end
end Hierarchy.DescentTerminalFrozenRoster

end OAI
