import OAI.ThreeFlat.Diagonal.ShrinkScoreWord
import OAI.ThreeFlat.Diagonal.ShrinkNavigationExecution
import OAI.ThreeFlat.Diagonal.RefreshImageScan
import OAI.ThreeFlat.RAM.HeaderScanLayout

namespace OAI
/-! # The actual two score scans on a physical shrinking-stage header -/
namespace ThreeFlat.Diagonal.ShrinkStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows RAM.DescriptorScan
open RefreshDemandRows RefreshStageNav ShrinkMotif NavigationPass CompressorPacking.Native
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {W M : ℕ} (cur : Word W) (m : Memory W)
open private nativeMemory nativeValue nativeFits from
  OAI.ThreeFlat.Diagonal.ShrinkChoiceNative

def scoreWord (lo : ℕ) (width : ℕ→Fin 8→ℕ) (a : ℕ) : Word W :=
  let i := a-lo
  (scorePrefix width (i/2) (decide (i%2=1)):Word W)

theorem prefix_run (head cost supply : ℕ) (field : ℕ→ℕ) (H : Scans.Header cur m head 63 field)
    (lo : field 30=cost) (len : field 31=2*(M+1)) (src : field 3=supply)
    (cap : cost+2*(M+1)<2^W) (two : 2<2^W)
    (header_apart : head+64≤cost ∨ cost+2*(M+1)≤head)
    (cur_apart : cur.val<cost ∨ cost+2*(M+1)≤cur.val)
    (supply_apart : supply+8*M≤cost ∨ cost+2*(M+1)≤ supply) (supply_end : supply+8*M≤2^W)
    (width : ℕ→Fin 8→ℕ) (stored : ∀ i<M,∀ j : Fin 8,(m (supply+i*8+j.val)).val=width i j)
    (scores : ∀ i≤M,∀ b,scorePrefix width i b<2^W) :
    let P := Execution.header cur 30 31 (prefixWords cur)
    P.fits m ∧ (P.run m).2=fillSegment cost (2*(M+1)) (scoreWord cost width) m ∧
      (P.run m).1=11+2*(M+1)*(2*(closed (w:=W) (prefixWords cur)).binds+4) := by
  let f := closed (w:=W) (prefixWords cur)
  have readPtr := (H.get 30 (by decide)).trans lo
  have readLen := (H.get 31 (by decide)).trans len
  change (headerWord m cur 30).val+(headerWord m cur 31).val<2^W ∧
    sweep (fun a z=>f.eval Fin.elim0 z (fun _=>a)) (headerWord m cur 31).val (headerWord m cur 30) m=_ ∧ _
  have cast : headerWord m cur 30=(cost:Word W) := by rw [←readPtr,Fin.cast_val_eq_self]
  refine ⟨by rwa [readPtr,readLen],?_,by change 11+(headerWord m cur 31).val*(2*f.binds+4)=_; rw [readLen]⟩
  rw [readLen,cast]
  apply sweep_prefix _ _ _ _ _ cap
  intro i hi
  let alt := fillSegment cost i (scoreWord cost width) m
  let a : Word W := ((cost+i:ℕ):Word W)
  let j : Fin 2 := ⟨i%2,Nat.mod_lt _ (by decide)⟩
  have split : i=i/2*2+j.val := by dsimp [j]; omega
  have av : a.val=cost+i := Fin.val_cast_of_lt (by omega)
  have atCur : alt cur.val=m cur.val := segment_other m _ _ _ _ (by omega)
  have atHead (k : ℕ) (hk : k≤63) : alt (head+k)=m (head+k) := segment_other m _ _ _ _ (by omega)
  have pp (k : ℕ) (hk : k≤63) :
      nativeValue alt a (ptr cur k)=field k := by
    change (alt ((alt cur.val).val+k)).val=_
    rw [atCur,H.pointer,atHead k hk,H.values k hk]
  have pj := prefix_native cur alt a width (i/2) j (by rw [atCur,H.pointer];have := H.fit;omega) two
    (by rw [av,pp 30 (by decide),lo];omega)
    (fun e hr=>by
      rw [pp 3 (by decide),src]
      change (fillSegment cost i (scoreWord cost width) m (supply+(i/2-1)*8+e.val)).val=_
      rw [segment_other m cost i (scoreWord cost width) _ (by have := e.isLt;omega)]
      exact stored _ (by omega) _)
    (by rw [pp 3 (by decide),src]; omega)
    (by
      intro hr
      rw [av]
      have index : cost≤cost+i-2 ∧ cost+i-2<cost+i := by omega
      have previousRow : (cost+i-2-cost)/2=i/2-1 := by omega
      have previousSide : (cost+i-2-cost)%2=j.val := by
        change (cost+i-2-cost)%2=i%2
        omega
      change (fillSegment cost i _ m (cost+i-2)).val=_
      rw [fillSegment,ite_eq_left index,scoreWord,previousRow,previousSide,
        Fin.val_cast_of_lt (scores (i/2-1) (by omega) _)])
  apply pj.trans
  unfold scoreWord
  simp [j]

theorem layout_native (arg : Word W) (field : ℕ→ℕ) (head : ℕ) (H : Scans.Header cur m head 63 field)
    (width : ℕ→Fin 8→ℕ) (len : field 0=M) (cap : field 30+2*M+2≤2^W)
    (tail : ∀ j : Fin 2,(m (field 30+2*M+j.val)).val=scorePrefix width M (decide (j.val=1))) :
    (closed (layoutWord cur)).eval Fin.elim0 m (fun _=>arg)=
      (if scorePrefix width M true < scorePrefix width M false then 1 else 0) := by
  let p := atRow (ptr cur 30) (ptr cur 0) 2
  let val := nativeValue m arg
  have pv : val p=field 30+2*M := by
    change (m ((m cur.val).val+30)).val+(m ((m cur.val).val+0)).val*2=_
    rw [H.pointer,H.values 30 (by decide),H.values 0 (by decide),len,Nat.mul_comm]
  have pf : nativeFits m arg p := ⟨ptr_fit cur m arg 30 (by rw [H.pointer];have := H.fit;omega),
    ⟨ptr_fit cur m arg 0 (by rw [H.pointer];have := H.fit;omega),trivial,trivial⟩,trivial⟩
  have readFits (j : Fin 2) : nativeFits m arg (RAM.MotifRows.field p j.val) :=
    ⟨⟨pf,trivial,trivial⟩,by change val p+j.val<2^W;rw [pv];have := j.isLt;omega⟩
  have exactRead (j : Fin 2) : val (RAM.MotifRows.field p j.val)=scorePrefix width M (decide (j.val=1)) := by
    change (m (val p+j.val)).val=_
    rw [pv,tail]
  have left : val (RAM.MotifRows.field p 0)=scorePrefix width M false := exactRead 0
  have right : val (RAM.MotifRows.field p 1)=scorePrefix width M true := exactRead 1
  have num := closed_read m (fun _=>arg) (layoutWord cur)
    ⟨readFits 1,readFits 0,(m _).isLt,(m _).isLt,by split <;> trivial⟩ (answer:=
      if scorePrefix width M true<scorePrefix width M false then 1 else 0) (by
      change (if decide (val (RAM.MotifRows.field p 1)<val (RAM.MotifRows.field p 0)) then 1 else 0)=_
      simp only [right,left,decide_eq_true_eq])
  split <;> rename_i h <;> simpa [h] using num


theorem layout_run (head : ℕ) (field : ℕ→ℕ) (H : Scans.Header cur m head 63 field)
    (width : ℕ→Fin 8→ℕ) (len : field 0=M) (one : field 33=1)
    (endFit : field 32+1<2^W) (cap : field 30+2*M+2≤2^W)
    (tail : ∀ j : Fin 2,(m (field 30+2*M+j.val)).val=scorePrefix width M (decide (j.val=1))) :
    let E := Execution.header cur 32 33 (layoutWord cur)
    let bit : Word W := if scorePrefix width M true<scorePrefix width M false then 1 else 0
    E.fits m ∧ (E.run m).2=writeMemory m (field 32:Word W) bit ∧
      (E.run m).1=11+(2*(closed (w:=W) (layoutWord cur)).binds+4) := by
  have readPtr := H.get 32 (by decide)
  have readLen := (H.get 33 (by decide)).trans one
  have ptr : headerWord m cur 32=(field 32:Word W) := by rw [←readPtr,Fin.cast_val_eq_self]
  refine ⟨?_,?_,?_⟩
  · change (headerWord m cur 32).val+(headerWord m cur 33).val<2^W
    rw [readPtr,readLen];exact endFit
  · change sweep _ (headerWord m cur 33).val (headerWord m cur 32) m=_
    rw [readLen,ptr]
    change writeMemory m _ ((closed (layoutWord cur)).eval _ _ _)=_
    rw [layout_native cur m _ field head H width len cap tail]
  · change 11+(headerWord m cur 33).val*_=_
    rw [readLen,Nat.one_mul]

theorem rowCost_bound (x : Fin 8→ℕ) (b : Bool) (B : ℕ) (h : ∀ i,x i≤B) :
    rowCost x b≤80*B^2 := by
  have lim (i : Fin 8) : multiplier i≤20 := by fin_cases i <;> decide
  calc
    rowCost x b≤∑ _j:Fin 4,20*B^2 :=
      Finset.sum_le_sum fun i _=>Nat.mul_le_mul (lim _) (Nat.pow_le_pow_left (h _) 2)
    _ = 80*B^2 := by simp;ring

theorem scorePrefix_bound (width : ℕ→Fin 8→ℕ) (r B : ℕ) (b : Bool) (h : ∀ i<r,∀ e,width i e≤B) :
    scorePrefix width r b≤80*r*B^2 := by
  calc
    scorePrefix width r b≤∑ _i∈Finset.range r,80*B^2 :=
      Finset.sum_le_sum fun i hi=>rowCost_bound _ _ _ (h i (Finset.mem_range.mp hi))
    _ = 80*r*B^2 := by simp;ring



end
end ThreeFlat.Diagonal.ShrinkStageNav

end OAI
