import OAI.Hierarchy.DescentRawFieldOps

namespace OAI
/-! # Publishing one raw field with fixed capacities and physically stored active counts -/

namespace Hierarchy.DescentOrdinaryRawRows.Padded
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM DescentOrdinaryDestRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Counts where
  old : ℕ
  pairs : ℕ

def count (a : ℕ) : Expr := .lookup ⟨a,0⟩ (.lit 0)
def guarded (a : ℕ) (active : Expr) : Expr := .branch .lt .row (count a) active (.lit 0)
def address (O : Output) (N : Counts) (j : ℕ) : Expr :=
  .op .add (.op .add (.lit (O.base+j)) (count N.old)) (times 10 .row)

private theorem count_read {w : ℕ} (a : ℕ) (m : Memory w) (i : Word w) : (count a).eval m i=m a := by
  simp [count,Expr.eval,Bank.read,Bank.size]
private theorem count_fits {w out a : ℕ} (wide : 1<2^w) (below : a<out) : (count a).Fits w out :=
  ⟨⟨by change 0<1;decide,wide,by change a+1≤out;omega⟩,trivial⟩

private theorem guarded_read {w : ℕ} (a : ℕ) (expr : Expr) (m : Memory w) (i n : ℕ)
    (row : i<2^w) (fits : n<2^w) (actual : m a=(n:Word w)) :
    (guarded a expr).eval m (i:Word w)=if i<n then expr.eval m (i:Word w) else 0 := by
  have cmp : (i:Word w)<(n:Word w) ↔ i<n := by
    change (i:Word w).val<(n:Word w).val ↔ _
    rw [Fin.val_cast_of_lt row,Fin.val_cast_of_lt fits]
  simp [guarded,Expr.eval,count,Comparison.test,Bank.read,Bank.size,actual,cmp]

private theorem address_read {w : ℕ} (O : Output) (N : Counts) (j i n : ℕ) (m : Memory w)
    (actual : m N.old=(n:Word w)) : (address O N j).eval m (i:Word w)=(O.addr n j i:Word w) := by
  change ((O.base+j:ℕ):Word w)+(count N.old).eval m (i:Word w)+(times 10 .row).eval m (i:Word w)=_
  rw [count_read,actual,times_eval]
  simp [addr,Expr.eval,Nat.cast_add,Nat.cast_mul]; ring

variable (S : Sources) (O : Output) (N : Counts) (b : ℕ) (f : Column)

def pass (w oc pc : ℕ) : ℕ→Procedure w
  | 0=>scan w O.base (oc+10*pc) (guarded N.old (S.old b f))
  | k+1=>(pass w oc pc k).seq (ProtocolRAMGeneratedWrite.program w O.dest O.vals pc
      (address O N k) (guarded N.pairs (S.born b (band k) f)))

def passCost (oc pc : ℕ) : ℕ→ℕ
  | 0=>4+(oc+10*pc)*(2*(guarded N.old (S.old b f)).work+4)
  | k+1=>passCost oc pc k+ProtocolRAMGeneratedWrite.work pc (address O N k) (guarded N.pairs (S.born b (band k) f))

def field (w oc pc : ℕ) := pass S O N b f w oc pc 10
def field_cost (oc pc : ℕ) := passCost S O N b f oc pc 10

structure Bounds (w oc pc : ℕ) : Prop where
  oldFits : (S.old b f).Fits w O.base
  bornFits : ∀s,(S.born b s f).Fits w O.base
  oldBefore : N.old<O.base
  pairsBefore : N.pairs<O.base
  scratch : O.base+(oc+10*pc)≤O.dest
  temporary : O.dest+pc≤O.vals
  memory : O.vals+pc<2^w

private def fillWord {w pairN pc : ℕ} (new : Born→Fin pairN→Word w) (s : Born) (i : Fin pc) : Word w :=
  if h:i.val<pairN then new s ⟨i.val,h⟩ else 0

structure Wrote {w oldN pairN : ℕ} (O : Output) (oc pc : ℕ)
    (raw : Fin oldN→Word w) (new : Born→Fin pairN→Word w) (m out : Memory w) : Prop where
  before : ∀a<O.base,out a=m a
  original : ∀i:Fin oldN,out (O.base+i.val)=raw i
  added : ∀(s : Born) (i : Fin pairN),out (O.addr oldN s.index.val i.val)=new s i
  padding : ∀j,oldN+10*pairN≤j→j<oc+10*pc→ out (O.base+j)=0

private structure Progress {w oldN pairN : ℕ} (O : Output) (oc pc k : ℕ)
    (raw : Fin oldN→Word w) (new : Born→Fin pairN→Word w) (m out : Memory w) : Prop where
  before : ∀a<O.base,out a=m a
  original : ∀i:Fin oldN,out (O.base+i.val)=raw i
  added : ∀j<k,∀i : Fin pairN,out (O.addr oldN j i.val)=new (band j) i
  padding : ∀j,oldN+10*pairN≤j→j<oc+10*pc→ out (O.base+j)=0

theorem publish (w oc pc oldN pairN : ℕ) (raw : Fin oldN→Word w) (new : Born→Fin pairN→Word w) (m : Memory w)
    (room : Bounds S O N b f w oc pc) (oldLe : oldN≤oc) (pairLe : pairN≤pc)
    (oldRead : m N.old=(oldN:Word w)) (pairRead : m N.pairs=(pairN:Word w))
    (rawRead : ∀i : Fin oldN,(S.old b f).eval m i.val=raw i)
    (newRead : ∀s (i : Fin pairN),(S.born b s f).eval m i.val=new s i) :
    ∃out,(field S O N b f w oc pc).Exec m out (field_cost S O N b f oc pc) ∧ Wrote O oc pc raw new m out := by
  have scr:=room.scratch
  have tmp:=room.temporary
  have mem:=room.memory
  have lo:=room.oldBefore
  have lp:=room.pairsBefore
  have wide : 1<2^w := by omega
  have oldFits := count_fits wide lo
  have pairFits := count_fits wide lp
  have passFit : (guarded N.old (S.old b f)).Fits w O.base := ⟨trivial,oldFits,room.oldFits,trivial⟩
  have run (k : ℕ) (legal : k≤10) : ∃out,(pass S O N b f w oc pc k).Exec m out (passCost S O N b f oc pc k) ∧
      Progress O oc pc k raw new m out := by
    induction k with
    | zero=>
      let oldExpr:=guarded N.old (S.old b f)
      refine ⟨ProtocolRAM.image O.base (oc+10*pc) oldExpr m,scan_exec O.base _ _ m passFit (by omega),?_⟩
      refine ⟨fun _ ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha),?_,fun _ hj=>by omega,?_⟩
      · intro i
        have hi:=i.isLt
        let j : Fin (oc+10*pc):=⟨i.val,by omega⟩
        exact (ProtocolRAMGeneratedWrite.read_image O.base _ oldExpr m j).trans
          ((guarded_read _ _ m i.val oldN (by omega) (by omega) oldRead).trans ((ite_eq_left hi).trans (rawRead i)))
      · intro j past inside
        have read:=ProtocolRAMGeneratedWrite.read_image O.base _ oldExpr m (⟨j,inside⟩:Fin (oc+10*pc))
        exact read.trans ((guarded_read _ _ m j oldN (by omega) (by omega) oldRead).trans (ite_eq_right (by omega)))
    | succ k ih=>
      obtain ⟨prev,exec,state⟩:=ih (by omega)
      let A:=address O N k
      let V:=guarded N.pairs (S.born b (band k) f)
      let ix (i : Fin pc):=O.addr oldN k i.val
      let word:=fillWord (pc:=pc) new (band k)
      let out:=ProtocolRAMGeneratedWrite.image O.dest O.vals A V ix word prev
      have bound (j) (hj:j<10) (i:Fin pc) : O.addr oldN j i.val<O.dest := by
        have:=i.isLt
        unfold addr
        omega
      have small (i : Fin pc) : ix i<O.dest := bound k (by omega) i
      have inject : Function.Injective ix := fun i j h=>Fin.ext (by dsimp [ix,addr] at h;omega)
      have native : (ProtocolRAMGeneratedWrite.program w O.dest O.vals pc A V).Exec prev out
          (ProtocolRAMGeneratedWrite.work pc A V) := by
        apply ProtocolRAMGeneratedWrite.run
        · apply ProtocolRAMGeneratedWrite.fits_mono _ (by omega : O.base≤O.dest)
          exact ⟨⟨trivial,oldFits⟩,by simp [times,Expr.Fits]⟩
        · apply ProtocolRAMGeneratedWrite.fits_mono _ (by omega : O.base≤O.dest)
          exact ⟨trivial,pairFits,room.bornFits _,trivial⟩
        · exact tmp
        · exact mem
        · intro i;exact address_read _ _ k i.val oldN prev ((state.before _ lo).trans oldRead)
        · intro i
          rw [show V.eval prev (i.val:Word w)=(if i.val<pairN then (S.born b (band k) f).eval prev (i.val:Word w) else 0) from
            guarded_read _ _ prev i.val pairN (by have:=i.isLt;omega) (by omega) ((state.before _ lp).trans pairRead)]
          by_cases live : i.val<pairN
          · simp only [ite_eq_left live,word,fillWord,dite_eq_left live]
            exact (eval_below _ _ _ _ (room.bornFits _) state.before).trans (newRead _ ⟨i.val,live⟩)
          · simp [word,fillWord,live]
        · intro i;have:=small i;omega
        · intro i j;have:=small j;omega
        · intro i j;have:=small j;omega
      have unchanged (a) (before : a<O.dest) (away : ∀i,a≠ix i) : out a=prev a :=
        ProtocolRAMGeneratedWrite.frame O.dest O.vals A V ix word prev a away (.inl before) (.inl (by omega))
      refine ⟨out,exec.then native,⟨?_,?_,?_,?_⟩⟩
      · intro a ha
        exact (unchanged a (by omega) (fun _=>by dsimp [ix,addr];omega)).trans (state.before _ ha)
      · intro i
        have hi:=i.isLt
        exact (unchanged _ (by omega) (fun _=>by dsimp [ix,addr];omega)).trans (state.original i)
      · intro j hj i
        let i':Fin pc:=⟨i.val,i.isLt.trans_le pairLe⟩
        rcases Nat.lt_or_eq_of_le (by omega : j≤k) with earlier|rfl
        · exact (unchanged _ (bound j (by omega) i') (fun t=>by dsimp [ix,addr];omega)).trans (state.added _ earlier i)
        · exact (ProtocolRAMGeneratedWrite.read O.dest O.vals A V ix word prev inject i').trans (dite_eq_left i.isLt)
      · intro j past inside
        by_cases hit : ∃i,O.base+j=ix i
        · obtain ⟨i,eqn⟩:=hit
          have dead : ¬i.val<pairN := by dsimp [ix,addr] at eqn;omega
          rw [eqn]
          exact (ProtocolRAMGeneratedWrite.read O.dest O.vals A V ix word prev inject i).trans (dite_eq_right dead)
        · exact (unchanged _ (by omega) (fun i h=>hit ⟨i,h⟩)).trans (state.padding _ past inside)
  obtain ⟨out,exec,wrote⟩:=run 10 le_rfl
  exact ⟨out,exec,wrote.before,wrote.original,fun s i=>by simpa [band_at] using wrote.added _ s.index.isLt i,wrote.padding⟩

end
end Hierarchy.DescentOrdinaryRawRows.Padded

end OAI
