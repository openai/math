import OAI.Hierarchy.DescentOrdinaryRawRows

namespace OAI
/-! # Ten fixed native append passes leave all raw original and new-branch fields at their physical edge rank -/

namespace Hierarchy.DescentOrdinaryRawRows
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentOrdinaryDestRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {w n e : ℕ} (S : Sources) (O : Output) (b : ℕ) (f : Column)

private theorem address_eval (O : Output) (e j : ℕ) (m : Memory w) (i : ℕ) :
    (O.address e j).eval m i=(O.addr e j i:Word w) := by
  change (_:Word w)+(times 10 .row).eval m i=_
  rw [times_eval]
  simp [addr,Expr.eval,Nat.cast_add,Nat.cast_mul]
  ring

def sweep (w n e : ℕ) : ℕ→Procedure w
  | 0=>scan w O.base e (S.old b f)
  | k+1=>(sweep w n e k).seq (ProtocolRAMGeneratedWrite.program w O.dest O.vals n
      (O.address e k) (S.born b (band k) f))
def work (n : ℕ) (e : ℕ) : ℕ→ℕ
  | 0=>4+e*(2*(S.old b f).work+4)
  | k+1=>work n e k+ProtocolRAMGeneratedWrite.work n (O.address e k) (S.born b (band k) f)

structure Bounds (w n e : ℕ) : Prop where
  oldFits : (S.old b f).Fits w O.base
  bornFits : ∀s,(S.born b s f).Fits w O.base
  scratch : O.base+(e+10*n)≤O.dest
  temporary : O.dest+n≤O.vals
  memory : O.vals+n<2^w

variable (raw : Fin e→Word w) (new : Born→Fin n→Word w) (m : Memory w)
def memory : ℕ→Memory w
  | 0=>ProtocolRAM.image O.base e (S.old b f) m
  | k+1=>ProtocolRAMGeneratedWrite.image O.dest O.vals (O.address e k) (S.born b (band k) f)
    (fun i : Fin n=>O.addr e k i.val) (new (band k)) (memory k)

structure Wrote (k : ℕ) (mem : Memory w) : Prop where
  before : ∀a<O.base,mem a=m a
  original : ∀i : Fin e,mem (O.base+i.val)=raw i
  added : ∀j<k,∀i : Fin n,mem (O.addr e j i.val)=new (band j) i

theorem publish (room : Bounds S O b f w n e)
    (oldRead : ∀i : Fin e,(S.old b f).eval m i.val=raw i)
    (bornRead : ∀s i,(S.born b s f).eval m (i:Fin n).val=new s i)
    (k : ℕ) (legal : k≤10) :
    (sweep S O b f w n e k).Exec m (memory (e:=e) S O b f new m k) (work S O b f n e k) ∧
    Wrote O raw new m k (memory (e:=e) S O b f new m k) := by
  induction k with
  | zero=>
    refine ⟨scan_exec O.base e _ m room.oldFits (by have:=room.scratch;have:=room.temporary;have:=room.memory;omega),?_⟩
    exact ⟨fun _ h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h),
      fun i=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ i).trans (oldRead i),fun j hj=>by omega⟩
  | succ k ih=>
    obtain ⟨exec,prior⟩:=ih (by omega)
    let prev:=memory (e:=e) S O b f new m k
    let ix (i : Fin n):=O.addr e k i.val
    have beforeScratch (j) (hj : j<10) (i : Fin n) : O.addr e j i.val<O.dest := by
      have :=room.scratch; have :=i.isLt;unfold addr;omega
    have small (i : Fin n) := beforeScratch k (by omega) i
    have ixInj : Function.Injective ix := fun x y h=>Fin.ext (by dsimp [ix,addr] at h;omega)
    have native : (ProtocolRAMGeneratedWrite.program w O.dest O.vals n (O.address e k) (S.born b (band k) f)).Exec prev
        (memory (e:=e) S O b f new m (k+1)) (ProtocolRAMGeneratedWrite.work n (O.address e k) (S.born b (band k) f)) := by
      apply ProtocolRAMGeneratedWrite.run
      · simp [address,times,Expr.Fits]
      · exact ProtocolRAMGeneratedWrite.fits_mono _ (by have:=room.scratch;omega) (room.bornFits _)
      · exact room.temporary
      · exact room.memory
      · intro i;exact address_eval O e k prev i.val
      · intro i;exact (eval_below _ _ _ _ (room.bornFits _) prior.before).trans (bornRead _ _)
      · intro i;have :=small i;have:=room.temporary;have:=room.memory;omega
      · intro i j;have:=small j;omega
      · intro i j;have:=small j;have:=room.temporary;omega
    refine ⟨Procedure.Exec.then exec native,?_⟩
    have frame (a : ℕ) (h : a<O.dest) (away : ∀i,a≠ix i) : memory (e:=e) S O b f new m (k+1) a=prev a :=
      ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ a away (.inl h) (.inl (by have:=room.temporary;omega))
    refine ⟨fun a ha=>(frame a (by have:=room.scratch;omega) (fun i=>by dsimp [ix,addr];omega)).trans (prior.before a ha),?_,?_⟩
    · intro i
      exact (frame _ (by have:=i.isLt;have:=room.scratch;omega) (fun j=>by have:=i.isLt;dsimp [ix,addr];omega)).trans (prior.original i)
    · intro j hj i
      rcases Nat.lt_or_eq_of_le (by omega : j≤k) with lt|rfl
      · exact (frame _ (beforeScratch _ (by omega) i) (fun t=>by dsimp [ix,addr];omega)).trans (prior.added _ lt i)
      · exact ProtocolRAMGeneratedWrite.read _ _ _ _ _ _ _ ixInj i

theorem read_born {out : Memory w} (done : Wrote O raw new m 10 out) (s : Born) (i : Fin n) :
    out (O.addr e s.index.val i.val)=new s i := by
  simpa [band_at] using done.added _ s.index.isLt i

end
end Hierarchy.DescentOrdinaryRawRows

end OAI
