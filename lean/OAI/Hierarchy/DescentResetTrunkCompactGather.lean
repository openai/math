import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentResetTrunkCompactRows
import OAI.Hierarchy.DescentResetTrunkCompactPointer

namespace OAI
/-! # Sharing a single measured relay pointer across every compact incoming stem -/
namespace Hierarchy.DescentResetTrunkCompactGather
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H P N G M w b : ℕ}

def aliasBank (base H : ℕ) : Bank := ⟨base,Nat.clog 2 H⟩
def geometry (base H : ℕ) := base+span H
def rows (base H G M : ℕ) := DescentResetTrunkCompactRows.rowBase (geometry base H) H G M
def endAddress (base H G M : ℕ) := DescentResetTrunkCompactRows.endAddress (geometry base H) H G M

def phase (w base H P G M : ℕ) (banks : DescentResetTrunkCompactPointer.Banks) : NativePhase w :=
  (DescentResetTrunkCompactPointer.phase w base H P banks).seq
    (DescentResetTrunkCompactRows.phase w (geometry base H) H G M (aliasBank base H))

/-- Each pass still executes the same calendar and preserves all outside words
on an arbitrary incoming configuration. -/
theorem any (base : ℕ) (banks : DescentResetTrunkCompactPointer.Banks) (m : Memory w)
    (space : DescentResetTrunkCompactPointer.Room banks N H P w base)
    (room : endAddress base H G M<2^w) :
    let q:=phase w base H P G M banks
    q.Runs m ∧ ∀a,a<base ∨ endAddress base H G M≤a→q.image m a=m a := by
  intro q
  let mid:=geometry base H
  let p:=DescentResetTrunkCompactPointer.phase w base H P banks
  let r:=DescentResetTrunkCompactRows.phase w mid H G M (aliasBank base H)
  have lo : base≤ mid:=Nat.le_add_right ..
  have high : mid≤endAddress base H G M:=
    (show mid≤rows base H G M from Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have sized : base+H≤ mid:=Nat.add_le_add_left (span_ge H) _
  have one:=DescentResetTrunkCompactPointer.any banks base m space ((sized.trans high).trans_lt room)
  have fit : (aliasBank base H).Fits w mid:=
    ⟨span_pos _,(Nat.le_add_left ..).trans_lt (high.trans_lt room),le_rfl⟩
  have two:=DescentResetTrunkCompactRows.any mid (aliasBank base H) (p.image m) fit room
  refine ⟨NativePhase.seq_runs p r m one.1 two.1,?_⟩
  intro a apart
  exact (two.2 a (apart.imp_left (·.trans_le lo))).trans
    (one.2 a (apart.imp_right (fun h=>sized.trans (high.trans h))))

theorem publish (base : ℕ) (banks : DescentResetTrunkCompactPointer.Banks)
    (name : Fin N→Fin P) (opposite : Fin N→Option (Fin N)) (bounded : N≤H)
    (m : Memory w) (space : DescentResetTrunkCompactPointer.Room banks N H P w base)
    (recorded : DescentResetTrunkCompactPointer.Measured banks name opposite m)
    (room : endAddress base H G M<2^w) :
    let n:=H*chunks G M
    let end_:=endAddress base H G M
    let q:=phase w base H P G M banks
    let ptr:=DescentResetTrunkCompactPointer.pointer bounded opposite
    q.Runs m ∧ (∀a,a<base ∨ end_≤a→q.image m a=m a) ∧
      (∀p : Row H G M,q.image m ((rows base H G M)+(row H G M p).val)=
        ((ptr p.1).elim n (fun v=>(row H G M (v,p.2)).val):Word w)) ∧
      ∀(old : Bank) (values : Fin H→Fin G→Cell b),old.Fits w end_ → old.base+n≤base→n≤old.size→
      Reads old values M m→
      (DescentResetTrunkGather.issue n (rows base H G M) old).Fits w end_ ∧
      Source (DescentResetTrunkGather.issue n (rows base H G M) old)
        (fun h g=>(ptr h).elim 0 (fun t=>values t g)) M (q.image m) := by
  intro n end_ q ptr
  let mid:=geometry base H
  let p:=DescentResetTrunkCompactPointer.phase w base H P banks
  let r:=DescentResetTrunkCompactRows.phase w mid H G M (aliasBank base H)
  have low : base≤ mid:=Nat.le_add_right ..
  have hi : mid≤rows base H G M:=Nat.le_add_right ..
  have boundary : rows base H G M+span n=end_:=rfl
  have upper : mid<2^w:=hi.trans_lt (((Nat.le_add_right ..).trans_eq boundary).trans_lt room)
  have small : base+H≤ mid:=Nat.add_le_add_left (span_ge H) _
  have one:=DescentResetTrunkCompactPointer.run banks name opposite bounded base m space recorded (small.trans_lt upper)
  have fit : (aliasBank base H).Fits w mid:=
    ⟨span_pos _,(Nat.le_add_left ..).trans_lt upper,le_rfl⟩
  have two:=DescentResetTrunkCompactRows.run mid (aliasBank base H) (p.image m) ptr fit (span_ge H) one.2.1 room
  have frame (a : ℕ) (apart : a<base ∨ end_≤a) : q.image m a=m a := by
    have endMono : base+H≤end_:=small.trans (hi.trans ((Nat.le_add_right ..).trans_eq boundary))
    exact (two.2.1 a (apart.imp_left (·.trans_le low))).trans
      (one.2.2 a (apart.imp_right (fun h=>endMono.trans h)))
  refine ⟨NativePhase.seq_runs p r m one.1 two.1,frame,two.2.2,?_⟩
  intro old values oldFit below cap input
  have res : (DescentResetTrunkGather.table (rows base H G M) n).Fits w end_ :=
    ⟨span_pos _,(Nat.le_add_left ..).trans_lt (boundary.trans_lt room),le_of_eq boundary⟩
  apply DescentResetTrunkGather.from_words ptr (rows base H G M) end_ (q.image m) old values oldFit cap res
  · intro ix
    have kept : old.base+(row H G M ix).val<base:=(Nat.add_lt_add_left (row H G M ix).isLt _).trans_le below
    exact (frame _ (.inl kept)).trans (input ix)
  · intro ix
    cases chosen : ptr ix.1 <;>
      simpa only [chosen,Option.elim,q,phase,NativePhase.seq,p,mid,rows,Nat.cast_mul] using two.2.2 ix

theorem run (base : ℕ) (banks : DescentResetTrunkCompactPointer.Banks)
    (name : Fin N→Fin P) (opposite : Fin N→Option (Fin N)) (bounded : N≤H)
    (m : Memory w) (space : DescentResetTrunkCompactPointer.Room banks N H P w base)
    (recorded : DescentResetTrunkCompactPointer.Measured banks name opposite m)
    (room : endAddress base H G M<2^w) :
    let n:=H*chunks G M
    let end_:=endAddress base H G M
    let q:=phase w base H P G M banks
    let ptr:=DescentResetTrunkCompactPointer.pointer bounded opposite
    q.Runs m ∧ (∀a,a<base ∨ end_≤a→q.image m a=m a) ∧
      ∀(old : Bank) (values : Fin H→Fin G→Cell b),old.Fits w end_ → old.base+n≤base→n≤old.size→
      Reads old values M m→
      (DescentResetTrunkGather.issue n (rows base H G M) old).Fits w end_ ∧
      Source (DescentResetTrunkGather.issue n (rows base H G M) old)
        (fun h g=>(ptr h).elim 0 (fun t=>values t g)) M (q.image m) := by
  have done:=publish (G:=G) (M:=M) (b:=b) base banks name opposite bounded m space recorded room
  exact ⟨done.1,done.2.1,done.2.2.2⟩

/-- Later ticket, prefix, or source-position banks may share the original row pointer.
Only its actual numerical words need to survive intervening writes. -/
theorem late_source (base dest : ℕ) (ptr : Fin H→Option (Fin H)) (old : Bank)
    (value : Fin H→Fin G→Cell b) (initial current : Memory w) (room : dest<2^w)
    (early : endAddress base H G M≤dest) (fits : old.Fits w dest) (size : H*chunks G M≤old.size)
    (issued : Reads old value M current)
    (pointers : ∀p : Row H G M,initial (rows base H G M+(row H G M p).val)=
      ((ptr p.1).elim (H*chunks G M) (fun v=>(row H G M (v,p.2)).val):Word w))
    (kept : ∀p : Row H G M,current (rows base H G M+(row H G M p).val)=
      initial (rows base H G M+(row H G M p).val)) :
    (DescentResetTrunkGather.issue (H*chunks G M) (rows base H G M) old).Fits w dest ∧
      Source (DescentResetTrunkGather.issue (H*chunks G M) (rows base H G M) old)
        (fun h g=>(ptr h).elim 0 (fun v=>value v g)) M current := by
  let n:=H*chunks G M
  have lower : (rows base H G M)+span n≤dest:=early
  have tab : (DescentResetTrunkGather.table (rows base H G M) n).Fits w dest :=
    ⟨span_pos _,(Nat.le_add_left ..).trans_lt (lower.trans_lt room),lower⟩
  exact DescentResetTrunkGather.from_words ptr _ dest current old value fits size tab issued
    (fun p=>(kept p).trans (pointers p))

theorem price (w base H P G M : ℕ) (banks : DescentResetTrunkCompactPointer.Banks) :
    let n:=H*chunks G M
    let q:=phase w base H P G M banks
    q.ticks≤42+108*H+124*n ∧ DescentStaticWordColumn.names q.program≤15*(2*H+4*n+4)+350 ∧
      endAddress base H G M≤base+4*H+6*n+5 := by
  intro n q
  let start:=geometry base H
  let a:=aliasBank base H
  have size:=DescentResetStemKeyReindex.size_le H H G M
  have floor:=DescentResetTrunkCompactRows.extent start H G M
  have hp:=span_le H
  change (4+H*(2*(DescentResetTrunkCompactPointer.alternate banks H P).work+4))+
    ((4+10*DescentResetStemKeyReindex.size H H G M)+(4+n*(2*(DescentResetTrunkCompactRows.make start H G M a).work+4)))≤_ ∧ _ ∧ _
  rw [DescentResetTrunkCompactPointer.cost,DescentResetTrunkCompactRows.work]
  refine ⟨by dsimp only [n] at *;omega,?_,?_⟩
  · change DescentStaticWordColumn.names
      ((DescentResetTrunkCompactPointer.phase w base H P banks).program.seq
        (DescentResetTrunkCompactRows.phase w start H G M a).program)≤_
    rw [DescentStaticWordColumn.names_seq]
    change DescentStaticWordColumn.names (scan w base H _)+
      DescentStaticWordColumn.names ((DescentResetStemKeyReindex.phase w start H H G M).program.seq
        (scan w (DescentResetTrunkCompactRows.rowBase start H G M) n _))≤_
    rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan,DescentStaticWordColumn.names_scan,
      DescentResetTrunkCompactPointer.cost,DescentResetTrunkCompactRows.work,DescentResetStemKeyReindex.names]
    dsimp only [n] at *
    omega
  · change DescentResetTrunkCompactRows.endAddress start H G M≤_
    dsimp only [start,geometry,n] at *
    omega

end
end Hierarchy.DescentResetTrunkCompactGather

end OAI
