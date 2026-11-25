import OAI.Hierarchy.DescentActorHeaderRAM
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Static addresses and numeric lookup tables for physical actor headers -/
namespace Hierarchy.DescentActorRaster.Headers.Public
open DescentPackedColony.Phase.Arena DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
variable {w : ℕ}

def bank (lo rows : ℕ) : Bank :=⟨lo,Nat.clog 2 rows⟩
def layout (lo H oldDepth maxCount : ℕ) (count depth totals : Bank) : Banks :=
  let start:=bank lo H
  let level:=bank (start.base+start.size) (oldDepth+1)
  let height:=bank (level.base+level.size) (maxCount+1)
  ⟨count,depth,totals,start,level,height⟩
def limit (lo H oldDepth maxCount : ℕ) :=
  let s:=bank lo H
  let d:=bank (lo+s.size) (oldDepth+1)
  d.base+d.size+(bank (d.base+d.size) (maxCount+1)).size
def words (lo H oldDepth maxCount common width w : ℕ) : Image w :=
  let s:=bank lo H
  let d:=bank (lo+s.size) (oldDepth+1)
  ⟨lo,limit lo H oldDepth maxCount,fun x=>
    if x<d.base then ((x-lo)*width:ℕ)
    else if x<d.base+d.size then (x-d.base-common+1:ℕ)
    else (Nat.clog 2 (x-(d.base+d.size))+1:ℕ)⟩

theorem tables (lo H oldDepth maxCount common width : ℕ) (count depth totals : Bank) (m : Memory w)
    (fit : limit lo H oldDepth maxCount<2^w) :
    let C:=layout lo H oldDepth maxCount count depth totals
    let I:=words lo H oldDepth maxCount common width w
    I.program.Exec m (I.output m) (4+10*I.length) ∧
    (∀v : Fin H,I.output m (C.hostStart.base+v.val)=((v.val*width:ℕ):Word w)) ∧
    (∀j,j<C.levels.size→I.output m (C.levels.base+j)=((j-common+1:ℕ):Word w)) ∧
    (∀j,j<C.heights.size→I.output m (C.heights.base+j)=((Nat.clog 2 j+1:ℕ):Word w)) ∧
    (∀x,x<lo ∨ limit lo H oldDepth maxCount≤x→I.output m x=m x) ∧ CheapCode I.program := by
  intro C I
  let p:=bank lo H
  let d:=bank (lo+p.size) (oldDepth+1)
  let s:=bank (d.base+d.size) (maxCount+1)
  have before : lo ≤ limit lo H oldDepth maxCount := by
    change lo ≤ lo+p.size+d.size+s.size
    omega
  have space:I.low+I.length<2^w:=by change lo+(limit lo H oldDepth maxCount-lo)<2^w;omega
  obtain ⟨ran,read,frame⟩:=I.issue m space
  refine ⟨ran,?_,?_,?_,frame,I.hardware.1⟩
  · intro v
    have small:v.val<p.size:=v.isLt.trans_le (Nat.le_pow_clog (by decide) _)
    have eq:d.base=lo+p.size:=rfl
    have rd:=read (lo+v.val) (by change lo≤_;omega) (by change _<d.base+d.size+s.size;omega)
    change I.output m (lo+v.val)=_
    change I.output m _=(if lo+v.val<lo+p.size then _ else _ : Word w) at rd
    simpa [Nat.add_sub_cancel_left,Nat.add_lt_add_left small] using rd
  · intro j hj
    change j<d.size at hj
    have floor:lo≤d.base:=Nat.le_add_right ..
    have read0:=read (d.base+j) (by change lo≤_;omega) (by change _<d.base+d.size+s.size;omega)
    change I.output m (d.base+j)=_
    change I.output m _=(if d.base+j<d.base then _ else if d.base+j<d.base+d.size then _ else _:Word w) at read0
    rw [ite_eq_right (show ¬d.base+j<d.base by omega),ite_eq_left (Nat.add_lt_add_left hj d.base)] at read0
    change I.output m (d.base+j)=((d.base+j-d.base-common+1 : ℕ) : Word w) at read0
    simpa only [Nat.add_sub_cancel_left] using read0
  · intro j hj
    change j<s.size at hj
    have floor:lo≤d.base:=Nat.le_add_right ..
    have read0:=read (d.base+d.size+j) (by change lo≤_;omega) (by change _<d.base+d.size+s.size;omega)
    change I.output m (d.base+d.size+j)=_
    change I.output m _=(if d.base+d.size+j<d.base then _ else if d.base+d.size+j<d.base+d.size then _ else _:Word w) at read0
    rw [ite_eq_right (show ¬d.base+d.size+j<d.base by omega),
      ite_eq_right (show ¬d.base+d.size+j<d.base+d.size by omega)] at read0
    change I.output m (d.base+d.size+j)=((Nat.clog 2 (d.base+d.size+j-(d.base+d.size))+1 : ℕ) : Word w) at read0
    simpa only [Nat.add_sub_cancel_left] using read0
end Hierarchy.DescentActorRaster.Headers.Public

end OAI
