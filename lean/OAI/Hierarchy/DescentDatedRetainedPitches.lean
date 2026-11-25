import OAI.Hierarchy.DescentDatedRetainedSetupRate
import OAI.Hierarchy.DescentRetainedControlLayout
import OAI.Hierarchy.DescentPackedWalshPrice

namespace OAI
/-! # Both genuine pitches of the retained GL and its selected donor stripe -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentDatedAddressBook DescentPackedWalsh Filter
noncomputable section
variable (v : DescentResetRetainedSetup.Layout)

/-- The original cut, the frozen block index and the local register unit determine
all four lane pitches used by the matrix program. -/
structure CalendarPitch (c k h unit : ℕ) : Prop where
  high : v.high=c-laneBits c h unit
  low : v.low=laneBits c h unit+k
  cut : v.cut=c
  blocks : v.blocks=2^k
  gather : v.gatherLanes=2^(laneBits c h unit)
  decoded : v.decodedLanes=v.gatherLanes
  emit : v.emitLanes=v.gatherLanes

theorem CalendarPitch.geometry {c k h u : ℕ} (g : v.CalendarPitch c k h u) :
    v.high+v.low=c+k ∧ v.donors=v.blocks ∧ 2^v.low=v.gatherLanes*v.blocks ∧
    v.matrixLanes=v.gatherLanes ∧ v.gatherLanes≤v.grouped ∧ 2^v.high≤v.grouped :=by
  let e:=laneBits c h u
  have low : e≤c:=Nat.min_le_left ..
  have dim : v.high+v.low=c+k:=by rw [g.high,g.low];change c-e+(e+k)=_;omega
  have ds : v.donors=v.blocks:=by simp only [donors,dim,g.cut,g.blocks,Nat.add_sub_cancel_left]
  have strip : 2^v.low=v.gatherLanes*v.blocks:=by rw [g.low,g.gather,g.blocks,pow_add]
  have populated : 0<v.blocks:=by rw [g.blocks];exact Nat.two_pow_pos _
  exact ⟨dim,ds,strip,by rw [matrixLanes,ds,strip,Nat.mul_div_cancel _ populated],
    by rw [g.gather,grouped,g.cut];exact Nat.pow_le_pow_right (by decide) low,
    by rw [g.high,grouped,g.cut];exact Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)⟩

def lookupUnit :=max v.wholeWord (max (v.bits*v.blocks+v.bits)
  (max (v.siteWord+v.stripWord) (v.stripWord+v.donors*Nat.clog 2 (v.donors+1))))

theorem CalendarPitch.words {c k h u : ℕ} (g : v.CalendarPitch c k h u)
    (pos : 0<u) (bought : 8*u≤h) (upper : v.lookupUnit≤u) :
    v.wholeWord*v.gatherLanes≤h/2 ∧ (v.bits*v.blocks+v.bits)*v.gatherLanes≤h/2 ∧
    (v.bits+v.bits)*2^v.low≤h/2 ∧ v.stripWord*v.matrixLanes≤h/2 ∧
    (v.siteWord+v.stripWord)*v.decodedLanes≤h/2 ∧ v.bits*v.decodedLanes≤h/2 ∧
    (v.stripWord+v.donors*Nat.clog 2 (v.donors+1))*v.decodedLanes≤h/2 :=by
  have keys:=keys_fit (m:=c) pos bought
  change 1+(u+u)*2^(laneBits c h u)≤h/2 at keys
  rw [←g.gather,Nat.add_mul] at keys
  have shape:=CalendarPitch.geometry v g
  have used {a : ℕ} (small : a≤u) : a*v.gatherLanes≤h/2 :=
    (Nat.mul_le_mul_right _ small).trans (by omega)
  rcases max_le_iff.mp upper with ⟨a,rest⟩
  rcases max_le_iff.mp rest with ⟨b,rest⟩
  rcases max_le_iff.mp rest with ⟨s,r⟩
  have bits : v.bits*v.blocks≤u:=(Nat.le_add_right ..).trans b
  have twice :=Nat.mul_le_mul_right v.gatherLanes bits
  rw [g.decoded,shape.2.2.2.1,shape.2.2.1]
  refine ⟨used a,used b,?_,used ((Nat.le_add_left ..).trans s),used s,
    used ((Nat.le_add_left ..).trans b),used r⟩
  have rewrite_ : (v.bits+v.bits)*(v.gatherLanes*v.blocks)=
      (v.bits*v.blocks)*v.gatherLanes+(v.bits*v.blocks)*v.gatherLanes:=by ring
  omega

variable {ι : ℕ→Type*} (p : ∀h,ι h→DescentResetRetainedSetup.Layout) (c k u : ∀h,ι h→ℕ)
theorem calendar_room_of_matrix (geometry : ∀h i,(p h i).CalendarPitch (c h i) (k h i) h (u h i))
    (hosts : Bounded (fun h i=>(p h i).hosts)) (groups : Bounded (fun h i=>(p h i).groups))
    (blocks : Bounded (fun h i=>(p h i).blocks)) (nodes : Bounded (fun h i=>(p h i).nodes))
    (args : Bounded (fun h i=>(p h i).args)) (previousNodes : Bounded (fun h i=>(p h i).previousNodes))
    (previousArgs : Bounded (fun h i=>(p h i).previousArgs))
    (prior : Bounded (fun h i=>(p h i).previousLanes)) (grouped : Bounded (fun h i=>(p h i).grouped))
    (priorWords : ∀ᶠ h:ℕ in atTop,∀i,(p h i).wholeWord*(p h i).previousLanes≤h/2)
    (dim : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(c h i+k h i)*(c h i+k h i)≤K*h)
    (selected : ∀ᶠ h:ℕ in atTop,∀i,0<u h i ∧ 8*(u h i)≤h ∧ (p h i).lookupUnit≤u h i) :
    ScalarRoom p :=by
  obtain ⟨K,dim⟩:=dim
  have geom:=fun h i=>CalendarPitch.geometry (p h i) (geometry h i)
  have gather:=grouped.of_le (fun h i=>(geom h i).2.2.2.2.1)
  refine ⟨hosts,groups,blocks,previousNodes,previousArgs,nodes,args,prior,gather,
    gather.of_le (fun h i=>(geometry h i).decoded.le),gather.of_le (fun h i=>(geometry h i).emit.le),
    grouped.of_le (fun h i=>(geom h i).2.2.2.2.2),
    (gather.mul blocks).of_le (fun h i=>(geom h i).2.2.1.le),grouped,K+1,?_⟩
  filter_upwards [priorWords,dim,selected] with h prev dimensions choose
  intro i
  rcases choose i with ⟨pos,fit,main⟩
  have ⟨a,b,d,e,f,g,_⟩:=CalendarPitch.words (p h i) (geometry h i) pos fit main
  have matrix:=dimensions i
  rw [←(geom h i).1] at matrix
  have small : h ≤ (K+1)*h := by rw [Nat.add_mul,Nat.one_mul]; omega
  have half := (Nat.div_le_self h 2).trans small
  have large : K*h ≤ (K+1)*h := by rw [Nat.add_mul]; exact Nat.le_add_right ..
  exact ⟨(prev i).trans half,a.trans half,
    b.trans half,d.trans half,matrix.trans large,
    e.trans half,f.trans half,g.trans half⟩

theorem calendar_room (geometry : ∀h i,(p h i).CalendarPitch (c h i) (k h i) h (u h i))
    (hosts : Bounded (fun h i=>(p h i).hosts)) (groups : Bounded (fun h i=>(p h i).groups))
    (blocks : Bounded (fun h i=>(p h i).blocks)) (nodes : Bounded (fun h i=>(p h i).nodes))
    (args : Bounded (fun h i=>(p h i).args)) (previousNodes : Bounded (fun h i=>(p h i).previousNodes))
    (previousArgs : Bounded (fun h i=>(p h i).previousArgs))
    (prior : Bounded (fun h i=>(p h i).previousLanes)) (grouped : Bounded (fun h i=>(p h i).grouped))
    (priorWords : ∀ᶠ h:ℕ in atTop,∀i,(p h i).wholeWord*(p h i).previousLanes≤h/2)
    (dim : ∀ᶠ h:ℕ in atTop,∀i,(c h i+k h i)*(c h i+k h i)≤h/2)
    (selected : ∀ᶠ h:ℕ in atTop,∀i,0<u h i ∧ 8*(u h i)≤h ∧ (p h i).lookupUnit≤u h i) :
    ScalarRoom p :=by
  exact calendar_room_of_matrix p c k u geometry hosts groups blocks nodes args previousNodes previousArgs
    prior grouped priorWords ⟨1,dim.mono fun h q i=>by rw [Nat.one_mul];exact (q i).trans (Nat.div_le_self ..)⟩ selected

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
