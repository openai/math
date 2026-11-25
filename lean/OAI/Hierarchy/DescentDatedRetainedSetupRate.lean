import OAI.Hierarchy.DescentResetRetainedChart
import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
/-! # Address room for the observed GL transfer of old seven-field operand panels -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentDatedAddressBook DescentSIMDLookup DescentGLPacked.BankImage DescentGLControlCode Filter
noncomputable section
variable {ι : ℕ→Type*} (p : ∀h,ι h→Layout)

structure ScalarRoom : Prop where
  hosts : Bounded (fun h i=>(p h i).hosts)
  groups : Bounded (fun h i=>(p h i).groups)
  blocks : Bounded (fun h i=>(p h i).blocks)
  oldNodes : Bounded (fun h i=>(p h i).previousNodes)
  oldArgs : Bounded (fun h i=>(p h i).previousArgs)
  nodes : Bounded (fun h i=>(p h i).nodes)
  args : Bounded (fun h i=>(p h i).args)
  priorLanes : Bounded (fun h i=>(p h i).previousLanes)
  gatherLanes : Bounded (fun h i=>(p h i).gatherLanes)
  decodedLanes : Bounded (fun h i=>(p h i).decodedLanes)
  emitLanes : Bounded (fun h i=>(p h i).emitLanes)
  high : Bounded (fun h i=>2^(p h i).high)
  low : Bounded (fun h i=>2^(p h i).low)
  grouped : Bounded (fun h i=>(p h i).grouped)
  packed : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;
    v.wholeWord*v.previousLanes≤K*h ∧ v.wholeWord*v.gatherLanes≤K*h ∧
    (v.bits*v.blocks+v.bits)*v.gatherLanes≤K*h ∧ (v.bits+v.bits)*2^v.low≤K*h ∧
    (v.high+v.low)*(v.high+v.low)≤K*h ∧ v.stripWord*v.matrixLanes≤K*h ∧
    (v.siteWord+v.stripWord)*v.decodedLanes≤K*h ∧ v.bits*v.decodedLanes≤K*h

theorem extent_rate (r : ScalarRoom p) : Bounded (fun h i=>(p h i).endAddress 0) :=by
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  let dim:=fun h (i:ι h)=>(p h i).high+(p h i).low
  let fat:=fun h (i:ι h)=>max (((p h i).bits+(p h i).bits)*2^(p h i).low) (dim h i*dim h i)
  have dims : Bounded dim :=(r.high.of_le fun _ _=>Nat.lt_two_pow_self.le).add
    (r.low.of_le fun _ _=>Nat.lt_two_pow_self.le)
  have fieldCount:=(c 2).add ((c 7).mul r.oldArgs)
  have sources:=fieldCount.mul r.blocks
  have channels:=fieldCount.mul r.oldNodes
  have outputs:=((((c (2*7)).mul r.args).mul r.nodes).add r.nodes)
  have matrixLanes : Bounded (fun h i=>(p h i).matrixLanes):=r.low.of_le fun _ _=>Nat.div_le_self ..
  obtain ⟨K,hk⟩:=r.packed
  have initial:=Overlap.address_rate r.hosts r.groups r.priorLanes r.gatherLanes
    ⟨K,hk.mono fun h q i=>(q i).1⟩
  have slotPage:=Bounded.pow_of_linear (K:=K) (hk.mono fun h q i=>(q i).2.1)
  have matPage:=Bounded.pow_of_linear (K:=K) (hk.mono fun h q i=>(q i).2.2.1)
  have matrix : Bounded (fun h i=>(p h i).matrix 0) :=by
    simpa only [Layout.matrix, slots, digits, Layout.sources, Layout.fields, firstStep, counts, Nat.zero_add] using
      (((sources.mul initial).add (r.oldNodes.mul slotPage)).add (r.blocks.mul ((c 2).mul matPage)))
  have root : Bounded (fun h i=>2^(fat h i)) :=Bounded.pow_of_linear (K:=K)
    (hk.mono fun h q i=>max_le (q i).2.2.2.1 (q i).2.2.2.2.1)
  have n : Bounded (fun h i=>Count (dim h i)) :=
    (((c 3).mul dims).mul dims).of_le fun _ _=>DescentGLNielsen.length_le _
  have rows:=(channels.mul r.hosts).mul r.high
  have setup:=(c 4).mul (((((c 1).add n).mul root).add n).add (dims.mul r.high) |>.add (c 1))
  have two:=(c 2).mul (rows.add (c 1))
  have gl : Bounded (fun h i=>(p h i).mixed 0) :=by
    apply ((((matrix.add setup).add two).add n).add ((((c 7).mul n).add (c 1)).mul (two.add root))).of_le
    intro h i
    let v:=p h i
    let m:=fat h i
    have split : (m+m)/2=m:=by omega
    have packed : (v.bits+v.bits)*2^v.low≤(m+m)/2:=by rw [split];exact le_max_left ..
    have sq : (v.high+v.low)*(v.high+v.low)≤(m+m)/2:=by rw [split];exact le_max_right ..
    simpa only [mixed, SignedFields.stop, Layout.channels, Layout.fields, v, split, m, dim] using Dated.paid_extent (v.matrix 0) (v.channels*v.hosts) v.high v.low v.bits (m+m) packed sq
  have next:=Overlap.address_rate r.hosts r.grouped matrixLanes r.decodedLanes ⟨K,hk.mono fun h q i=>(q i).2.2.2.2.2.1⟩
  have joint:=Bounded.pow_of_linear (K:=K) (hk.mono fun h q i=>(q i).2.2.2.2.2.2.1)
  have projected : Bounded (fun h i=>2^((p h i).siteWord*(p h i).decodedLanes)) :=by
    apply joint.of_le
    intro h i
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have final:=Overlap.address_rate r.hosts r.grouped r.decodedLanes r.emitLanes ⟨K,hk.mono fun h q i=>(q i).2.2.2.2.2.2.2⟩
  have physical : Bounded (fun h i=>(p h i).rows) :=r.hosts.mul
    ((r.grouped.add r.decodedLanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have tables:=gl.add (channels.mul next)
  have decode:=tables.add ((channels.add (c 1)).mul joint)
  have out:=decode.add (outputs.mul projected)
  exact (((out.add (outputs.mul physical)).add (physical.add (c 1)).padded).add (outputs.mul final))

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
