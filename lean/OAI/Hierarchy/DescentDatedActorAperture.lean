import OAI.Hierarchy.DescentDatedActorSetup
import OAI.Hierarchy.DescentResetActorDirectoryCode
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # The newly measured actor census and its compact inverse precede all receiver reads -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentSIMDLookup ProtocolRAM Filter
noncomputable section
variable (v : ActorSetup)

def directory (base : ℕ) : DescentResetNewActorDirectory.Layout :=
  ⟨v.endAddress base,v.hosts,v.shapes,v.chunksPerHost⟩
def directoryEnd (base : ℕ) :=(v.directory base).endAddress

theorem translated (base : ℕ) : v.directoryEnd base=base+v.directoryEnd 0 := by
  simp only [directoryEnd,directory,DescentResetNewActorDirectory.Layout.endAddress,endAddress,scene,gate,next,bank,
    heights,levels,starts,counts,depths,Bank.size,DescentSharedLeafLookup.Public.stop,
    DescentResetNewActorDirectory.Layout.size,DescentResetNewActorDirectory.Layout.pitch,
    DescentResetNewActorDirectory.Layout.bits,DescentResetNewActorDirectory.Layout.sites,Nat.zero_add,Nat.add_assoc]

structure ScalarRoom {ι : ℕ→Type*} (a : ∀h,ι h→ActorSetup) : Prop where
  hosts : Bounded (fun h i=>(a h i).hosts)
  arity : Bounded (fun h i=>(a h i).arity)
  groups : Bounded (fun h i=>(a h i).groups)
  lanes : Bounded (fun h i=>(a h i).lanes)
  shapes : Bounded (fun h i=>(a h i).shapes)
  width : Bounded (fun h i=>(a h i).oldWidth)
  maxCount : Bounded (fun h i=>(a h i).maxCount)
  tags : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(a h i).headerBits≤C*h
  scene : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(a h i).unitBits*(a h i).lanes≤C*h

theorem rate {ι : ℕ→Type*} (a : ∀h,ι h→ActorSetup) (r : ScalarRoom a) :
    Bounded (fun h i=>(a h i).directoryEnd 0) := by
  let c (i : ℕ):=Bounded.const (ι:=ι) i
  obtain ⟨C,t⟩:=r.tags
  obtain ⟨K,k⟩:=r.scene
  have tags:=Bounded.pow_of_linear (K:=C) t
  have rom:=Bounded.pow_of_linear (K:=K) k
  have batch : Bounded (fun h i=>(a h i).chunksPerHost) :=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=r.hosts.mul batch
  have root:=r.hosts.mul r.shapes
  have h0:=((((r.hosts.padded.add (r.hosts.mul r.arity).padded).add r.hosts.padded).add
    (r.width.add (c 1)).padded).add (r.maxCount.add (c 1)).padded)
  have h1:=(((h0.add (r.shapes.mul r.hosts)).add ((c 2).mul rows.padded)).add
    ((r.lanes.add (c 1)).mul tags).padded)
  have h2:=(h1.add (r.shapes.mul ((c 2).mul rom))).add (r.shapes.mul rows).padded
  have all:=h2.add ((((c 4).mul root.padded).add (c 1)).add ((c 4).mul root))
  apply all.of_le
  intro h i
  simp only [directoryEnd,directory,DescentResetNewActorDirectory.Layout.endAddress,endAddress,scene,gate,next,bank,
    heights,levels,starts,counts,depths,Bank.size,DescentSharedLeafLookup.Public.stop,DescentSharedLeafLookup.Public.stride,
    DescentSharedLeafLookup.Public.words,chunksPerHost,DescentResetNewActorDirectory.Layout.size,DescentResetNewActorDirectory.Layout.pitch,
    DescentResetNewActorDirectory.Layout.bits,DescentResetNewActorDirectory.Layout.sites,Nat.zero_add,Nat.le_refl]

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
