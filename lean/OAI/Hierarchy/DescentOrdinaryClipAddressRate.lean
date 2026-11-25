import OAI.Hierarchy.DescentOrdinaryVenueClipExtent
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # The original panel, actor and half-table address space for the funded clip -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentPackedColony DescentDatedAddressBook DescentSIMDLookup DescentPacking.PackedMatch.Local Filter
noncomputable section
variable {ι : ℕ→Type*} (c : ∀h,ι h→Clip)

structure AddressInputs : Prop where
  hosts : Bounded (fun h i=>(c h i).venue.hosts)
  groups : Bounded (fun h i=>(c h i).venue.groups)
  paths : Bounded (fun h i=>(c h i).venue.paths)
  header : Bounded (fun h i=>DescentRawCablePanel.DepotRAM.ActorInputs.count (c h i).venue.socket)
  actors : Bounded (fun h i=>(c h i).actorCount)
  panels : Bounded (fun h i=>(c h i).panelPitch)
  inputs : Bounded (fun h i=>(c h i).actorPitch)
  receiving : Bounded (fun h i=>(c h i).working)
  payload : ∃q:ℕ,∀ᶠ h:ℕ in atTop,∀i,(c h i).payload≤q*h

theorem extent_rate_any (a : AddressInputs c)
    (ready : ∀ᶠ h:ℕ in atTop,∀i,let v:=c h i;
      (v.peerBits+1)*v.panelPitch≤v.payload/2 ∧ (v.actorBits+1)*v.actorPitch≤v.payload/2) :
    Bounded (fun h i=>(c h i).fullEnd 0):=by
  have part {M : ∀h,ι h→ℕ} (pitch : Bounded M) : Bounded (fun h i=>Overlap.rows (c h i).venue.hosts (c h i).venue.groups (M h i)) :=
    a.hosts.mul ((a.groups.add pitch).of_le (fun h i=>(Nat.div_le_self _ _).trans (Nat.sub_le ..)))
  obtain ⟨q,hq⟩:=a.payload
  have page:Bounded (fun h i=>2^((c h i).payload/2)):=
    ⟨q,hq.mono (fun h hs i=>Nat.pow_le_pow_right (by decide) ((Nat.div_le_self _ _).trans (hs i)))⟩
  have b : Bounded (fun h i=>(c h i).extentFactor) := by
    have linear := (Bounded.const 64).add ((Bounded.const 24).mul a.paths)
    have quadratic := linear.add (a.paths.pow 2)
    exact (quadratic.add ((Bounded.const 6).mul a.header)).add ((Bounded.const 2).mul a.actors)
  have m : Bounded (fun h i=>(c h i).extentMass):=
    (((((Bounded.const 1).add page).add a.hosts).add (part a.receiving)).add (part a.panels)).add (part a.inputs)
  obtain ⟨e,volume⟩:=b.mul m
  refine ⟨e,?_⟩
  filter_upwards [ready,volume] with h inputs room
  intro i
  obtain ⟨pb,tb⟩:=inputs i
  have size := (c h i).fullEnd_le_any 0 pb tb
  rw [Nat.zero_add] at size
  exact size.trans (room i)

theorem extent_rate (a : AddressInputs c)
    (ready : ∀ᶠ h:ℕ in atTop,∀i,let v:=c h i;0<v.panelPitch ∧ 0<v.actorPitch ∧
      (v.peerBits+1)*v.panelPitch≤v.payload/2 ∧ (v.actorBits+1)*v.actorPitch≤v.payload/2) :
    Bounded (fun h i=>(c h i).fullEnd 0):=
  extent_rate_any c a (ready.mono fun _ atH i => (atH i).2.2)

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI
