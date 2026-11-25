import OAI.Hierarchy.DescentOrdinaryClipAddressRate
import OAI.Hierarchy.DescentOrdinaryPriorRetileRate
import OAI.Hierarchy.DescentDatedRoleControlRate
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentOperandSourceAddressPieces

namespace OAI
/-! The populated clip, both retiles, acquired chip and census have an address bound
on one registered date; the two input rectangles can have different host counts. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentRawCablePanel DescentOrdinaryAtomFieldRAM
open DescentDatedPriorOperand DescentOrdinaryVenueIngress Filter
noncomputable section
set_option quotPrecheck false
variable {ι : ℕ→Type*} {F : Type} [Field F] {Pin : ∀h,ι h→Type}
    (v : ∀h (i : ι h),PhysicalOrdinary F (Pin h i)) (prior : ∀h,ι h→DatePorts) (floor : ∀h,ι h→ℕ)
local notation "W_" => fun h i=>(v h i).registeredFrom (prior h i) (floor h i)
local notation "A_" => fun h i=>(v h i).registeredEntry (prior h i) (floor h i)
local notation "C_" => fun h i=>((A_) h i).clip
local notation "old_" => fun h i=>((A_) h i).previous
local notation "role_" => fun h i=>((A_) h i).roleLayout ((W_) h i)
local notation "chip_" => fun h i=>((A_) h i).chip ((W_) h i)
local notation "pop_" => fun h i=>{((A_) h i).population ((W_) h i) 0 with base:=0}

structure EntryAddressInputs : Prop where
  previous : Layout.ScalarRoom old_
  clip : Clip.AddressInputs C_
  actual : ∀ᶠ h:ℕ in atTop,∀i,let c:=(C_) h i;
    (c.peerBits+1)*c.panelPitch≤c.payload/2 ∧ (c.actorBits+1)*c.actorPitch≤c.payload/2
  rolePitch : Bounded (fun h i=>(prior h i).roleLanes)
  roleKey : Linear (fun h i=>((role_) h i).bits*((role_) h i).beforeLanes)
  chipKey : Linear (fun h i=>DepotRAM.totalBits ((chip_) h i).format*((chip_) h i).lanes)
  sites : Bounded (fun h i=>((W_) h i).vector.lows)
  populationKeys : ∃q:ℕ,∀ᶠ h in atTop,∀i,let p:=(pop_) h i;
    (p.roleBits*p.nodes)*p.lanes≤q*h ∧ (p.countBits*p.donors+p.countBits)*p.lanes≤q*h

theorem registered_entry_address (inputs : EntryAddressInputs v prior floor) :
    Bounded (fun h i=>((W_) h i).ingressWords) :=by
  let cst:=fun n=>Bounded.const (ι:=ι) n
  have clip:=Clip.extent_rate_any C_ inputs.clip inputs.actual
  have current:=inputs.clip.hosts.mul (inputs.clip.groups.chunks inputs.clip.receiving)
  have prev:=DescentOrdinaryPriorRetile.prior_aperture old_ (fun h i=>((C_) h i).working)
    (fun _ _=>0) inputs.previous inputs.clip.receiving (cst 0)
  have pages:=((cst 7).mul inputs.previous.arities).mul inputs.previous.blocks
  have paddedRows:=inputs.clip.hosts.mul (inputs.previous.groups.chunks inputs.clip.receiving)
  have prevPad:= (prev.add ((pages.add (cst 1)).mul paddedRows)).add ((paddedRows.add (cst 1)).padded)
  have roles:=DescentOrdinaryRoleRetile.Layout.address_bound (fun h i=>((role_) h i).retile) (fun _ _=>0)
    inputs.previous.hosts inputs.clip.groups inputs.rolePitch inputs.clip.receiving
    inputs.previous.blocks (cst 0) inputs.roleKey
  have rolePad:= (roles.add ((inputs.previous.blocks.add (cst 1)).mul current)).add ((current.add (cst 1)).padded)
  have chip:=(((cst 0).add inputs.chipKey.table).add current.padded).add ((current.add (cst 1)).padded)
  have pop:=RoleControl.Layout.bounded_end pop_ ⟨inputs.clip.hosts,inputs.clip.groups,inputs.clip.receiving,
    inputs.clip.paths.mul inputs.previous.blocks,inputs.sites,inputs.populationKeys⟩ (cst 0)
  exact ((((clip.add prevPad).add rolePad).add chip).add pop)
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
