import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentTerminalSliceShelf
import OAI.Hierarchy.DescentExteriorHopSnapshots

namespace OAI
/-! # A fixed address exponent for the literal last projection, replay and control directory -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentDatedAddressBook DescentTerminalSliceShelf DescentExteriorReplay
open DescentTerminalPointerFrame Filter
noncomputable section

/-- The primitive quantities in the three actual address increments. -/
structure ReplayUsage where
  start : ℕ
  slots : ℕ
  width : ℕ
  blocks : ℕ
  hosts : ℕ
  dates : ℕ
  cohorts : ℕ
  packets : ℕ
  controls : ℕ
  paid : ℕ
  scratch : ℕ

def ReplayUsage.slice (z:ReplayUsage) :=
  fence z.start (2+3*z.slots) z.width (z.blocks*z.hosts)
def ReplayUsage.fresh (z:ReplayUsage) :=z.scratch+(z.dates+1)*DescentExteriorReplay.Snapshots.stride z.cohorts
def ReplayUsage.sources (z:ReplayUsage) :=z.fresh+pad z.packets+pad z.packets+
  (pad z.controls+pad z.paid+(z.paid+1))

/-- Each clause is either a previous address, a physically attained population,
or the scratch bound of the original hop program. -/
structure ReplayUsage.Room (z:ReplayUsage) (h C:ℕ) : Prop where
  start : z.start≤2^(C*h)
  blocks : z.blocks≤2^(C*h)
  hosts : z.hosts≤2^(C*h)
  dates : z.dates≤2^(C*h)
  cohorts : z.cohorts≤2^(C*h)
  packets : z.packets≤2^(C*h)
  controls : z.controls≤2^(C*h)
  paid : z.paid≤2^(C*h)
  lookup : DescentTerminalPointerFrame.size (2+3*z.slots) z.width≤2*2^(h/2)
  literal : z.scratch≤z.slice+2*z.hosts+3*2^(h/2)

theorem uniform_replay_space (C:ℕ) :
    ∃K,∀ᶠ h:ℕ in atTop,∀z:ReplayUsage,z.Room h C→z.sources≤2^(K*h) :=by
  let I (h:ℕ):={z:ReplayUsage // z.Room h C}
  let z (h:ℕ) (i:I h):=i.val
  let rows (h:ℕ) (i:I h):=(z h i).blocks*(z h i).hosts
  let l (h:ℕ) (i:I h):=2+3*(z h i).slots
  let cells (h:ℕ) (i:I h):=DescentTerminalPointerFrame.size (l h i) (z h i).width
  have rr (x:∀h,I h→ℕ) (b:∀h i,x h i≤2^(C*h)) : Bounded x :=
    ⟨C,Eventually.of_forall b⟩
  have half : Bounded (fun h (_:I h)=>2^(h/2)) :=
    Bounded.pow_of_linear (K:=1) (Eventually.of_forall fun h _=>by simpa only [one_mul] using Nat.div_le_self h 2)
  let c (n:ℕ):=Bounded.const (ι:=I) n
  have slots : Bounded cells:=((c 2).mul half).of_le fun h i=>i.property.lookup
  have lanes : Bounded l:=slots.of_le fun h i=>by
    change _≤l h i*2^(z h i).width+_
    exact (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans (Nat.le_add_right ..)
  have hosts:=rr (fun h i=>(z h i).hosts) (fun h i=>i.property.hosts)
  have heights : Bounded rows :=(rr _ (fun h (i:I h)=>i.property.blocks)).mul hosts
  have early:=rr (fun h i=>(z h i).start) (fun h i=>i.property.start)
  have tables : Bounded (fun h i=>(z h i).slice) :=
    ((early.add (lanes.mul heights)).add heights.padded).add ((c 6).mul (slots.add heights.padded))
  have scratch : Bounded (fun h i=>(z h i).scratch) :=
    ((tables.add ((c 2).mul hosts)).add ((c 3).mul half)).of_le fun h i=>i.property.literal
  have dates:=rr (fun h i=>(z h i).dates) (fun h i=>i.property.dates)
  have history:=rr (fun h i=>(z h i).cohorts) (fun h i=>i.property.cohorts)
  have fresh : Bounded (fun h i=>(z h i).fresh) :=scratch.add ((dates.add (c 1)).mul (history.add (c 1)).padded)
  have packets:=rr (fun h i=>(z h i).packets) (fun h i=>i.property.packets)
  have controls:=rr (fun h i=>(z h i).controls) (fun h i=>i.property.controls)
  have paid:=rr (fun h i=>(z h i).paid) (fun h i=>i.property.paid)
  have total : Bounded (fun h i=>(z h i).sources) :=
    ((fresh.add packets.padded).add packets.padded).add ((controls.padded.add paid.padded).add (paid.add (c 1)))
  obtain ⟨K,bound⟩:=total
  exact ⟨K,bound.mono fun h chosen z room=>chosen ⟨z,room⟩⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
