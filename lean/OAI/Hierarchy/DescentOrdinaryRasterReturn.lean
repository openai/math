import OAI.Hierarchy.DescentVenueQuantityState

namespace OAI
/-! # Dense ordinary actor and payment outputs following the reached host numbering -/
namespace Hierarchy.DescentOrdinaryRasterReturn
open DescentDatedAddressBook DescentVenueQuantityPlanes DescentSIMDLookup ProtocolRAM Filter
noncomputable section
variable (d:Dims)
def actor:Dims:={d with precision:=1}
def inverse (base:ℕ):Bank:=⟨base,Nat.clog 2 d.hosts⟩
def first (base:ℕ):=base+2^(Nat.clog 2 d.hosts)
def second (base:ℕ):=State.roof d (first d base)
def roof (base:ℕ):=State.roof (actor d) (second d base)
def paidBank (base x:ℕ):Bank:=⟨State.out d (first d base)+x*(d.hosts*chunks d.groups d.lanes),
  Nat.clog 2 (d.hosts*chunks d.groups d.lanes)⟩
def actorBank (base x:ℕ):Bank:=⟨State.out (actor d) (second d base)+x*(d.hosts*chunks d.groups d.lanes),
  Nat.clog 2 (d.hosts*chunks d.groups d.lanes)⟩

private theorem roof_parts (base : ℕ) :
    roof d base=base+2^(Nat.clog 2 d.hosts)+State.roof d 0+State.roof (actor d) 0 := by
  calc
    roof d base = second d base+State.roof (actor d) 0 := State.shift (actor d) (second d base)
    _ = (first d base+State.roof d 0)+State.roof (actor d) 0 :=
      congrArg (fun n=>n+State.roof (actor d) 0) (State.shift d (first d base))

theorem translated (base : ℕ) : roof d base=base+roof d 0 := by
  simp only [roof_parts,Nat.zero_add,Nat.add_assoc]

theorem after (base : ℕ) : base≤roof d base := by
  rw [translated d base]
  exact Nat.le_add_right ..

variable {ι:ℕ→Type*}
structure ScalarRoom (v:∀h,ι h→Dims):Prop where
  full:State.ScalarRoom v
  existsBit:State.ScalarRoom (fun h i=>actor (v h i))

theorem extent_rate (v:∀h,ι h→Dims)(r:ScalarRoom v):
    Bounded (fun h i=>roof (v h i) 0):=by
  have dims:=State.extent_rate v r.full
  have bits:=State.extent_rate _ r.existsBit
  have prior:=r.full.hosts.padded
  apply ((prior.add dims).add bits).of_le
  intro h i
  change roof (v h i) 0≤2^(Nat.clog 2 (v h i).hosts)+State.roof (v h i) 0+State.roof (actor (v h i)) 0
  exact le_of_eq (by rw [roof_parts,Nat.zero_add])

end
end Hierarchy.DescentOrdinaryRasterReturn

end OAI
