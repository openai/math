import OAI.Hierarchy.DescentResetDenseOperand

namespace OAI
/-! # Packed common-shape rows and their compact receiver coordinate pages -/
namespace Hierarchy.DescentResetActorClass
open DescentSIMDLookup DescentPackedZip DescentResetDenseOperand

structure Shape where
  rawHosts : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ

namespace Shape
variable (c : Shape)
def parts := chunks c.groups c.lanes
def cells := c.rawHosts*c.parts
def next (base : ℕ) :=base+2^Nat.clog 2 c.cells
def remap (base : ℕ) : Layout:=⟨c.next base,c.hosts,c.rawHosts,c.parts⟩
def endAddress (base : ℕ) := (c.remap base).endAddress
theorem translate (base : ℕ) : c.endAddress base=base+c.endAddress 0:=by
  change (base + 2^Nat.clog 2 c.cells) + (c.remap 0).size =
    base + ((0 + 2^Nat.clog 2 c.cells) + (c.remap 0).size)
  simp only [Nat.zero_add, Nat.add_assoc]

end Shape
end Hierarchy.DescentResetActorClass

end OAI
