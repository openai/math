import Mathlib.Data.Nat.Basic

namespace OAI
/-! The ordinary reference dictionary layout uses only the public dimensions of one date. -/
namespace Hierarchy.DescentOrdinaryRefsROM

structure Chart where
  base : ℕ
  degree : ℕ
  k : ℕ
  oldNodes : ℕ
  newNodes : ℕ
  capacity : ℕ
  bits : ℕ
  nameBits : ℕ
  countBits : ℕ
  lanes : ℕ

namespace Chart
variable (C : Chart)
def donors := (C.degree+1)^4*2^C.k
def nodes := C.donors*(C.oldNodes+C.capacity*6)
def actors := C.donors*(1+C.capacity*6)
def count := (3+C.nodes)*2
/-- The longest binary key among the three compactor tables and the shared node field operator. -/
def keyBits :=
  max (C.nameBits+C.nameBits*C.actors)
    (max (1*C.actors+C.countBits*C.donors) (max (1*C.nodes+C.bits*C.nodes) (C.bits*C.nodes+C.bits)))

def width := C.keyBits*C.lanes
def digitBits := (C.bits*C.oldNodes)*C.lanes
def digitSize := C.oldNodes*2^C.digitBits
def tableBase := C.base+C.digitSize
def tableSize := C.count*2^C.width
def endAddress := C.tableBase+C.tableSize

def withBase (base : ℕ) : Chart := {C with base}
def extent := C.digitSize+C.tableSize

@[simp] theorem withBase_extent (base : ℕ) : (C.withBase base).extent=C.extent:=rfl
theorem end_eq (base : ℕ) : (C.withBase base).endAddress=base+C.extent := Nat.add_assoc ..
theorem extent_rate (h : ℕ) (old : C.digitBits ≤ h/2) (packed : C.keyBits*C.lanes ≤ h/2) :
    C.extent≤(C.oldNodes+C.count)*2^(h/2) := by
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) old))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) packed))

end Chart
end Hierarchy.DescentOrdinaryRefsROM

end OAI
