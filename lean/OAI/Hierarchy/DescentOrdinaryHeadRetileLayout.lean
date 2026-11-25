import OAI.Hierarchy.DescentOverlapTables

namespace OAI
/-! # Numerical floor for gathering original head columns and resizing their pitch -/
namespace Hierarchy.DescentOrdinaryHeadRetile
open DescentSIMDLookup
noncomputable section

structure Shape where
  n : ℕ
  hosts : ℕ
  groups : ℕ
  before : ℕ
  after : ℕ
  bits : ℕ

namespace Shape
variable (S : Shape)
def oldRows := S.hosts*chunks S.groups S.before
def roleStart (base : ℕ) :=base+S.n*S.oldRows+2^Nat.clog 2 (S.oldRows+1)
def endAddress (base : ℕ) :=
  let rows:=S.hosts*chunks S.groups S.after
  Overlap.dest (S.roleStart base) S.hosts S.groups S.before S.after S.bits+
    S.n*rows+2^Nat.clog 2 (rows+1)

theorem translated (base : ℕ) : S.endAddress base=base+S.endAddress 0 :=by
  simp only [endAddress,roleStart,Overlap.dest,Overlap.dictBase,Nat.zero_add,Nat.add_assoc]

theorem layout (base : ℕ) : base+S.n*S.oldRows≤S.roleStart base ∧ S.roleStart base≤S.endAddress base :=
  ⟨Nat.le_add_right ..,(Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))⟩
theorem base_le (base : ℕ) : base≤S.endAddress base :=(Nat.le_add_right ..).trans ((S.layout base).1.trans (S.layout base).2)

end Shape
end
end Hierarchy.DescentOrdinaryHeadRetile

end OAI
