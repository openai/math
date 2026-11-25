import OAI.Hierarchy.DescentPrimitivePalettePrintedBits
import OAI.Hierarchy.DescentSeedTokenNumbers

namespace OAI
/-! # The physical pitch of the initial global original-role pages -/
namespace Hierarchy.DescentDatedSeedStartup.Primitive
open DescentSixParty DescentSIMDLookup DescentPrimitivePalette
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec) (s Z payload k : ℕ)

def paletteLanes := lanes payload (4*max (DescentPackedSeed.Primitive.roleBits s*2^k) (printedBits D s Z op))

private theorem field_half {field : ℕ}
    (fit : field ≤ max (DescentPackedSeed.Primitive.roleBits s*2^k) (printedBits D s Z op)) :
    field*paletteLanes D op s Z payload k ≤ payload/2 :=by
  let unit:=max (DescentPackedSeed.Primitive.roleBits s*2^k) (printedBits D s Z op)
  have within : field ≤ 4*unit := fit.trans (show unit ≤ 4*unit by omega)
  calc
    _ ≤ (4*unit)*paletteLanes D op s Z payload k := Nat.mul_le_mul_right _ within
    _ = paletteLanes D op s Z payload k*(4*unit) := Nat.mul_comm ..
    _ ≤ payload/2 := lanes_fit payload (4*unit)

theorem chosen_printed_half :
    printedBits D s Z op*paletteLanes D op s Z payload k ≤ payload/2 :=
  field_half D op s Z payload k (Nat.le_max_right ..)

theorem chosen_roles_half :
    (DescentPackedSeed.Primitive.roleBits s*2^k)*paletteLanes D op s Z payload k ≤ payload/2 :=
  field_half D op s Z payload k (Nat.le_max_left ..)

end Hierarchy.DescentDatedSeedStartup.Primitive

end OAI
