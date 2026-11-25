import OAI.Hierarchy.DescentResetTrunkPhases

namespace OAI
/-! # Numeric read bounds for the three geometric trunk descriptors -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
noncomputable section
def scalarBank (base n i : ℕ) : Bank:=⟨base+i*n,Nat.clog 2 n⟩

def rawTrunkExpr (field gran neighbors palette : ℕ) :=
  DescentResetTrunkScalar.header field gran (fun j=>.lookup (scalarBank neighbors gran j.val) .row)
    (.lookup (scalarBank palette gran 0) .row) (.lookup (scalarBank palette gran 1) .row)
    (.lookup (scalarBank palette gran 2) .row)

theorem raw_trunk_work (field gran neighbors palette : ℕ) :
    (rawTrunkExpr field gran neighbors palette).work=DescentResetTrunkScalar.tableWork :=
  DescentResetTrunkScalar.table_work field gran (fun j=>scalarBank neighbors gran j.val)
    (scalarBank palette gran 0) (scalarBank palette gran 1) (scalarBank palette gran 2)

/-- The third dyadic bank may contain addresses after the last scalar written
by the three contiguous arrays. This accounts for that padding once. -/
theorem scalar_bank_room {N w base out : ℕ} (after : base+2*N+span N≤out)
    (word : out<2^w) (j : Fin 3) : (scalarBank base N j.val).Fits w out:=by
  have fit : j.val*N≤2*N:=Nat.mul_le_mul_right N (by have step:=j.isLt;omega)
  have room : base+j.val*N+span N≤out:=by omega
  exact ⟨span_pos _,(Nat.le_add_left ..).trans_lt (room.trans_lt word),room⟩

theorem raw_trunk_fits {field N w peers palette out : ℕ}
    (old : peers+2*N+span N≤out) (tables : palette+2*N+span N≤out) (word : out<2^w) :
    (rawTrunkExpr field N peers palette).Fits w out:=
  DescentResetTrunkScalar.fits _ _ _ _ (fun j=>⟨scalar_bank_room old word j,trivial⟩)
    ⟨scalar_bank_room tables word 0,trivial⟩ ⟨scalar_bank_room tables word 1,trivial⟩
    ⟨scalar_bank_room tables word 2,trivial⟩
end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
