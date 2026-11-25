import OAI.Hierarchy.DescentResetRetainedPlacementChart

namespace OAI
/-! # Address diagram for shape-specific retained reset quantities -/
namespace Hierarchy.DescentRetainedTargetPlacement.Chart
open DescentResetRetainedPlacement ProtocolRAM
noncomputable section
variable (v : DescentResetRetainedPlacement.Chart) (b : Batch)
def expanded : Batch := { b with fields:=b.fields*v.shapes }
def oldRows := v.oldHosts*v.parts
def aperture := (v.shapes+1)*v.blocks*oldRows v
def guard := DescentResetRetainedPlacement.Chart.rounded (aperture v)
def route (floor : ℕ) : Bank :=
  ⟨v.projected (expanded v b) floor+2*guard v,Nat.clog 2 (v.sparse*v.parts+1)⟩
def directory (floor : ℕ) := (route v b floor).base+(route v b floor).size
def samples (floor : ℕ) := directory v b floor+(2*2^Nat.clog 2 v.rows+2^Nat.clog 2 v.sparse)
def bank (floor : ℕ) (f : Fin b.fields) (x : Fin v.blocks) : Bank :=
  ⟨samples v b floor+(finProdFinEquiv (f,x)).val*v.rows,Nat.clog 2 (v.rows+1)⟩
def endAddress (floor : ℕ) :=
  samples v b floor+(b.fields*v.blocks)*v.rows+DescentResetRetainedPlacement.Chart.rounded v.rows

theorem affine (floor : ℕ) : endAddress v b floor=floor+endAddress v b 0:=by
  simp only [endAddress,samples,directory,route,Bank.size,v.projected_affine (expanded v b) floor,
    Nat.add_assoc]

end
end Hierarchy.DescentRetainedTargetPlacement.Chart

end OAI
