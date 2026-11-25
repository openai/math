import OAI.Hierarchy.DescentRetainedTargetPlacementChart
import OAI.Hierarchy.DescentResetRetainedPlacement

namespace OAI
/-! # One indirect lookup selects the genuine shape-specific primary at each compact actor -/
namespace Hierarchy.DescentRetainedTargetPlacement.Chart
open DescentResetRetainedPlacement DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {w : ℕ} (v : DescentResetRetainedPlacement.Chart) (b : Batch)

def literal (keep : Fin v.shapes→Bool) (j : ℕ) : ℕ :=
  if ok:j<v.sparse*v.parts then
    let pair : Fin v.sparse×Fin v.parts:=finProdFinEquiv.symm ⟨j,ok⟩
    if keep (v.shape pair.1) then
      (v.shape pair.1).val*(v.blocks*oldRows v)+(finProdFinEquiv (v.previous pair.1,pair.2)).val+1
    else 0
  else 0

def dir (floor : ℕ) : DescentResetDenseOperand.Layout:=⟨directory v b floor,v.newHosts,v.sparse,v.parts⟩
def slab (floor : ℕ) (f : Fin b.fields) (x : Fin v.blocks) : Bank :=
  let out:=DescentResetStemProject.out floor (b.fields*v.shapes) v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes
  ⟨out+f.val*(v.shapes*v.blocks*oldRows v)+x.val*oldRows v,Nat.clog 2 (aperture v+1)⟩

theorem slab_address (floor : ℕ) (f : Fin b.fields) (t : Fin v.shapes) (x : Fin v.blocks) (j : ℕ) :
    (slab v b floor f x).base+(t.val*(v.blocks*oldRows v)+j)=
      (v.projectedBank (expanded v b) floor (finProdFinEquiv (f,t)) x).base+j:=by
  simp only [slab,DescentResetRetainedPlacement.Chart.projectedBank,DescentResetStemProject.bank,
    DescentResetStemProject.page,DescentVectorBookReshape.blockBank,DescentScalarBookReshape.dest,
    DescentVectorBookReshape.destBase,DescentVectorBookReshape.rows,Nat.mul_one,oldRows,
    DescentResetRetainedPlacement.Chart.parts,expanded]
  change _=(_+(t.val+v.shapes*f.val)*(v.blocks*(v.oldHosts*chunks v.groups v.lanes))+
    x.val*(v.oldHosts*chunks v.groups v.lanes))+j
  ring

def sparseExpr (floor : ℕ) (f : Fin b.fields) (x : Fin v.blocks) : Expr :=
  let a:=Expr.lookup (route v b floor) .row
  .branch .eq a (.lit 0) (.lit 0) (.lookup (slab v b floor f x) (.op .sub a (.lit 1)))

def term (floor : ℕ) (cnt inv : Bank) (j : Fin (b.fields*v.blocks)) : Expr :=
  let z:=finProdFinEquiv.symm j
  (dir v b floor).load cnt inv (sparseExpr v b floor z.1 z.2)

def program (floor w : ℕ) (keep : Fin v.shapes→Bool) (src : Fin (b.fields*v.shapes)→Expr) (cnt inv : Bank) :=
  (((v.projectedCode (expanded v b) floor w src).seq (DescentStaticWordColumn.program w (route v b floor).base
    (literal v keep) (route v b floor).size)).seq ((dir v b floor).setup w)).seq
    (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (samples v b floor) (List.ofFn (term v b floor cnt inv))))

def ticks (floor : ℕ) (src : Fin (b.fields*v.shapes)→Expr) (cnt inv : Bank) :=
  ((v.projectedTicks (expanded v b) floor src+(4+10*(route v b floor).size))+(4+10*(dir v b floor).size))+
    clock (ProbeStage.Native.columns v.rows (samples v b floor) (List.ofFn (term v b floor cnt inv)))

def routed (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin (b.fields*v.shapes)→Expr) (m : Memory w) :=
  DescentStaticWordColumn.image (route v b floor).base (literal v keep) (v.projectedImage (expanded v b) floor src m)
    (route v b floor).size
def ready (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin (b.fields*v.shapes)→Expr) (m : Memory w) :=
  (dir v b floor).mounted (routed v b floor keep src m)
def image (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin (b.fields*v.shapes)→Expr) (cnt inv : Bank) (m : Memory w) :=
  result (ProbeStage.Native.columns v.rows (samples v b floor) (List.ofFn (term v b floor cnt inv))) (ready v b floor keep src m)

theorem order (floor : ℕ) : floor≤v.projected (expanded v b) floor ∧
    v.projected (expanded v b) floor≤(route v b floor).base ∧ (route v b floor).base≤directory v b floor ∧
    directory v b floor≤ samples v b floor ∧ samples v b floor+(b.fields*v.blocks)*v.rows≤endAddress v b floor:=by
  refine ⟨?_,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩
  rw [v.projected_affine (expanded v b) floor];exact Nat.le_add_right ..

end
end Hierarchy.DescentRetainedTargetPlacement.Chart

end OAI
