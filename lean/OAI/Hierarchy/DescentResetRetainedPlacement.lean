import OAI.Hierarchy.DescentResetRetainedPlacementChart
import OAI.Hierarchy.DescentResetDenseOperand
import OAI.Hierarchy.DescentResetStemProjectExpr

namespace OAI
/-! # Native sparse-to-compact relocation of retained reset operand pages -/
namespace Hierarchy.DescentResetRetainedPlacement.Chart
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {w U : ℕ} (v : DescentResetRetainedPlacement.Chart) (b : DescentResetRetainedPlacement.Batch)

def previous (h : Fin v.sparse) : Fin v.oldHosts :=finProdFinEquiv.symm h |>.1
def shape (h : Fin v.sparse) : Fin v.shapes :=finProdFinEquiv.symm h |>.2
/-- The pointer is one-based so an omitted role and the actual first row remain distinct. -/
def literal (keep : Fin v.shapes→Bool) (j : ℕ) : ℕ :=
  if hit : j<v.sparse*v.parts then
    let z : Fin v.sparse×Fin v.parts:=finProdFinEquiv.symm ⟨j,hit⟩
    if keep (v.shape z.1) then (finProdFinEquiv (v.previous z.1,z.2)).val+1 else 0
  else 0

def dir (floor : ℕ) : DescentResetDenseOperand.Layout :=⟨v.directory b floor,v.newHosts,v.sparse,v.parts⟩
def projectedBank (floor : ℕ) (i : Fin b.fields) (x : Fin v.blocks) :=
  DescentResetStemProject.bank floor b.fields v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes i x
def sparseExpr (floor : ℕ) (i : Fin b.fields) (x : Fin v.blocks) : Expr :=
  let addr:=Expr.lookup (v.route b floor) .row
  .branch .eq addr (.lit 0) (.lit 0) (.lookup (v.projectedBank b floor i x) (.op .sub addr (.lit 1)))
def term (floor : ℕ) (cnt inv : Bank) (j : Fin (b.fields*v.blocks)) : Expr :=
  let z:=finProdFinEquiv.symm j
  (v.dir b floor).load cnt inv (v.sparseExpr b floor z.1 z.2)
def projectedCode (floor w : ℕ) (src : Fin b.fields→Expr) :=
  DescentResetStemProjectExpr.program floor v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes src w
def projectedTicks (floor : ℕ) (src : Fin b.fields→Expr) :=
  DescentResetStemProjectExpr.ticks floor v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes src
def projectedImage (floor : ℕ) (src : Fin b.fields→Expr) (m : Memory w) :=
  DescentResetStemProjectExpr.image floor v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes src m

def code (floor w : ℕ) (keep : Fin v.shapes→Bool) (src : Fin b.fields→Expr) (cnt inv : Bank) :=
  (((v.projectedCode b floor w src).seq (DescentStaticWordColumn.program w (v.projected b floor)
    (v.literal keep) (v.route b floor).size)).seq ((v.dir b floor).setup w)).seq
    (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (v.samples b floor)
      (List.ofFn (v.term b floor cnt inv))))
def ticks (floor : ℕ) (src : Fin b.fields→Expr) (cnt inv : Bank) :=
  ((v.projectedTicks b floor src+(4+10*(v.route b floor).size))+(4+10*(v.dir b floor).size))+
    clock (ProbeStage.Native.columns v.rows (v.samples b floor) (List.ofFn (v.term b floor cnt inv)))
def routed (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin b.fields→Expr) (m : Memory w) :=
  DescentStaticWordColumn.image (v.projected b floor) (v.literal keep) (v.projectedImage b floor src m)
    (v.route b floor).size
def ready (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin b.fields→Expr) (m : Memory w) :=
  (v.dir b floor).mounted (v.routed b floor keep src m)
def image (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin b.fields→Expr) (cnt inv : Bank) (m : Memory w) :=
  result (ProbeStage.Native.columns v.rows (v.samples b floor) (List.ofFn (v.term b floor cnt inv)))
    (v.ready b floor keep src m)

theorem projection (floor : ℕ) :
    DescentResetStemProject.endAddress floor b.fields v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes=
      v.projected b floor :=by
  simp only [projected,rounded,parts,DescentResetStemProject.endAddress,DescentResetStemProject.pageEnd,
    DescentResetStemProject.out,DescentResetStemProject.reshapeBase,DescentResetStemProject.converted,
    DescentResetStemProject.overlapBase,DescentResetStemProject.gathered,DescentResetStemProject.dense,
    DescentVectorBookReshape.output,DescentVectorBookReshape.cells,DescentVectorBookReshape.dictionaryWords,
    DescentVectorBookReshape.rows,Bank.size]

theorem order (floor : ℕ) : floor≤v.projected b floor ∧ v.projected b floor≤v.directory b floor ∧
    v.directory b floor≤v.samples b floor ∧ v.samples b floor+(b.fields*v.blocks)*v.rows≤v.endAddress b floor :=by
  refine ⟨?_,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩
  rw [v.projected_affine b floor];exact Nat.le_add_right ..

theorem termFits (floor : ℕ) (cnt inv : Bank) (ct : cnt.Fits w floor) (iv : inv.Fits w floor)
    (room : v.endAddress b floor<2^w) (j : Fin (b.fields*v.blocks)) :
    (v.term b floor cnt inv j).Fits w (v.samples b floor) :=by
  obtain ⟨a,c,d,e⟩:=v.order b floor
  have sm:= (Nat.le_add_right ..).trans e
  have changeCap {B : Bank} {lo hi : ℕ} (ok : B.Fits w lo) (inc : lo≤hi) : B.Fits w hi:=
    ⟨ok.1,ok.2.1,ok.2.2.trans inc⟩
  have dirs:=(v.dir b floor).book_fits cnt inv (changeCap ct (a.trans c)) (changeCap iv (a.trans c)) (sm.trans_lt room)
  have region : (v.route b floor).Fits w (v.samples b floor):=by
    refine ⟨Nat.two_pow_pos _,?_,d⟩
    exact (Nat.le_add_left ..).trans_lt ((d.trans sm).trans_lt room)
  let z : Fin b.fields×Fin v.blocks:=finProdFinEquiv.symm j
  have page : (v.projectedBank b floor z.1 z.2).Fits w (v.samples b floor):=by
    have src:=DescentResetStemProject.page_fits (w:=w) (out:=DescentResetStemProject.out floor b.fields v.oldHosts
      v.groups v.blocks b.bits b.inputLanes v.lanes) (H:=v.oldHosts) (G:=v.groups) (M:=v.lanes) z.1 z.2
    apply changeCap (src ((v.projection b floor).trans_lt (((c.trans d).trans sm).trans_lt room)))
    exact (v.projection b floor).le.trans (c.trans d)
  apply (v.dir b floor).fits dirs
  exact ⟨⟨region,trivial⟩,trivial,trivial,page,⟨region,trivial⟩,trivial⟩

theorem placement_cheap (project route directory columns : Procedure w) (p : CheapCode project)
    (r : CheapCode route) (d : CheapCode directory) (c : CheapCode columns) :
    CheapCode (((project.seq route).seq directory).seq columns) :=
  cheap_seq (A:=(project.seq route).seq directory) (B:=columns)
    (cheap_seq (A:=project.seq route) (B:=directory)
      (cheap_seq (A:=project) (B:=route) @p @r) @d) @c

set_option maxHeartbeats 800000 in
theorem any (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin b.fields→Expr) (cnt inv : Bank)
    (m : Memory w) (lanes : 0<v.lanes) (blocks : 0<v.blocks) (srcFits : ∀i,(src i).Fits w floor)
    (ct : cnt.Fits w floor) (iv : inv.Fits w floor) (room : v.endAddress b floor<2^w) :
    (v.code b floor w keep src cnt inv).Exec m (v.image b floor keep src cnt inv m) (v.ticks b floor src cnt inv) ∧
    (∀a,a<floor ∨ v.endAddress b floor≤a→v.image b floor keep src cnt inv m a=m a) ∧
    CheapCode (v.code b floor w keep src cnt inv) :=by
  obtain ⟨a,c,d,e⟩:=v.order b floor
  have sm : v.samples b floor≤v.endAddress b floor:=(Nat.le_add_right ..).trans e
  have lim:=sm.trans_lt room
  obtain ⟨runA,frA,cheapA⟩:=DescentResetStemProjectExpr.any floor v.oldHosts v.groups v.blocks b.bits
    b.inputLanes v.lanes src m lanes blocks srcFits ((v.projection b floor).trans_lt ((c.trans d).trans_lt lim))
  have runB : (DescentStaticWordColumn.program w (v.projected b floor) (v.literal keep) (v.route b floor).size).Exec
      (v.projectedImage b floor src m) (v.routed b floor keep src m) (4+10*(v.route b floor).size) :=
    DescentStaticWordColumn.mount _ _ _ _ (d.trans_lt lim)
  obtain ⟨runC,cheapC,_,frC⟩:=(v.dir b floor).setup_run (v.routed b floor keep src m) lim
  let terms:=List.ofFn (v.term b floor cnt inv)
  have size : terms.length=b.fields*v.blocks:=List.length_ofFn
  have fit : ∀q∈terms,q.Fits w (v.samples b floor):=by
    intro q h; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h;exact v.termFits b floor cnt inv ct iv room j
  have runD : (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (v.samples b floor) terms)).Exec
      (v.ready b floor keep src m) (v.image b floor keep src cnt inv m)
      (clock (ProbeStage.Native.columns v.rows (v.samples b floor) terms)) :=
    ProbeStage.Native.columns_exec terms (v.ready b floor keep src m)
    (ProbeStage.Native.columns_safe terms (le_refl (v.samples b floor)) fit
      (by simpa only [size] using e.trans_lt room))
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then runA runB) runC) runD,?_,?_⟩
  · intro u hu
    apply (ProbeStage.Native.columns_frame terms (v.ready b floor keep src m)
      (hu.imp (fun h=>h.trans_le ((a.trans c).trans d)) (fun h=>by simpa only [size] using e.trans h))).trans
    apply (frC u (hu.imp (fun h=>h.trans_le (a.trans c)) (fun h=>sm.trans h))).trans
    apply (DescentStaticWordColumn.frame (v.projected b floor) (v.route b floor).size (v.literal keep)
      (v.projectedImage b floor src m) u
      (hu.imp (fun h=>h.trans_le a) (fun h=>(d.trans sm).trans h))).trans
    exact frA u (hu.imp_right (fun h=>(v.projection b floor).le.trans (((c.trans d).trans sm).trans h)))
  · exact placement_cheap (v.projectedCode b floor w src)
      (DescentStaticWordColumn.program w (v.projected b floor) (v.literal keep) (v.route b floor).size)
      ((v.dir b floor).setup w) (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (v.samples b floor) terms))
      @cheapA (DescentStaticWordColumn.cheap w (v.projected b floor) (v.literal keep) (v.route b floor).size) @cheapC
      (program_cheap w (ProbeStage.Native.columns v.rows (v.samples b floor) terms))

end
end Hierarchy.DescentResetRetainedPlacement.Chart

end OAI
