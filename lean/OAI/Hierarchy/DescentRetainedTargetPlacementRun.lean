import OAI.Hierarchy.DescentRetainedTargetPlacement

namespace OAI
namespace Hierarchy.DescentRetainedTargetPlacement.Chart
open DescentResetRetainedPlacement DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {w : ℕ} (v : DescentResetRetainedPlacement.Chart) (b : Batch)

theorem slab_room (floor : ℕ) (f : Fin b.fields) (x : Fin v.blocks) (space : (route v b floor).base<2^w) :
    (slab v b floor f x).Fits w (route v b floor).base:=by
  let o:=DescentResetStemProject.out floor (b.fields*v.shapes) v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes
  let n:=oldRows v
  have prior : o+((b.fields*v.shapes)*v.blocks)*n≤v.projected (expanded v b) floor:=by
    rw [←v.projection (expanded v b) floor]
    simp only [DescentResetStemProject.endAddress,DescentResetStemProject.pageEnd,DescentVectorBookReshape.rows,
      expanded,oldRows,DescentResetRetainedPlacement.Chart.parts,o,n,Nat.mul_one,Nat.mul_assoc]
    apply Nat.le_add_right
  have field :=Nat.mul_le_mul_right (v.shapes*v.blocks*n) f.isLt.le
  have base : o+f.val*(v.shapes*v.blocks*n)≤v.projected (expanded v b) floor:=by
    exact (Nat.add_le_add_left field o).trans (by simpa only [Nat.mul_assoc] using prior)
  have enlarge : v.blocks*n≤aperture v:=by
    change _≤(v.shapes+1)*v.blocks*n
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul];omega
  have rounded : aperture v≤guard v:= (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have offset :=(Nat.mul_le_mul_right n x.isLt.le).trans (enlarge.trans rounded)
  have full : (slab v b floor f x).base+(slab v b floor f x).size≤(route v b floor).base:=by
    change o+f.val*(v.shapes*v.blocks*n)+x.val*n+guard v≤v.projected (expanded v b) floor+2*guard v
    omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (full.trans_lt space),full⟩

theorem termFits (floor : ℕ) (cnt inv : Bank) (ct : cnt.Fits w floor) (iv : inv.Fits w floor)
    (room : endAddress v b floor<2^w) (j : Fin (b.fields*v.blocks)) :
    (term v b floor cnt inv j).Fits w (samples v b floor):=by
  obtain ⟨a,p,c,d,e⟩:=order v b floor
  have lim : samples v b floor<2^w:=(Nat.le_add_right ..).trans_lt (e.trans_lt room)
  have advance {B : Bank} {lo hi : ℕ} (ok : B.Fits w lo) (inc : lo≤hi) : B.Fits w hi:=
    ⟨ok.1,ok.2.1,ok.2.2.trans inc⟩
  have dirs:=(dir v b floor).book_fits cnt inv (advance ct ((a.trans p).trans c))
    (advance iv ((a.trans p).trans c)) lim
  have region : (route v b floor).Fits w (samples v b floor):=by
    refine ⟨Nat.two_pow_pos _,?_,d⟩
    exact (Nat.le_add_left ..).trans_lt (d.trans_lt lim)
  let z : Fin b.fields×Fin v.blocks:=finProdFinEquiv.symm j
  have slabFit:=advance (slab_room v b floor z.1 z.2 ((c.trans d).trans_lt lim)) (c.trans d)
  apply (dir v b floor).fits dirs
  exact ⟨⟨region,trivial⟩,trivial,trivial,slabFit,⟨region,trivial⟩,trivial⟩

set_option maxHeartbeats 800000 in
theorem any (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin (b.fields*v.shapes)→Expr) (cnt inv : Bank)
    (m : Memory w) (lanes : 0<v.lanes) (blocks : 0<v.blocks) (srcFits : ∀i,(src i).Fits w floor)
    (ct : cnt.Fits w floor) (iv : inv.Fits w floor) (room : endAddress v b floor<2^w) :
    (program v b floor w keep src cnt inv).Exec m (image v b floor keep src cnt inv m) (ticks v b floor src cnt inv) ∧
    (∀a,a<floor ∨ endAddress v b floor≤a→image v b floor keep src cnt inv m a=m a) ∧
    CheapCode (program v b floor w keep src cnt inv) :=by
  obtain ⟨a0,ap,c,d,e⟩:=order v b floor
  have a:=a0.trans ap
  have sm : samples v b floor≤endAddress v b floor:=(Nat.le_add_right ..).trans e
  have lim:=sm.trans_lt room
  obtain ⟨runA,frA,cheapA⟩:=DescentResetStemProjectExpr.any floor v.oldHosts v.groups v.blocks b.bits
    b.inputLanes v.lanes src m lanes blocks srcFits ((v.projection (expanded v b) floor).trans_lt (((ap.trans c).trans d).trans_lt lim))
  have runB : (DescentStaticWordColumn.program w (route v b floor).base (literal v keep) (route v b floor).size).Exec
      (v.projectedImage (expanded v b) floor src m) (routed v b floor keep src m) (4+10*(route v b floor).size) :=
    DescentStaticWordColumn.mount _ _ _ _ (d.trans_lt lim)
  obtain ⟨runC,cheapC,_,frC⟩:=(dir v b floor).setup_run (routed v b floor keep src m) lim
  let terms:=List.ofFn (term v b floor cnt inv)
  have size : terms.length=b.fields*v.blocks:=List.length_ofFn
  have fit : ∀q∈terms,q.Fits w (samples v b floor):=by
    intro q h; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h;exact termFits v b floor cnt inv ct iv room j
  have runD : (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (samples v b floor) terms)).Exec
      (ready v b floor keep src m) (image v b floor keep src cnt inv m)
      (clock (ProbeStage.Native.columns v.rows (samples v b floor) terms)) :=
    ProbeStage.Native.columns_exec terms (ready v b floor keep src m)
    (ProbeStage.Native.columns_safe terms (le_refl (samples v b floor)) fit
      (by simpa only [size] using e.trans_lt room))
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then runA runB) runC) runD,?_,?_⟩
  · intro u hu
    apply (ProbeStage.Native.columns_frame terms (ready v b floor keep src m)
      (hu.imp (fun h=>h.trans_le ((a.trans c).trans d)) (fun h=>by simpa only [size] using e.trans h))).trans
    apply (frC u (hu.imp (fun h=>h.trans_le (a.trans c)) (fun h=>sm.trans h))).trans
    apply (DescentStaticWordColumn.frame (route v b floor).base (route v b floor).size (literal v keep)
      (v.projectedImage (expanded v b) floor src m) u
      (hu.imp (fun h=>h.trans_le a) (fun h=>(d.trans sm).trans h))).trans
    exact frA u (hu.imp_right (fun h=>(v.projection (expanded v b) floor).le.trans ((((ap.trans c).trans d).trans sm).trans h)))
  · exact DescentResetRetainedPlacement.Chart.placement_cheap (v.projectedCode (expanded v b) floor w src)
      (DescentStaticWordColumn.program w (route v b floor).base (literal v keep) (route v b floor).size)
      ((dir v b floor).setup w) (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (samples v b floor) terms))
      @cheapA (DescentStaticWordColumn.cheap w (route v b floor).base (literal v keep) (route v b floor).size) @cheapC
      (program_cheap w (ProbeStage.Native.columns v.rows (samples v b floor) terms))


end
end Hierarchy.DescentRetainedTargetPlacement.Chart

end OAI
