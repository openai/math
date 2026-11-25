import OAI.Hierarchy.DescentRetainedCompactBounds
import OAI.Hierarchy.DescentRetainedTargetPlacementRun
import OAI.Hierarchy.DescentResetRetainedPlacementRead

namespace OAI
namespace Hierarchy.DescentRetainedTargetPlacement.Chart
open DescentResetRetainedPlacement DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical
noncomputable section
variable {w U : ℕ} (v : DescentResetRetainedPlacement.Chart) (b : Batch)

theorem sparse_source (floor : ℕ) (keep : Fin v.shapes→Bool) (f : Fin b.fields) (x : Fin v.blocks)
    (Y : Fin v.shapes→Fin v.oldHosts→Fin v.groups→Cell b.bits) (m : Memory w)
    (fixed : ∀j : Fin (v.sparse*v.parts),m ((route v b floor).base+j.val)=(literal v keep j.val:Word w))
    (old : ∀t,Source (.lookup (v.projectedBank (expanded v b) floor (finProdFinEquiv (f,t)) x) .row) (Y t) v.lanes m)
    (room : samples v b floor<2^w) :
    Source (sparseExpr v b floor f x) (selected v b keep Y) v.lanes m:=by
  rintro ⟨h,c⟩
  let k:=finProdFinEquiv (h,c)
  let j:=finProdFinEquiv (v.previous h,c)
  let t:=v.shape h
  let pos:=t.val*(v.blocks*oldRows v)+j.val
  obtain ⟨_,_,b0,d0,_⟩:=order v b floor
  have early:=(b0.trans d0).trans_lt room
  have rfit : (route v b floor).Fits w (samples v b floor):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (d0.trans_lt room),d0⟩
  have ix : (route v b floor).read m (k.val:Word w)=(literal v keep k.val:Word w):=
    (bank_read _ _ (k.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))) rfit).trans (fixed k)
  have sf:=slab_room v b floor f x early
  have oldFit (t : Fin v.shapes):=(DescentResetStemProject.page_fits
    (out:=DescentResetStemProject.out floor (b.fields*v.shapes) v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes)
    (H:=v.oldHosts) (G:=v.groups) (M:=v.lanes) (finProdFinEquiv (f,t)) x
    ((v.projection (expanded v b) floor).trans_lt (((order v b floor).2.1).trans_lt early)))
  have K : pos+1≤aperture v:=by
    have jb : j.val+1≤oldRows v:=j.isLt
    have bp : 1≤v.blocks:=Nat.zero_lt_of_lt x.isLt
    have localRoom : oldRows v≤v.blocks*oldRows v:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (oldRows v) bp
    have next := Nat.mul_le_mul_right (v.blocks*oldRows v) (show t.val+1≤v.shapes+1 from Nat.le_succ_of_le t.isLt)
    change _≤(v.shapes+1)*v.blocks*oldRows v
    rw [Nat.mul_assoc]
    apply le_trans _ next
    rw [Nat.add_mul,Nat.one_mul]
    dsimp only [pos];omega
  have rounded : aperture v+1≤(slab v b floor f x).size:=Nat.le_pow_clog (by decide) _
  have posSmall : pos+1<(2^w):=(K.trans ((Nat.le_succ _).trans rounded)).trans_lt sf.2.1
  have unpack : (finProdFinEquiv.symm k : Fin v.sparse × Fin v.parts) = (h,c) :=
    finProdFinEquiv.symm_apply_apply (h,c)
  have code : literal v keep k.val = (if keep (v.shape h) then pos+1 else 0) := by
    unfold literal
    rw [dite_eq_left (show k.val < v.sparse*v.parts from k.isLt)]
    exact congrArg (fun z : Fin v.sparse × Fin v.parts =>
      if keep (v.shape z.1) then (v.shape z.1).val*(v.blocks*oldRows v)+
        (finProdFinEquiv (v.previous z.1,z.2)).val+1 else 0) unpack
  by_cases use : keep (v.shape h)=true
  · have addr : (literal v keep k.val:Word w)=((pos+1:ℕ):Word w):=by rw [code,ite_eq_left use]
    have nz : ((pos+1:ℕ):Word w)≠0:=by
      intro z;have hz:=congrArg Fin.val z;rw [Fin.val_cast_of_lt posSmall] at hz;simp at hz
    have val := old t (v.previous h,c)
    change (v.projectedBank (expanded v b) floor (finProdFinEquiv (f,t)) x).read m (j.val:Word w)=_ at val
    have cap:=DescentResetStemProject.page_capacity
      (out:=DescentResetStemProject.out floor (b.fields*v.shapes) v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes)
      (H:=v.oldHosts) (G:=v.groups) (M:=v.lanes) (finProdFinEquiv (f,t)) x
    let oldBank := v.projectedBank (expanded v b) floor (finProdFinEquiv (f,t)) x
    have stored : m (oldBank.base+j.val) = ((data (Y t) (v.previous h,c)).val : Word w) :=
      (bank_read oldBank m (j.isLt.trans_le cap) (oldFit t)).symm.trans val
    have payload : data (selected v b keep Y) (h,c) = data (Y t) (v.previous h,c) := by
      unfold data
      apply congrArg (encode b.bits v.lanes)
      funext l
      by_cases active : c.val*v.lanes+l.val < v.groups <;> simp [active,selected,use,t]
    change (sparseExpr v b floor f x).eval m (k.val:Word w)=_
    rw [payload]
    calc
      _ = (slab v b floor f x).read m (pos : Word w) := by
        simp only [sparseExpr,Expr.eval,ix,addr,Comparison.test,beq_iff_eq,Nat.cast_zero,
          nz,ite_false,RowOp.opcode,BinaryOp.eval];
          simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
      _ = m ((slab v b floor f x).base+pos) :=
        bank_read _ m ((Nat.lt_succ_self pos).trans_le (K.trans ((Nat.le_succ _).trans rounded))) sf
      _ = m (oldBank.base+j.val) := congrArg m (slab_address v b floor f t x j.val)
      _ = _ := stored
  · have addr : (literal v keep k.val:Word w)=0:=by rw [code,ite_eq_right use,Nat.cast_zero]
    have blank : data (selected v b keep Y) (h,c)=0:=by
      unfold data
      have zero : (fun l : Fin v.lanes=>if a : c.val*v.lanes+l.val<v.groups then
          selected v b keep Y h ⟨_,a⟩ else 0)=fun _=>0:=by funext l;split <;> simp [selected,use]
      rw [zero]
      apply Fin.ext
      change (finFunctionFinEquiv (fun _ : Fin v.lanes=>(0:Cell b.bits))).val=0
      simp []
    change (sparseExpr v b floor f x).eval m (k.val:Word w)=_
    simp [sparseExpr,Expr.eval,ix,addr,Comparison.test,blank]

theorem validBank (floor : ℕ) (room : endAddress v b floor<2^w) (f : Fin b.fields) (x : Fin v.blocks) :
    (bank v b floor f x).Fits w (endAddress v b floor) ∧ v.rows≤(bank v b floor f x).size :=by
  let i:=finProdFinEquiv (f,x)
  have pos:=Nat.two_pow_pos (Nat.clog 2 (v.rows+1))
  have inside:=Nat.mul_le_mul_right v.rows i.isLt.le
  have area : (bank v b floor f x).base+(bank v b floor f x).size≤endAddress v b floor:=by
    change samples v b floor+i.val*v.rows+DescentResetRetainedPlacement.Chart.rounded v.rows ≤
      samples v b floor+(b.fields*v.blocks)*v.rows+DescentResetRetainedPlacement.Chart.rounded v.rows
    omega
  refine ⟨⟨pos,(Nat.le_add_left ..).trans_lt (area.trans_lt room),area⟩,?_⟩
  exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)

theorem read (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin (b.fields*v.shapes)→Expr) (cnt inv : Bank) (m : Memory w)
    (lanes : 0<v.lanes) (before : 0<b.inputLanes) (blocks : 0<v.blocks) (srcFits : ∀i,(src i).Fits w floor)
    (ct : cnt.Fits w floor) (iv : inv.Fits w floor) (room : endAddress v b floor<2^w)
    (name : Fin U→Fin v.sparse) (count : m cnt.base=(U:Word w)) (inverse : ∀i : Fin U,m (inv.base+i.val)=((name i).val:Word w))
    (countFits : U<2^w) (hostFits : v.newHosts≤2^w) (invFits : U≤ inv.size)
    (Y : Fin (b.fields*v.shapes)→Fin v.oldHosts→Fin (v.groups*v.blocks)→Cell b.bits)
    (input : ∀i,Source (src i) (Y i) b.inputLanes m) (i : Fin b.fields) (x : Fin v.blocks) :
    Source (.lookup (bank v b floor i x) .row) (compact v b keep name Y i x) v.lanes (image v b floor keep src cnt inv m) :=by
  obtain ⟨a,ap,c0,d,e⟩:=order v b floor
  have c:=ap.trans c0
  have lim : samples v b floor<2^w:=((Nat.le_add_right ..).trans e).trans_lt room
  let mid:=v.projectedImage (expanded v b) floor src m
  let last:=ready v b floor keep src m
  obtain ⟨_,readA,placedA,frA,_⟩:=DescentResetStemProjectExpr.run floor v.oldHosts v.groups v.blocks b.bits
    b.inputLanes v.lanes src m Y before lanes blocks srcFits input ((v.projection (expanded v b) floor).trans_lt ((c.trans d).trans_lt lim))
  have frB (u : ℕ) (lo : u<v.projected (expanded v b) floor) : routed v b floor keep src m u=mid u:=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl (lo.trans_le ap))
  have frC (u : ℕ) (lo : u<directory v b floor) : last u=routed v b floor keep src m u:=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl lo)
  have below (u : ℕ) (lo : u<v.projected (expanded v b) floor) : last u=mid u:=(frC _ (lo.trans_le c)).trans (frB _ lo)
  have prior (u : ℕ) (lo : u<floor) : last u=m u:=(below _ (lo.trans_le a)).trans (frA _ (.inl lo))
  have current (t : Fin v.shapes) :
      Source (.lookup (v.projectedBank (expanded v b) floor (finProdFinEquiv (i,t)) x) .row)
        (fun h g=>Y (finProdFinEquiv (i,t)) h (finProdFinEquiv (g,x))) v.lanes last:=by
    intro p
    have fitBank : (v.projectedBank (expanded v b) floor (finProdFinEquiv (i,t)) x).Fits w
        (v.projected (expanded v b) floor) := by
      rw [← v.projection (expanded v b) floor]
      exact placedA (finProdFinEquiv (i,t)) x
    exact (ProtocolRAM.eval_below (out := v.projected (expanded v b) floor)
      (.lookup (v.projectedBank (expanded v b) floor (finProdFinEquiv (i,t)) x) .row)
      _ mid last ⟨fitBank, trivial⟩ below).trans (readA (finProdFinEquiv (i,t)) x p)
  have fixed (j : Fin (v.sparse*v.parts)) : last ((route v b floor).base+j.val)=(literal v keep j.val:Word w):=by
    have bound : j.val < (route v b floor).size :=
      j.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))
    apply (frC _ (Nat.add_lt_add_left (show j.val<(route v b floor).size from bound) _)).trans
    exact DescentStaticWordColumn.read _ _ _ _ bound
  have each:=sparse_source v b floor keep i x _ last fixed current lim
  have makeLarge {B : Bank} (z : B.Fits w floor) : B.Fits w (directory v b floor):=⟨z.1,z.2.1,z.2.2.trans (a.trans c)⟩
  have load:=DescentResetDenseOperand.source (directory v b floor) cnt inv (sparseExpr v b floor i x) last name _ each
    (samples v b floor) ((dir v b floor).books _) ((dir v b floor).book_fits cnt inv (makeLarge ct) (makeLarge iv) lim)
    ((prior _ (by have h:=ct.1;have g:=ct.2.2;omega)).trans count)
    (fun j=>(prior _ (by have z:=j.isLt.trans_le invFits;have h:=iv.2.2;omega)).trans (inverse j)) countFits hostFits invFits
  let z:=finProdFinEquiv (i,x)
  let terms:=List.ofFn (term v b floor cnt inv)
  have fit : ∀q∈terms,q.Fits w (samples v b floor):=by
    intro q h;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h;exact termFits v b floor cnt inv ct iv room j
  obtain ⟨fb,sz⟩:=validBank v b floor room i x
  apply source_column _ _ fb _ _ sz
  intro p
  have iz : z.val<terms.length:=by simpa only [terms,List.length_ofFn] using z.isLt
  have cell:=ProbeStage.Native.columns_read terms last (le_refl (samples v b floor)) fit z.val iz (row _ _ _ p)
  have slot : terms[z.val]'iz = (dir v b floor).load cnt inv (sparseExpr v b floor i x) := by
    calc
      terms[z.val]'iz = term v b floor cnt inv z := by simp only [terms, List.getElem_ofFn, Fin.eta]
      _ = _ := by
        unfold term
        rw [show (finProdFinEquiv.symm z : Fin b.fields × Fin v.blocks) = (i,x) from
          finProdFinEquiv.symm_apply_apply (i,x)]
  rw [slot] at cell
  exact cell.trans (load p)


end
end Hierarchy.DescentRetainedTargetPlacement.Chart

end OAI
