import OAI.Hierarchy.DescentResetRetainedPlacement

namespace OAI
/-! # Reading the retained node and signed fields at the actual dense reset actor -/
namespace Hierarchy.DescentResetRetainedPlacement.Chart
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical
noncomputable section
variable {w U : ℕ} (v : DescentResetRetainedPlacement.Chart) (b : DescentResetRetainedPlacement.Batch)

def selected (keep : Fin v.shapes→Bool) (Y : Fin v.oldHosts→Fin v.groups→Cell b.bits)
    (raw : Fin v.sparse) (g : Fin v.groups) : Cell b.bits:=
  if keep (v.shape raw) then Y (v.previous raw) g else 0

theorem validBank (floor : ℕ) (room : v.endAddress b floor<2^w) (f : Fin b.fields) (x : Fin v.blocks) :
    (v.bank b floor f x).Fits w (v.endAddress b floor) ∧ v.rows≤(v.bank b floor f x).size :=by
  let i:=finProdFinEquiv (f,x)
  have pos:=Nat.two_pow_pos (Nat.clog 2 (v.rows+1))
  have inside:=Nat.mul_le_mul_right v.rows i.isLt.le
  have area : (v.bank b floor f x).base+(v.bank b floor f x).size≤v.endAddress b floor:=by
    change v.samples b floor+i.val*v.rows+rounded v.rows≤v.samples b floor+(b.fields*v.blocks)*v.rows+rounded v.rows
    omega
  refine ⟨⟨pos,(Nat.le_add_left ..).trans_lt (area.trans_lt room),area⟩,?_⟩
  exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)

theorem sparse_source (floor : ℕ) (keep : Fin v.shapes→Bool) (i : Fin b.fields) (x : Fin v.blocks)
    (Y : Fin v.oldHosts→Fin v.groups→Cell b.bits) (m : Memory w)
    (fixed : ∀j : Fin (v.sparse*v.parts),m ((v.route b floor).base+j.val)=(v.literal keep j.val:Word w))
    (old : Source (.lookup (v.projectedBank b floor i x) .row) Y v.lanes m)
    (room : v.samples b floor<2^w) :
    Source (v.sparseExpr b floor i x) (v.selected b keep Y) v.lanes m :=by
  rintro ⟨h,c⟩
  let k:=finProdFinEquiv (h,c)
  let j:=finProdFinEquiv (v.previous h,c)
  have routeFit : (v.route b floor).Fits w (v.samples b floor):=by
    have le : v.directory b floor≤v.samples b floor:=Nat.le_add_right ..
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (le.trans_lt room),le⟩
  have ksmall : k.val<(v.route b floor).size:=k.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))
  have ix : (v.route b floor).read m (k.val:Word w)=(v.literal keep k.val:Word w):=
    (bank_read _ _ ksmall routeFit).trans (fixed k)
  have bound : j.val+1<2^w:=by
    have sz:=DescentResetStemProject.page_fits (out:=DescentResetStemProject.out floor b.fields v.oldHosts
      v.groups v.blocks b.bits b.inputLanes v.lanes) (H:=v.oldHosts) (G:=v.groups) (M:=v.lanes) i x
      ((v.projection b floor).trans_lt (((v.order b floor).2.1.trans (v.order b floor).2.2.1).trans_lt room))
    exact lt_of_le_of_lt (Nat.succ_le_of_lt (j.isLt.trans_le (DescentResetStemProject.page_capacity (out:=DescentResetStemProject.out floor b.fields
      v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes) (H:=v.oldHosts) (G:=v.groups) (M:=v.lanes) i x))) sz.2.1
  have unpack : (finProdFinEquiv.symm k : Fin v.sparse × Fin v.parts) = (h,c) :=
    finProdFinEquiv.symm_apply_apply (h,c)
  have code : v.literal keep k.val = (if keep (v.shape h) then j.val+1 else 0) := by
    unfold literal
    rw [dite_eq_left (show k.val < v.sparse*v.parts from k.isLt)]
    exact congrArg (fun z : Fin v.sparse × Fin v.parts =>
      if keep (v.shape z.1) then (finProdFinEquiv (v.previous z.1,z.2)).val+1 else 0) unpack
  by_cases use : keep (v.shape h)=true
  · have addr : (v.literal keep k.val:Word w)=((j.val+1:ℕ):Word w):=by
      rw [code, ite_eq_left use]
    have nz : ((j.val+1:ℕ):Word w)≠0:=by
      intro dead;have z:=congrArg Fin.val dead;rw [Fin.val_cast_of_lt bound] at z;simp at z
    have payload : data (v.selected b keep Y) (h,c) = data Y (v.previous h,c) := by
      unfold data
      apply congrArg (encode b.bits v.lanes)
      funext l
      by_cases active : c.val*v.lanes+l.val < v.groups <;> simp [active, selected, use]
    change (v.sparseExpr b floor i x).eval m (k.val:Word w)=_
    rw [payload]
    calc
      _ = (v.projectedBank b floor i x).read m (j.val : Word w) := by
        simp only [sparseExpr, Expr.eval, ix, addr, Comparison.test, beq_iff_eq, Nat.cast_zero,
          nz, ite_false, RowOp.opcode, BinaryOp.eval];
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      _ = _ := old (v.previous h,c)
  · have addr : (v.literal keep k.val:Word w)=0:=by rw [code, ite_eq_right use, Nat.cast_zero]
    have blank : data (v.selected b keep Y) (h,c)=0:=by
      unfold data
      have allZero : (fun l : Fin v.lanes=>if a : c.val*v.lanes+l.val<v.groups then
          v.selected b keep Y h ⟨_,a⟩ else 0)=fun _=>0:=by funext l;split <;> simp [selected,use]
      rw [allZero]
      apply Fin.ext
      change (finFunctionFinEquiv (fun _ : Fin v.lanes=>(0:Cell b.bits))).val=0
      simp []
    change (v.sparseExpr b floor i x).eval m (k.val:Word w)=_
    simp [sparseExpr,Expr.eval,ix,addr,Comparison.test,blank]

def compact (keep : Fin v.shapes→Bool) (name : Fin U→Fin v.sparse)
    (Y : Fin b.fields→Fin v.oldHosts→Fin (v.groups*v.blocks)→Cell b.bits) (i : Fin b.fields) (x : Fin v.blocks) :=
  DescentResetDenseOperand.dense (H:=v.newHosts) name
    (v.selected b keep (fun h g=>Y i h (finProdFinEquiv (g,x))))

theorem read (floor : ℕ) (keep : Fin v.shapes→Bool) (src : Fin b.fields→Expr) (cnt inv : Bank) (m : Memory w)
    (lanes : 0<v.lanes) (before : 0<b.inputLanes) (blocks : 0<v.blocks) (srcFits : ∀i,(src i).Fits w floor)
    (ct : cnt.Fits w floor) (iv : inv.Fits w floor) (room : v.endAddress b floor<2^w)
    (name : Fin U→Fin v.sparse) (count : m cnt.base=(U:Word w)) (inverse : ∀i : Fin U,m (inv.base+i.val)=((name i).val:Word w))
    (countFits : U<2^w) (hostFits : v.newHosts≤2^w) (invFits : U≤ inv.size)
    (Y : Fin b.fields→Fin v.oldHosts→Fin (v.groups*v.blocks)→Cell b.bits)
    (input : ∀i,Source (src i) (Y i) b.inputLanes m) (i : Fin b.fields) (x : Fin v.blocks) :
    Source (.lookup (v.bank b floor i x) .row) (v.compact b keep name Y i x) v.lanes (v.image b floor keep src cnt inv m) :=by
  obtain ⟨a,c,d,e⟩:=v.order b floor
  have lim : v.samples b floor<2^w:=((Nat.le_add_right ..).trans e).trans_lt room
  let mid:=v.projectedImage b floor src m
  let last:=v.ready b floor keep src m
  obtain ⟨_,readA,placedA,frA,_⟩:=DescentResetStemProjectExpr.run floor v.oldHosts v.groups v.blocks b.bits
    b.inputLanes v.lanes src m Y before lanes blocks srcFits input ((v.projection b floor).trans_lt ((c.trans d).trans_lt lim))
  have frB (u : ℕ) (lo : u<v.projected b floor) : v.routed b floor keep src m u=mid u:=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl lo)
  have frC (u : ℕ) (lo : u<v.directory b floor) : last u=v.routed b floor keep src m u:=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl lo)
  have below (u : ℕ) (lo : u<v.projected b floor) : last u=mid u:=(frC _ (lo.trans_le c)).trans (frB _ lo)
  have prior (u : ℕ) (lo : u<floor) : last u=m u:=(below _ (lo.trans_le a)).trans (frA _ (.inl lo))
  have old := readA i x
  have current : Source (.lookup (v.projectedBank b floor i x) .row) (fun h g=>Y i h (finProdFinEquiv (g,x))) v.lanes last:=by
    intro p
    have fitBank : (v.projectedBank b floor i x).Fits w (v.projected b floor) := by
      rw [← v.projection b floor]
      exact placedA i x
    exact (ProtocolRAM.eval_below (out := v.projected b floor) (.lookup (v.projectedBank b floor i x) .row)
      _ mid last ⟨fitBank, trivial⟩ below).trans (old p)
  have fixed (j : Fin (v.sparse*v.parts)) : last ((v.route b floor).base+j.val)=(v.literal keep j.val:Word w):=by
    have bound : j.val < (v.route b floor).size :=
      j.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))
    apply (frC _ (Nat.add_lt_add_left (show j.val<(v.route b floor).size from bound) _)).trans
    exact DescentStaticWordColumn.read _ _ _ _ bound
  have each:=v.sparse_source b floor keep i x _ last fixed current lim
  have makeLarge {B : Bank} (z : B.Fits w floor) : B.Fits w (v.directory b floor):=⟨z.1,z.2.1,z.2.2.trans (a.trans c)⟩
  have load:=DescentResetDenseOperand.source (v.directory b floor) cnt inv (v.sparseExpr b floor i x) last name _ each
    (v.samples b floor) ((v.dir b floor).books _) ((v.dir b floor).book_fits cnt inv (makeLarge ct) (makeLarge iv) lim)
    ((prior _ (by have h:=ct.1;have g:=ct.2.2;omega)).trans count)
    (fun j=>(prior _ (by have z:=j.isLt.trans_le invFits;have h:=iv.2.2;omega)).trans (inverse j)) countFits hostFits invFits
  let z:=finProdFinEquiv (i,x)
  let terms:=List.ofFn (v.term b floor cnt inv)
  have fit : ∀q∈terms,q.Fits w (v.samples b floor):=by
    intro q h;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h;exact v.termFits b floor cnt inv ct iv room j
  obtain ⟨fb,sz⟩:=v.validBank b floor room i x
  apply source_column _ _ fb _ _ sz
  intro p
  have iz : z.val<terms.length:=by simpa only [terms,List.length_ofFn] using z.isLt
  have cell:=ProbeStage.Native.columns_read terms last (le_refl (v.samples b floor)) fit z.val iz (row _ _ _ p)
  have slot : terms[z.val]'iz = (v.dir b floor).load cnt inv (v.sparseExpr b floor i x) := by
    calc
      terms[z.val]'iz = v.term b floor cnt inv z := by simp only [terms, List.getElem_ofFn, Fin.eta]
      _ = _ := by
        unfold term
        rw [show (finProdFinEquiv.symm z : Fin b.fields × Fin v.blocks) = (i,x) from
          finProdFinEquiv.symm_apply_apply (i,x)]
  rw [slot] at cell
  exact cell.trans (load p)

end
end Hierarchy.DescentResetRetainedPlacement.Chart

end OAI
