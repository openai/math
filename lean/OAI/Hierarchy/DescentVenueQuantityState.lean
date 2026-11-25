import OAI.Hierarchy.DescentVenueQuantityPlanes
import OAI.Hierarchy.DescentDatedOverlapAperture

namespace OAI
/-! # Public reset count workspace addressed using the observed row and directory banks -/
namespace Hierarchy.DescentVenueQuantityPlanes.State
open DescentSIMDLookup DescentActorRaster DescentPackedZip DescentDatedAddressBook ProtocolRAM Filter
noncomputable section
variable (p:Dims)
def rounded (n:ℕ):=2^Nat.clog 2 n
def sparse:=p.oldHosts*p.shapes
def columns:=sparse p*chunks p.groups p.lanes
def oldRows:=p.blocks*columns p
def newRows:=p.blocks*(p.hosts*chunks p.groups p.lanes)
def lookupArea:=p.blocks*2^((p.precision*p.blocks)*p.lanes)
def reshape (base:ℕ):=Overlap.endAddress base (p.shapes*p.oldHosts) (p.groups*p.blocks) p.oldLanes
  (p.lanes*p.blocks) p.precision
def grouped (base:ℕ):=reshape p base+rounded (lookupArea p+1)+2*rounded (oldRows p+1)
def collect (base:ℕ):=grouped p base+rounded (oldRows p)
def out (base:ℕ):=collect p base+2*rounded (newRows p)+rounded (sparse p)
def roof (base:ℕ):=out p base+rounded (newRows p)
def layout (base:ℕ) (original count inverse:Bank):Layout :=
  ⟨original,count,inverse,base,reshape p base,⟨grouped p base,Nat.clog 2 (oldRows p)⟩,collect p base,out p base⟩

theorem shift (base:ℕ):roof p base=base+roof p 0:=by
  simp only [roof,out,collect,grouped,reshape,Overlap.endAddress,Overlap.dest,Overlap.dictBase,Nat.zero_add,Nat.add_assoc]

private theorem base_to_reshape (base : ℕ) : base ≤ reshape p base := by
  simp only [reshape, Overlap.endAddress, Overlap.dest, Overlap.dictBase, Nat.add_assoc]
  exact Nat.le_add_right ..

private theorem earlier {w base:ℕ} (original count inverse:Bank) (_originalFit:original.Fits w base)
    (countFit:count.Fits w base) (inverseFit:inverse.Fits w base) (endFit:roof p base<2^w) :
    let L:=layout p base original count inverse
    let bank:=Overlap.outputBank base (p.shapes*p.oldHosts) (p.groups*p.blocks) p.oldLanes (p.lanes*p.blocks) p.precision
    let spec:=DescentScalarBookReshape.layout p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes L.reshape bank
    let n:=sparse p
    let s:=chunks p.groups p.lanes
    (DescentScalarBookReshape.expression spec).Fits w L.grouped.base ∧
      (DenseRead.expr p.blocks p.hosts s L.collect n L.count L.inverse L.grouped).Fits w L.out :=by
  intro L bank spec n s
  have inputEnd' := base_to_reshape p base
  have ra:=Nat.le_pow_clog (b:=2) (by decide) (lookupArea p+1)
  have ro:=Nat.le_pow_clog (b:=2) (by decide) (oldRows p+1)
  have low:reshape p base≤grouped p base:=by unfold grouped;omega
  have mid:grouped p base≤collect p base:=Nat.le_add_right ..
  have final:collect p base≤out p base:=by unfold out;omega
  have end_:out p base≤roof p base:=Nat.le_add_right ..
  have banks (T:Bank) (lo:ℕ) (t:T.base+T.size≤lo) (budget:lo≤roof p base):T.Fits w lo :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (t.trans_lt (budget.trans_lt endFit)),t⟩
  have headToEnd:=mid.trans (final.trans end_)
  have groupFit: L.grouped.Fits w L.out:=banks _ _ (by exact final) end_
  have rootFields : spec.dictionary.Fits w L.grouped.base ∧ spec.srcRow.Fits w L.grouped.base ∧
      spec.offset.Fits w L.grouped.base ∧ bank.Fits w L.grouped.base :=by
    dsimp only [spec,L,layout,DescentScalarBookReshape.layout]
    refine ⟨banks _ _ ?_ headToEnd,banks _ _ ?_ headToEnd,banks _ _ ?_ headToEnd,
      banks _ _ low headToEnd⟩ <;> simp only [grouped,lookupArea,oldRows,columns,sparse,rounded,Bank.size] at * <;> omega
  have sourceFit : spec.source.Fits w L.grouped.base := rootFields.2.2.2
  have counterFit : L.count.Fits w L.out :=
    banks count _ (countFit.2.2.trans (inputEnd'.trans (low.trans (mid.trans final)))) end_
  have inverseF : L.inverse.Fits w L.out :=
    banks inverse _ (inverseFit.2.2.trans (inputEnd'.trans (low.trans (mid.trans final)))) end_
  have pages : collect p base + rounded (newRows p) + rounded (newRows p) + rounded (sparse p) =
      out p base := by simp only [out, two_mul, Nat.add_assoc]
  have hdr : (DenseRead.host p.blocks p.hosts s L.collect).Fits w L.out ∧
      (DenseRead.offset p.blocks p.hosts s L.collect).Fits w L.out ∧
      (DenseRead.stride p.blocks p.hosts s L.collect n).Fits w L.out:=by
    refine ⟨banks _ _ ?_ end_,banks _ _ ?_ end_,banks _ _ ?_ end_⟩
    · change collect p base + rounded (newRows p) ≤ out p base
      rw [← pages]
      exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
    · change collect p base + rounded (newRows p) + rounded (newRows p) ≤ out p base
      rw [← pages]
      exact Nat.le_add_right ..
    · exact pages.le
  exact ⟨by simp [DescentScalarBookReshape.expression,Expr.Fits,rootFields.1,rootFields.2.2.1,rootFields.2.1,sourceFit],
    by simp [DenseRead.expr,Expr.Fits,hdr.1,hdr.2.1,hdr.2.2,groupFit,counterFit,inverseF]⟩

theorem room {used w:ℕ} (base:ℕ) (original count inverse:Bank) (oldFit:original.Fits w base)
    (cntFit:count.Fits w base) (invFit:inverse.Fits w base)
    (oldSize:p.shapes*p.oldHosts*chunks (p.groups*p.blocks) p.oldLanes≤original.size)
    (inverseSize:used ≤ inverse.size) (real:used<2^w) (host:p.hosts≤2^w) (positive:0<p.lanes)
    (blockPos:0<p.blocks) (space:roof p base<2^w):
    Room p (layout p base original count inverse) used w:=by
  let L:=layout p base original count inverse
  have upper: out p base≤roof p base:=Nat.le_add_right ..
  have collectLe:collect p base≤out p base:=by unfold out;omega
  have shapeLe:reshape p base≤grouped p base:=by unfold grouped;omega
  have og:grouped p base≤collect p base:=Nat.le_add_right ..
  have initial : base≤reshape p base:=base_to_reshape p base
  have change:chunks (p.groups*p.blocks) (p.lanes*p.blocks)=chunks p.groups p.lanes:=
    chunks_group _ _ _ positive blockPos
  have nextSpace:reshape p base<2^w:=(shapeLe.trans (og.trans (collectLe.trans upper))).trans_lt space
  have ok:=Overlap.output_fits base (p.shapes*p.oldHosts) (p.groups*p.blocks) p.oldLanes (p.lanes*p.blocks) p.precision w nextSpace
  have roots:=earlier p original count inverse oldFit cntFit invFit space
  have tableSize:=Nat.le_pow_clog (b:=2) (by decide) (lookupArea p+1)
  have span:=Nat.le_pow_clog (b:=2) (by decide) (oldRows p+1)
  have late:reshape p base+DescentScalarBookReshape.cells p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes≤grouped p base:=by
    simp only [DescentScalarBookReshape.cells,grouped,lookupArea,oldRows,columns,sparse,rounded] at *
    omega
  have trueTile:=Nat.le_pow_clog (b:=2) (by decide) (oldRows p)
  have nextTile:=Nat.le_pow_clog (b:=2) (by decide) (newRows p)
  refine ⟨oldFit,oldSize,ok.2.2.trans_lt nextSpace,⟨roots.1,?_,?_,late,?_⟩,initial,roots.2,trueTile,cntFit.1,
    inverseSize,cntFit.2.2,invFit.2.2,shapeLe.trans og,le_rfl,?_,?_,host,real⟩
  · simpa only [layout,reshape,Overlap.finish,Overlap.outputBank,Overlap.rows,change,Nat.mul_assoc] using ok.2.2
  · simpa only [layout,Overlap.rows,change,Nat.mul_assoc] using ok.2.1
  · exact (Nat.add_le_add_left trueTile _).trans_lt ((collectLe.trans upper).trans_lt space)
  · change collect p base+(2*(2^Nat.clog 2 (newRows p))+2^Nat.clog 2 (sparse p))≤out p base
    simp [out,rounded,Nat.add_assoc]
  · exact (Nat.add_le_add_left nextTile _).trans_lt space

variable {ι:ℕ→Type*}
structure ScalarRoom (v:∀h,ι h→Dims):Prop where
  sheets:Bounded (fun h i=>(v h i).shapes)
  oldHosts:Bounded (fun h i=>(v h i).oldHosts)
  hosts:Bounded (fun h i=>(v h i).hosts)
  groups:Bounded (fun h i=>(v h i).groups)
  blocks:Bounded (fun h i=>(v h i).blocks)
  oldLanes:Bounded (fun h i=>(v h i).oldLanes)
  lanes:Bounded (fun h i=>(v h i).lanes)
  rawWidth:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(v h i).precision*(v h i).oldLanes≤C*h
  reshapedWidth:∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,((v h i).precision*(v h i).blocks)*(v h i).lanes≤C*h

theorem extent_rate (v:∀h,ι h→Dims) (r:ScalarRoom v):Bounded (fun h i=>roof (v h i) 0):=by
  have overlap:=Overlap.address_rate (r.sheets.mul r.oldHosts) (r.groups.mul r.blocks) r.oldLanes (r.lanes.mul r.blocks) r.rawWidth
  have chunkBound:Bounded (fun h i=>chunks (v h i).groups (v h i).lanes):=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have old:=r.oldHosts.mul r.sheets
  have inner:=old.mul chunkBound
  have data_:=r.blocks.mul inner
  have new_:=r.blocks.mul (r.hosts.mul chunkBound)
  obtain ⟨K,rk⟩:=r.reshapedWidth
  have dict:=r.blocks.mul (Bounded.pow_of_linear (K:=K) rk)
  have shelves:=((overlap.add (dict.add (Bounded.const 1)).padded).add ((Bounded.const 2).mul (data_.add (Bounded.const 1)).padded))
  exact ((((shelves.add data_.padded).add ((Bounded.const 2).mul new_.padded)).add old.padded).add new_.padded)

end
end Hierarchy.DescentVenueQuantityPlanes.State

end OAI
