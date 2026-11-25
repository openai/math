import OAI.Hierarchy.DescentTerminalRolePairFields
import OAI.Hierarchy.DescentTerminalActorRepack
import OAI.Hierarchy.DescentTerminalPopulationIssue

namespace OAI
/-! # Retain physical actor presence and paid node population across the two scalar-book scans -/
namespace Hierarchy.DescentTerminalRolePrefix
open DescentTerminalVertexFields DescentTerminalPrimitiveFrames DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization DescentTerminalCombinedRole DescentEpochTagKeys
open DescentBundleHistory DescentKernelHistory ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {q t hid N slots p groups blocks shops wb:ℕ} (R:MaskAllocation.Channels blocks) (start:ℕ) (m:Memory wb)
local notation "L" => MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=slots) (p:=p) (groups:=groups) R start
local notation "meas" => measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=slots) (w:=p) (groups:=groups)
local notation "nbits" => Nat.clog 2 (N+1)

/-- Read the physical output bank of the paid population pass with the same word
format used by the scalar shelf. -/
theorem population {n:ℕ} (b:Fin blocks) (i:Fin shops) (g:Fin groups)
    (fits:shops≤2^wb) (size:shops≤(R.primitive b 3).size)
    (paid:digit nbits g.val (m ((R.primitive b 3).base+i.val)).val=n) :
    venueField (cellAt (meas L m i) (finProdFinEquiv (g,b))) nodeCount=n := by
  let cell:=cellAt (meas L m i) (finProdFinEquiv (g,b))
  have short:(cell 3).val<2^nbits:=by
    have lim:(cell 3).val<2^(1*nbits):=(cell 3).isLt
    simpa only [Nat.one_mul] using lim
  have seen:(cell 3).val=n:=by
    rw [show cell 3=cellAt (meas L m i) (finProdFinEquiv (g,b)) 3 by rfl,cell_digit]
    let channelBits := channelSize (q:=q) (t:=t) (H:=hid) (N:=N) (A:=slots) (w:=p) (groups:=groups) (blocks:=blocks)
    have laneBits : familySize (q:=q) (t:=t) (H:=hid) (N:=N) (A:=slots) (w:=p) (3:Fin 8)=nbits := by
      simp [familySize,items,itemBits]
    have channelEq : channelBits (finProdFinEquiv (b,(3:Fin 8).succ)) = nbits*groups := by
      simp only [channelBits,channelSize,Equiv.symm_apply_apply,primitiveSize,Fin.cases_succ,laneBits]
    simp only [measured,MaskAllocation.shelf,MaskAllocation.Channels.primitive_at,laneBits]
    change digit nbits g.val (((R.primitive b 3).read m (i.val:Computability.VPVNP.BurstRAM.Word wb)).val%2^(channelBits (finProdFinEquiv (b,(3:Fin 8).succ))))=_
    rw [channelEq,digit_clip,Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le fits),Nat.mod_eq_of_lt (i.isLt.trans_le size)]
    exact paid
  rw [venue_digit]
  change digit nbits 0 (cell 3).val=_
  simpa [digit,Nat.mod_eq_of_lt short] using seen

/-- A prior reached actor word is the geometric image, including sites with
zero charged nodes. Its bit is independent of the population word. -/
theorem presence {V:Type} [Fintype V] (home:V→Fin shops) (grp:V→Fin groups) (block:V→Fin blocks)
    (b:Fin blocks) (i:Fin shops) (g:Fin groups) (fits:shops≤2^wb) (size:shops≤(R.occupied b).size)
    (packed:m ((R.occupied b).base+i.val)=((encode 1 groups (fun z=>
      (if ∃v,home v=i ∧ grp v=z ∧ block v=b then 1 else 0):Fin groups→Cell 1)).val:Computability.VPVNP.BurstRAM.Word wb)) (wide:groups≤wb) :
    (blankAt (meas L m i) (finProdFinEquiv (g,b))).val=if ∃v,home v=i ∧ grp v=g ∧ block v=b then 1 else 0 := by
  rw [presence_digit]
  let channelBits := channelSize (q:=q) (t:=t) (H:=hid) (N:=N) (A:=slots) (w:=p) (groups:=groups) (blocks:=blocks)
  have channelEq : channelBits (finProdFinEquiv (b,(0:Fin 9))) = 1*groups := by
    simp only [channelBits,channelSize,Equiv.symm_apply_apply,primitiveSize,Fin.cases_zero]
  simp only [measured,MaskAllocation.shelf,MaskAllocation.Channels.occupied_at]
  change digit 1 g.val (((R.occupied b).read m (i.val:Computability.VPVNP.BurstRAM.Word wb)).val%2^(channelBits (finProdFinEquiv (b,(0:Fin 9)))))=_
  rw [channelEq,digit_clip,Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le fits),Nat.mod_eq_of_lt (i.isLt.trans_le size),packed]
  let flags:Fin groups→Cell 1:=fun z=>if ∃v,home v=i ∧ grp v=z ∧ block v=b then 1 else 0
  have width:1*groups≤wb:=by simpa only [Nat.one_mul] using wide
  have cell: (encode 1 groups flags).val<2^wb:=(encode 1 groups flags).isLt.trans_le (Nat.pow_le_pow_right (by decide) width)
  rw [Fin.val_cast_of_lt cell,digit_encode]
  by_cases hit:∃v,home v=i ∧ grp v=g ∧ block v=b <;> simp [flags,hit]
end

section Complete
open DescriptorExpr
private theorem cheap_pair (wb : ℕ) (first second : DescentTerminalCombinedRole.Shelf) (out countRows : ℕ) :
    CheapCode (paired (wb:=wb) first second out countRows) :=
  @cheap_seq wb (scan wb out countRows (emit first)) (scan wb (out+countRows) countRows (emit second))
    (@scan_cheap wb out countRows (emit first)) (@scan_cheap wb (out+countRows) countRows (emit second))
set_option quotPrecheck false
set_option maxHeartbeats 300000
variable {U B V:Type} [Fintype V] {n A G p rate N groups wb q hid slots blocks shops:ℕ}
    {widthAt:B→ℕ} {r:BitRecipe U B widthAt} (old:Codec U n) (hp:0<p) (shape:Shape p r) (u:r.Node)
    (first second:DescentTerminalCombinedRole.Shelf) (out:ℕ) (R:MaskAllocation.Channels blocks) (start:ℕ) (m:Memory wb)
    (home:V→Fin shops) (grp:V→Fin groups) (block:V→Fin blocks) (v:V) (slot:Fin N)
local notation "rows" => blocks*shops
local notation "cap" => DescentBundleTagKeys.capacity n A G p rate
local notation "mach" => MaskAllocation.shelf (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (p:=p) (groups:=groups) R start
local notation "readAt" => measured (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (w:=p) (groups:=groups) mach
local notation "done" => memory first second out rows m
local notation "src" => observed (n:=n) (A:=A) (G:=G) (p:=p) (R:=rate) (N:=N) (M:=groups)
local notation "i" => home v
local notation "g" => grp v
local notation "b" => block v
local notation "position" => finProdFinEquiv (g,b)
local notation "idx" => (finProdFinEquiv (b,i)).val
variable (fitRole:(emit first).Fits wb out) (fitCount:(emit second).Fits wb out) (limit:out+blocks*shops+blocks*shops<2^wb)
    (roles:Static (A:=A) (G:=G) (p:=p) (R:=rate) (N:=N) (M:=groups) old first m)
    (arity:CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=rate) (N:=N) (M:=groups) slots second m)
    (same:second.input=first.input) (fitsRole:output n A G p rate*N*groups≤wb) (fitsCount:Nat.clog 2 (slots+1)*N*groups≤wb)
    (rBase:(R.primitive (block v) 5).base=out+(block v).val*shops) (rLen:shops≤(R.primitive (block v) 5).size)
    (aBase:(R.primitive (block v) 6).base=out+blocks*shops+(block v).val*shops) (aLen:shops≤(R.primitive (block v) 6).size)
    (roleFit:old.fits (r.tag u)) (arityFit:(shape.recipe hp).arity u≤ slots)
    (countsBefore:(R.primitive (block v) 3).base+(R.primitive (block v) 3).size≤out) (nLen:shops≤(R.primitive (block v) 3).size)
    (actorsBefore:(R.occupied (block v)).base+(R.occupied (block v)).size≤out) (oLen:shops≤(R.occupied (block v)).size)
    (f1:R.primitive (block v) 1=R.occupied (block v)) (wide:groups≤wb)

include fitRole fitCount limit roles arity same countsBefore nLen actorsBefore oLen wide f1 in
/-- Occupation and population hold on every reached site, independently of whether
it has any scalar node. This also supplies the empty-site case before quantifying over nodes. -/
theorem retained
    (paid:digit (Nat.clog 2 (N+1)) (g).val (m ((R.primitive b 3).base+(i).val)).val=Fintype.card r.Node)
    (actors:m ((R.occupied b).base+(i).val)=((encode 1 groups (fun z=>
      (if ∃y,home y=i ∧ grp y=z ∧ block y=b then 1 else 0):Fin groups→Cell 1)).val:Computability.VPVNP.BurstRAM.Word wb)) :
    (paired (wb:=wb) first second out rows).Exec m done (steps rows+steps rows) ∧ CheapCode (paired (wb:=wb) first second out rows) ∧
    (blankAt (readAt done i) position).val=1 ∧
    venueField (cellAt (readAt done i) position) (.inr (.inl ()))=1 ∧
    venueField (cellAt (readAt done i) position) nodeCount=Fintype.card r.Node ∧
    ∀j,j<out→done j=m j := by
  have later : (emit second).Fits wb (out+rows) :=
    ProtocolRAMGeneratedWrite.fits_mono (w:=wb) (a:=out) («b»:=out+rows) (emit second) (Nat.le_add_right out rows) fitCount
  have pairedRun:=both (n:=n) (A:=A) (G:=G) (p:=p) (R:=rate) (N:=N) (M:=groups) (slots:=slots)
    old first second out rows m fitRole fitCount later limit roles arity same
  have before:=paired_below first second out rows m
  have nonempty:shops≤rows:=by simpa using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt (b).isLt))
  have hostRoom:shops≤2^wb:=by omega
  have represented:∃y,home y=i ∧ grp y=g ∧ block y=b:=⟨v,rfl,rfl,rfl⟩
  have fromActor:=(presence (q:=q) (t:=cap) (hid:=hid) (N:=N) (slots:=slots) (p:=p)
    R start m home grp block b i g hostRoom oLen actors wide).trans (ite_eq_left represented)
  have presentNow:=(occupation_below (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (p:=p) mach m done b i g out
    (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.occupied_at] using actorsBefore) before).trans fromActor
  have liveNow:=(live_at (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (p:=p) R start done b i g f1).trans presentNow
  have count:=population (q:=q) (t:=cap) (hid:=hid) (N:=N) (slots:=slots) (p:=p) R start m b i g hostRoom nLen paid
  have countNow:=(field_below (q:=q) (t:=cap) (H:=hid) (N:=N) (A:=slots) (p:=p) mach m done b i g out nodeCount
    (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at,nodeCount,group] using countsBefore) before).trans count
  refine ⟨?_,?_,presentNow,liveNow,countNow,before⟩
  · exact pairedRun.1
  · exact @cheap_pair wb first second out rows

include fitRole fitCount limit roles arity same fitsRole fitsCount rBase rLen aBase aLen roleFit arityFit countsBefore
  nLen actorsBefore oLen wide f1 in
/-- The preceding native population page and actor image survive the two new scans.
This statement records occupation on the physical site even if its scalar node set is empty. -/
theorem «fields»
    (paid:digit (Nat.clog 2 (N+1)) (g).val (m ((R.primitive b 3).base+(i).val)).val=Fintype.card r.Node)
    (actors:m ((R.occupied b).base+(i).val)=((encode 1 groups (fun z=>
      (if ∃y,home y=i ∧ grp y=z ∧ block y=b then 1 else 0):Fin groups→Cell 1)).val:Computability.VPVNP.BurstRAM.Word wb))
    (printed:Printed old (DescentTerminalCombinedRole.fields (n:=n) (A:=A) (G:=G) (p:=p) (R:=rate) (DescentTerminalCombinedRole.node (n:=n) (A:=A) (G:=G) (p:=p) (R:=rate) (N:=N) (M:=groups) (src first m (idx:Computability.VPVNP.BurstRAM.Word wb)) g slot)) (r.tag u) (shape.sliceFields u)) :
    (paired (wb:=wb) first second out rows).Exec m done (steps rows+steps rows) ∧ CheapCode (paired (wb:=wb) first second out rows) ∧
    (blankAt (readAt done i) position).val=1 ∧
    venueField (cellAt (readAt done i) position) (.inr (.inl ()))=1 ∧
    venueField (cellAt (readAt done i) position) nodeCount=Fintype.card r.Node ∧
    venueField (cellAt (readAt done i) position) (nodeRole slot)=
      ((DescentBundleTagKeys.codec old A G p rate).store ((shape.recipe hp).tag u)).val+1 ∧
    venueField (cellAt (readAt done i) position) (nodeArity slot)=(shape.recipe hp).arity u ∧
    ∀j,j<out→done j=m j := by
  have oldFields:=DescentTerminalRolePairFields.paired_fields (q:=q) (hid:=hid) (slots:=slots) (A:=A) (G:=G) (R:=rate) old hp shape u first second out mach m fitRole fitCount
    limit roles arity same fitsRole fitsCount i b g slot
    (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using rBase)
    (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using rLen)
    (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using aBase)
    (by simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using aLen)
    roleFit arityFit printed
  have live:=retained (q:=q) (hid:=hid) (slots:=slots) (A:=A) (G:=G) (p:=p) (rate:=rate) (r:=r) old first second out R start m home grp block v fitRole fitCount limit roles arity same
    countsBefore nLen actorsBefore oLen f1 wide paid actors
  refine ⟨?_,?_,live.2.2.1,live.2.2.2.1,live.2.2.2.2.1,oldFields.2.2.1,oldFields.2.2.2.1,oldFields.2.2.2.2⟩
  · exact oldFields.1
  · exact @cheap_pair wb first second out rows

end Complete
end Hierarchy.DescentTerminalRolePrefix

end OAI
