import OAI.Hierarchy.DescentResetStemChipProjection
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # The root packet at the original actor of every reset operand row -/
namespace Hierarchy.DescentOperandRootPull
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  base : ℕ
  parent : ℕ
  actors : ℕ
  receivers : ℕ
  groups : ℕ
  blocks : ℕ
  bits : ℕ
  fields : ℕ
  beforeLanes : ℕ
  afterLanes : ℕ

namespace Layout
variable (L : Layout)
def width:=L.bits*L.fields
def prefixEnd:=DescentResetStemProject.endAddress L.base 1 L.actors L.groups L.blocks L.width L.beforeLanes L.afterLanes
def tableBase:=L.prefixEnd+DescentResetStemKeyReindex.size L.actors L.receivers L.groups L.afterLanes
def endAddress:=DescentOperandFamilyBook.endAddress L.fields 1 L.width L.afterLanes L.tableBase
def field (i : Fin L.fields) (data : Fin 1→Cell L.width) : Cell L.bits :=
  (encode L.bits L.fields).symm (data 0) i

theorem field_zero (i : Fin L.fields) : L.field i (fun _=>0)=0 := by
  have zero : encode L.bits L.fields (fun _=>0)=0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin L.fields=>(0:Cell L.bits))).val=0
    simp
  change (encode L.bits L.fields).symm (0 : Cell (L.bits*L.fields)) i = 0
  exact congrFun ((encode L.bits L.fields).symm_apply_eq.mpr zero.symm) i

def parentPhase (w : ℕ) := DescentResetStemKeyReindex.phase w L.prefixEnd L.actors L.receivers L.groups L.afterLanes
def packets (x : Fin L.blocks) : Expr :=
  DescentResetStemChipProjection.source L.base L.parent L.actors L.receivers L.groups L.blocks L.width L.beforeLanes L.afterLanes
    (0:Fin 1) x
def src (i : Fin L.fields) (x : Fin L.blocks) : Expr :=
  DescentOperandFamilyBook.expr L.field L.afterLanes L.tableBase i (fun _=>L.packets x)

def program (old : Expr) (w : ℕ) :=
  ((DescentResetStemProjectExpr.program L.base L.actors L.groups L.blocks L.width L.beforeLanes L.afterLanes
    (fun _ : Fin 1=>old) w).seq (L.parentPhase w).program).seq
    (DescentOperandFamilyBook.program L.field L.afterLanes L.tableBase w)
def clock (old : Expr) (w : ℕ) :=
  DescentResetStemProjectExpr.ticks L.base L.actors L.groups L.blocks L.width L.beforeLanes L.afterLanes
    (fun _ : Fin 1=>old)+(L.parentPhase w).ticks+DescentOperandFamilyBook.ticks L.fields 1 L.width L.afterLanes
def mid {w : ℕ} (old : Expr) (m : Memory w) :=
  (L.parentPhase w).image (DescentResetStemProjectExpr.image L.base L.actors L.groups L.blocks L.width L.beforeLanes L.afterLanes
    (fun _ : Fin 1=>old) m)
def image {w : ℕ} (old : Expr) (m : Memory w) :=DescentOperandFamilyBook.image L.field L.afterLanes L.tableBase (L.mid old m)

theorem src_work (i : Fin L.fields) (x : Fin L.blocks) : (L.src i x).work≤55 := by
  apply DescentOperandFamilyBook.expr_work L.field L.afterLanes L.tableBase i _ 30
  exact fun _=>le_of_eq (DescentResetStemChipProjection.source_work ..)

theorem extent :
    L.endAddress = L.base+({L with base:=0}).endAddress := by
  unfold endAddress tableBase prefixEnd DescentOperandFamilyBook.endAddress
  rw [DescentResetStemProject.extent L.base]
  simp [width,Nat.add_assoc]

theorem base_le : L.base≤L.endAddress:=by rw [L.extent];exact Nat.le_add_right ..

theorem table_le : L.tableBase≤L.endAddress:=Nat.le_add_right ..

set_option maxHeartbeats 1600000 in
theorem any {w : ℕ} (old : Expr) (m : Memory w) (hm : 0<L.afterLanes) (hx : 0<L.blocks)
    (fit : old.Fits w L.base) (room : L.endAddress<2^w) :
    (L.program old w).Exec m (L.image old m) (L.clock old w) ∧ CheapCode (L.program old w) ∧
      ∀z,z<L.base ∨ L.endAddress≤z→L.image old m z=m z := by
  let p:=DescentResetStemProjectExpr.program L.base L.actors L.groups L.blocks L.width L.beforeLanes L.afterLanes
    (fun _ : Fin 1=>old) w
  have a : L.base≤L.prefixEnd:=by unfold prefixEnd;rw [DescentResetStemProject.extent];omega
  have b : L.prefixEnd≤L.tableBase:=Nat.le_add_right ..
  have c:=L.table_le
  let input := fun _ : Fin 1 => old
  let projected := DescentResetStemProjectExpr.image L.base L.actors L.groups L.blocks L.width
    L.beforeLanes L.afterLanes input m
  let projectionTicks := DescentResetStemProjectExpr.ticks L.base L.actors L.groups L.blocks L.width
    L.beforeLanes L.afterLanes input
  let parent := L.parentPhase w
  let book := DescentOperandFamilyBook.program L.field L.afterLanes L.tableBase w
  obtain ⟨first, firstFrame, firstCheap⟩ := DescentResetStemProjectExpr.any L.base L.actors
    L.groups L.blocks L.width L.beforeLanes L.afterLanes input m hm hx (fun _ => fit)
    ((b.trans c).trans_lt room)
  obtain ⟨middle, _, middleFrame⟩ := DescentResetStemKeyReindex.run (base:=L.prefixEnd)
    (H₀:=L.actors) (H₁:=L.receivers) (G:=L.groups) (M:=L.afterLanes) projected (c.trans_lt room)
  obtain ⟨last, lastCheap, lastFrame, _⟩ := DescentOperandFamilyBook.any L.field
    L.afterLanes L.tableBase (L.mid old m) room
  have runMid : (p.seq parent.program).Exec m (L.mid old m) (projectionTicks+parent.ticks) :=
    @Procedure.Exec.then w p parent.program m projected (L.mid old m) projectionTicks parent.ticks
      (@first) (@middle)
  refine ⟨@Procedure.Exec.then w (p.seq parent.program) book m (L.mid old m) (L.image old m)
      (projectionTicks+parent.ticks) (DescentOperandFamilyBook.ticks L.fields 1 L.width L.afterLanes)
      (@runMid) (@last),
    @cheap_seq w (p.seq parent.program) book
      (@cheap_seq w p parent.program (@firstCheap) parent.cheap) (@lastCheap), ?_⟩
  rintro z (before|after_)
  · exact (lastFrame z (.inl (before.trans_le (a.trans b)))).trans
      ((middleFrame z (.inl (before.trans_le a))).trans (firstFrame z (.inl before)))
  · exact (lastFrame z (.inr after_)).trans
      ((middleFrame z (.inr (c.trans after_))).trans (firstFrame z (.inr ((b.trans c).trans after_))))

set_option maxHeartbeats 1600000 in
theorem run {w : ℕ} (old : Expr) (m : Memory w)
    (value : Fin L.actors→Fin (L.groups*L.blocks)→Fin L.fields→Cell L.bits)
    (owner : Fin L.receivers→Fin L.actors) (ha : 0<L.beforeLanes) (hb : 0<L.afterLanes) (hx : 0<L.blocks)
    (fits : old.Fits w L.base)
    (stored : Source old (fun h g=>encode L.bits L.fields (value h g)) L.beforeLanes m)
    (directory : DescentResetStemKeyReindex.Directory L.parent owner m) (prior : L.parent+span L.receivers≤L.base)
    (room : L.endAddress<2^w) :
    (L.program old w).Exec m (L.image old m) (L.clock old w) ∧ CheapCode (L.program old w) ∧
      (∀j x,(L.src j x).Fits w L.endAddress ∧ Source (L.src j x)
        (fun h g=>value (owner h) (finProdFinEquiv (g,x)) j) L.afterLanes (L.image old m)) ∧
      ∀z,z<L.base ∨ L.endAddress≤z→L.image old m z=m z := by
  let packet:=fun (_ : Fin 1) h g=>encode L.bits L.fields (value h g)
  have next : L.tableBase≤L.endAddress:=Nat.le_add_right ..
  obtain ⟨clocked, cheap, frame⟩ := L.any old m hb hx fits room
  obtain ⟨_, _, projected, _⟩ := DescentResetStemChipProjection.project (Q:=1) (oldH:=L.actors)
    (newH:=L.receivers) (groups:=L.groups) (X:=L.blocks) (b:=L.width)
    (srcM:=L.beforeLanes) (M:=L.afterLanes) L.base L.parent (fun _ : Fin 1 => old)
    packet owner m ha hb hx (fun _ => fits) (fun _ => stored) directory prior (next.trans_lt room)
  refine ⟨@clocked, @cheap, ?_, frame⟩
  intro j x
  have data := projected 0 x
  have outputs := DescentOperandFamilyBook.issued L.field L.field_zero
    (H:=L.receivers) (G:=L.groups) L.afterLanes L.tableBase j
    (fun _ : Fin 1 => L.packets x) (L.mid old m)
    (fun h g _ => encode L.bits L.fields (value (owner h) (finProdFinEquiv (g,x))))
    (fun _ => data.1) (fun _ => data.2) room
  simpa only [src,field,Equiv.symm_apply_apply,image,endAddress] using outputs


end Layout
end
end Hierarchy.DescentOperandRootPull

end OAI
