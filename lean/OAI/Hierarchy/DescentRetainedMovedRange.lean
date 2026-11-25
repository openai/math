import OAI.Hierarchy.DescentResetOperandMovedSources
import OAI.Hierarchy.DescentPhysicalOperandSelection
import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentRetainedControlWord

namespace OAI
/-! # A native home-filtered primary row carries the original three slice fields -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSIMDLookup DescentPackedZip DescentRetainedControl DescentRotorWindowArchive
open DescentResetOperandSetup.Chart ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)
local notation "L" => C.retained
variable (which : C.seven.control.Targets) (X : C.seven.Packets) (panels : C.retained.Strips)
variable (t : Fin C.placement.shapes) (h : Fin C.retained.hosts) (g : Fin C.retained.grouped)
local notation "unpack" => (encode C.seven.packetBits (count C.seven.degree (L).donors C.seven.capacity)).symm (X h g)
def ownerAt (d : Fin (L).donors) : Bool :=
  decide (which t=some (((unpack) (ix (.inl (.inl (.inl d))))).val/2))
def priorAt (a b : Fin (L).donors) : Bool :=
  decide (((unpack) (ix (.inr (.inl (a,b))))).val≠0)
local notation "accept" => ownerAt C which X t h g
local notation "prior" => priorAt C X h g
local notation "before" => (L).site panels h g
local notation "out" => (L).routedWord accept prior before

theorem decoded_output (mode : Fin 2) (f : Fin 7) (operand : Fin (L).args) (slot : Fin (L).nodes) :
    C.seven.decoded which X panels ((L).outputID mode f operand slot) t h g =
      (L).decodeDigit ((L).site (C.seven.stripes which X panels t) h g) mode f operand slot := by
  let z : Fin ((2*7*(L).args)*(L).nodes) :=
    finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (mode,f),operand),slot)
  have index : (finSumFinEquiv.symm ((L).outputID mode f operand slot) :
      Fin ((2*7*(L).args)*(L).nodes) ⊕ Fin (L).nodes) = .inl z :=
    finSumFinEquiv.symm_apply_apply _
  unfold DescentRetainedSeven.Chart.decoded DescentResetRetainedSetup.Layout.function
  erw [index]
  dsimp only [z]
  erw [finProdFinEquiv.symm_apply_apply,finProdFinEquiv.symm_apply_apply,finProdFinEquiv.symm_apply_apply]
  rfl

/-- Both predicates are the actual just-read packet comparators. The position is the sum of
accepted original nodes, followed by the retained node's original number. -/
theorem decoded_range (mode : Fin 2) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior d=(order d).val) (d : Fin (L).donors)
    (n : Fin (L).previousNodes) (arg : Fin (L).previousArgs) (active : accept d=true)
    (valid : n.val<(L).originalCount before d) (present : arg.val<((L).entry before d n (L).arityField).val)
    (slot : Fin (L).nodes) (number : slot.val=(L).offset out (order d)+n.val)
    (operand : Fin (L).args) (same : operand.val=arg.val) (f : Fin 3) :
    C.seven.decoded which X panels ((L).outputID mode (page f) operand slot) t h g=
      (L).entry before d n ((L).operandField (page f) arg) := by
  have socket : C.seven.roster which X t h g=vector accept prior:=rfl
  have word_ : (L).site (C.seven.stripes which X panels t) h g=out := by
    unfold DescentResetRetainedSetup.Layout.site DescentRetainedSeven.Chart.stripes
    simp only [socket]
    exact joined _ _ _ order rank _
  rw [decoded_output,word_]
  simp only [DescentResetRetainedSetup.Layout.decodeDigit,
    show 4≤(page f).val from Nat.le_add_right ..,true_or,or_true,ite_true,number,same]
  exact (L).routed_old_field accept prior order (fun x=>rank x) before d n arg (page f) active valid present

section PhysicalWord
variable {w U : ℕ} (base : ℕ) (s : C.Sources) (name : Fin U→Fin C.placement.sparse) (memory : Memory w)
variable (host : C.placement.oldHosts=C.retained.hosts) (group : C.placement.groups*C.placement.blocks=C.retained.grouped)
variable (signed : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits)
local notation "Y" => fun z : Fin ((L).outputs*C.placement.shapes) =>
  let pair:=finProdFinEquiv.symm z
  reindexed host group (C.seven.decoded s.which X panels pair.1 pair.2)
variable (moved : C.Moved base s name memory (fun z : Fin (C.retained.outputs*C.placement.shapes) =>
  let pair:=finProdFinEquiv.symm z
  reindexed host group (C.seven.decoded s.which X panels pair.1 pair.2)) signed)
variable (block : Fin C.placement.blocks) (rack : Fin C.placement.newHosts) (group_ : Fin C.placement.groups)
variable (alive : rack.val<U)
local notation "sparse" => name ⟨rack.val,alive⟩
local notation "shp" => C.placement.shape sparse
local notation "prev" => (C.placement.previous sparse).cast host
local notation "coordinate" => (finProdFinEquiv (group_,block)).cast group
local notation "take_" => ownerAt C s.which X shp prev coordinate
local notation "prior_" => priorAt C X prev coordinate
local notation "original" => (L).site panels prev coordinate
local notation "restored" => (L).routedWord take_ prior_ original

include moved in
theorem moved_scalar (key : Fin (L).outputs) (primary : s.primary shp=true)
    (chunk : Fin (chunks C.placement.groups C.lanes)) (lane : Fin C.lanes)
    (atGroup : chunk.val*C.lanes+lane.val=group_.val) (room : (L).bits*C.lanes≤w) :
    let expr:=C.oldField base block key
    let row_:=row C.placement.newHosts C.placement.groups C.lanes (rack,chunk)
    let seen:Cell ((L).bits*C.lanes):=((expr.eval memory (row_.val:Word w)).val:ℕ)
    (encode (L).bits C.lanes).symm seen lane=C.seven.decoded s.which X panels key shp prev coordinate := by
  intro expr row_ seen
  let table:=DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch s.primary name Y key block
  have source : Source expr table C.lanes memory:=moved.retained key block
  have eqn:=source (rack,chunk)
  have small : (data table (rack,chunk)).val<2^w :=
    (data table (rack,chunk)).isLt.trans_le (Nat.pow_le_pow_right (by decide) room)
  have packed : seen=data table (rack,chunk) := by
    apply Fin.ext
    change (expr.eval memory _).val%2^((L).bits*C.lanes)=_
    rw [eqn,Fin.val_cast_of_lt small]
    exact Nat.mod_eq_of_lt (data table (rack,chunk)).isLt
  rw [packed]
  change (encode C.seven.batch.bits C.lanes).symm (data table (rack,chunk)) lane = _
  simp only [data,Equiv.symm_apply_apply]
  have live : chunk.val*C.lanes+lane.val<C.placement.groups:=atGroup.trans_lt group_.isLt
  rw [dite_eq_left live]
  have grouped : (⟨chunk.val*C.lanes+lane.val,live⟩:Fin C.placement.groups)=group_:=Fin.ext atGroup
  rw [grouped]
  change DescentResetDenseOperand.dense name _ rack group_=_
  simp only [DescentResetDenseOperand.dense,alive,dite_eq_left,DescentRetainedTargetPlacement.Chart.selected,
    primary,reindexed]
  erw [ite_true,finProdFinEquiv.symm_apply_apply]
  rfl

include moved in
/-- The observed `oldField` operand of the real moved sheet, unpacked at the live SIMD
lane and retained node. Under the home claim the byte equals its unfiltered source field. -/
theorem moved_range (mode : Fin 2) (primary : s.primary shp=true) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior_ d=(order d).val) (d : Fin (L).donors) (n : Fin (L).previousNodes)
    (arg : Fin (L).previousArgs) (elected : take_ d=true) (valid : n.val<(L).originalCount original d)
    (present : arg.val<((L).entry original d n (L).arityField).val) (slot : Fin (L).nodes)
    (number : slot.val=(L).offset restored (order d)+n.val) (operand : Fin (L).args) (same : operand.val=arg.val)
    (f : Fin 3) (chunk : Fin (chunks C.placement.groups C.lanes)) (lane : Fin C.lanes)
    (atGroup : chunk.val*C.lanes+lane.val=group_.val) (room : (L).bits*C.lanes≤w) :
    let expr:=C.oldField base block ((L).outputID mode (page f) operand slot)
    let row_:=row C.placement.newHosts C.placement.groups C.lanes (rack,chunk)
    let seen:Cell ((L).bits*C.lanes):=((expr.eval memory (row_.val:Word w)).val:ℕ)
    (encode (L).bits C.lanes).symm seen lane=(L).entry original d n ((L).operandField (page f) arg) := by
  exact (moved_scalar C X panels base s name memory host group signed moved block rack group_ alive
    ((L).outputID mode (page f) operand slot) primary chunk lane atGroup room).trans
    (decoded_range C s.which X panels shp prev coordinate mode order rank d n arg elected valid present slot number operand same f)

end PhysicalWord
end
end Hierarchy.DescentRetainedRangeDigits

end OAI
