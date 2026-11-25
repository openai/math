import OAI.Hierarchy.DescentRegisteredResetHeaders
import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentCalendarPrimaryPrivateKeys

namespace OAI
/-! # Original operand coordinates at a registered reset row -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentDatedAddressBook
open DescentLocalPrivateNames DescentPrimitivePalette DescentDatedPriorOperand DescentRetainedRangeDigits
open DescentOperandStateBanks RegisterTimeline
open scoped Classical Fin.CommRing

noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentPacking.PackedMatch.Local.Stage
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
    {q ε:ℝ} {S:AtomSchedule} {k age grain degree wire hist p R:ℕ}
    (r:Reached W G q ε S k age grain degree wire hist) (B:BitDescription W) (number:Local B)
    (shape:WorldShape p R B) (hp:0<p)

/-- The ordinary argument denoted by the registered flattened operand number. -/
def registeredMouth (y:NodeOrder.All B) (index:ℕ) (active:index<(occurrences (shape.sites y.1) y.2).length) :
    DescentLocalPrivateNames.Slot ((shape.sites y.1).recipe hp) :=
  ⟨y.2,⟨index,by simpa only [DescentRetainedRangeDigits.length _ _ hp] using active⟩⟩

variable {a:PhysicalReset} {floor w:ℕ} (u:a.DateInputs floor w)
local notation "out" => a.successor
local notation "ports" => reset a floor u
local notation "prev" => (ports).rangeLayout
local notation "next_" => (out).rangeLayout
variable (space:RangeRoom ports r B) (ok:u.Ready) (axes:prev=next_)

local notation "nodeAt_" n:arg => ((n).cast (congrArg Layout.nodes axes)).cast ok.nodes.symm
local notation "argAt_" j:arg => ((j).cast (congrArg Layout.operands axes)).cast ok.slots.symm
local notation "rackAt_" x:arg => (x).cast (congrArg Layout.blocks axes)
local notation "coord_" v:arg => Reached.NodeCells.coordinate r v

include ok axes in
/-- The original archived operand rectangle agrees with the actual posted register. -/
theorem registered_mouth_capacity : (ports).argumentsPerNode=u.operand.slots ∧ (ports).nodes=u.operand.nodes :=
  ⟨(congrArg Layout.operands axes).trans ok.slots.symm,(congrArg Layout.nodes axes).trans ok.nodes.symm⟩

include ok axes in
theorem registered_retained_capacity :
    (ports).argumentsPerNode=(out).setup.retained.args ∧ (ports).nodes=(out).setup.retained.nodes :=
  registered_mouth_capacity u ok axes

/-- Each live registered row recovers both axes of the actually issued operand.
The next node bound and fan-in bound can be any proofs of the hardware capacities. -/
theorem registered_mouth (x:Fin (prev).blocks) (j:Fin (prev).operands) (h:Fin (prev).hosts)
    (g:Fin (prev).groups) (n:Fin (prev).nodes) (y:NodeOrder.All B)
    (hit:slotAt ports r B number space x n h g=some y) (active:j.val<(occurrences (shape.sites y.1) y.2).length)
    (nodes:Fintype.card (B.recipe y.1).Node≤u.operand.nodes)
    (args:∀z,((shape.sites y.1).recipe hp).arity z≤u.operand.slots) :
    let mouth:=registeredMouth B shape hp y j.val active
    let packed:=reached_mouth _ ((number y.1).toEmbedding.trans (Fin.castLEEmb nodes)) args mouth
    let pair : Fin u.operand.nodes × Fin u.operand.slots:=finProdFinEquiv.symm packed
    argAt_ j=pair.2 ∧ nodeAt_ n=pair.1 ∧ x.val=(coord_ y.1).2.2.val ∧
      h.val=(coord_ y.1).1.val ∧ g.val=(coord_ y.1).2.1.val ∧
      ∀f₀:Fin 7,(out).operandOrdinal u.operand f₀ (argAt_ j) (rackAt_ x) (nodeAt_ n)=
        (out).operandOrdinal u.operand f₀ pair.2 (rackAt_ x) pair.1 :=by
  rcases y with ⟨v,z⟩
  obtain ⟨rowId,nodeId,hostId,groupId⟩:=slotAt_coordinates ports r B number space x n h g v z hit
  intro mouth packed pair
  have position : pair = ((number v z).castLE nodes, mouth.2.castLE (args z)) :=
    finProdFinEquiv.symm_apply_apply _
  rw [position]
  have arg:(argAt_ j).val=j.val:=rfl
  have node:(nodeAt_ n).val=(number v z).val:=congrArg (fun t:Fin (prev).nodes=>t.val) nodeId
  have ix:(argAt_ j)=(⟨j.val,by simpa only [DescentRetainedRangeDigits.length _ _ hp] using active⟩:
      Fin (((shape.sites v).recipe hp).arity z)).castLE (args z):=Fin.ext arg
  have in_:nodeAt_ n=((number v z).castLE nodes):=Fin.ext node
  exact ⟨ix,in_,congrArg (fun t:Fin (prev).blocks=>t.val) rowId,
    congrArg (fun t:Fin (prev).hosts=>t.val) hostId,congrArg (fun t:Fin (prev).groups=>t.val) groupId,
    fun f₀=>congrArg₂ (fun arg node => (out).operandOrdinal u.operand f₀ arg (rackAt_ x) node) ix in_⟩

/-- The selected recipe occurrence refers to the same chronological pointer word,
including its zero-based original argument number. -/
theorem registered_mouth_pointer (pin:P→ℕ) (y:NodeOrder.All B) (j:ℕ) (oldArgs:ℕ)
    (active:j<(occurrences (shape.sites y.1) y.2).length) :
    let mouth:=registeredMouth B shape hp y j active
    Reached.argumentPointer r B number shape hp pin oldArgs y j=
      Reached.argumentPointer r B number shape hp pin oldArgs ⟨y.1,mouth.1⟩ mouth.2.val :=by
  cases y
  rfl

include ok axes in
theorem registered_retained_pointer (pin:P→ℕ) (y:NodeOrder.All B) (j:ℕ)
    (active:j<(occurrences (shape.sites y.1) y.2).length) :
    let mouth:=registeredMouth B shape hp y j active
    Reached.argumentPointer r B number shape hp pin (ports).argumentsPerNode y j=
      Reached.argumentPointer r B number shape hp pin (out).setup.retained.args ⟨y.1,mouth.1⟩ mouth.2.val :=by
  simpa only [(registered_retained_capacity u ok axes).1] using
    (registered_mouth_pointer r B number shape hp pin y j (ports).argumentsPerNode active)

/-- A native report on the reached cell is the four-field report at the registered
row. Both sides select the very same ordinal from the funded reset scanner. -/
theorem registered_mouth_amount (small:2*(out).receiver.candidates<2^(out).receiver.queryBits)
    (actor:Computability.VPVNP.BurstRAM.Memory w) (choice:∀i,OrdinalRead u ok small actor i) (pin:P→ℕ)
    (x:Fin (prev).blocks) (j:Fin (prev).operands) (h:Fin (prev).hosts)
    (g:Fin (prev).groups) (n:Fin (prev).nodes) (y:NodeOrder.All B)
    (hit:slotAt ports r B number space x n h g=some y) (active:j.val<(occurrences (shape.sites y.1) y.2).length)
    (nodes:Fintype.card (B.recipe y.1).Node≤u.operand.nodes)
    (args:∀z,((shape.sites y.1).recipe hp).arity z≤u.operand.slots)
    (reported:
      let mouth:=registeredMouth B shape hp y j.val active
      let packed:=reached_mouth _ ((number y.1).toEmbedding.trans (Fin.castLEEmb nodes)) args mouth
      let pair:Fin u.operand.nodes × Fin u.operand.slots:=finProdFinEquiv.symm packed
      ∀f₀:Fin 4,((choice ((out).operandOrdinal u.operand (f₀.castLE (by decide)) pair.2 (rackAt_ x) pair.1)).amount
        (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=
          (Reached.argumentPointer r B number shape hp pin (out).setup.retained.args ⟨y.1,mouth.1⟩ mouth.2.val).header f₀) :
    ∀f₀:Fin 4,((choice ((out).operandOrdinal u.operand (f₀.castLE (by decide)) (argAt_ j) (rackAt_ x) (nodeAt_ n))).amount
      (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=
          (Reached.argumentPointer r B number shape hp pin (ports).argumentsPerNode y j.val).header f₀:=by
  intro f₀
  have same:=registered_mouth r B number shape hp u space ok axes x j h g n y hit active nodes args
  have pointer:=registered_retained_pointer r B number shape hp u ok axes pin y j.val active
  exact (congrArg (fun i:Fin (out).receiver.fields=>
    ((choice i).amount (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val)
    (same.2.2.2.2.2 (f₀.castLE (by decide)))).trans
      ((reported f₀).trans (congrArg (fun t:Pointer=>t.header f₀) pointer.symm))

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
