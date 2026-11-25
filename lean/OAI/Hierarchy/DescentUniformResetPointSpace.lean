import OAI.Hierarchy.DescentResetAreaPoint
import OAI.Hierarchy.DescentUniformRootSpace
import OAI.Hierarchy.DescentUniformMiddleRegions
import OAI.Hierarchy.DescentUniformFundedRoom
import OAI.Hierarchy.DescentUniformOperandSetup
import OAI.Hierarchy.DescentUniformResetVenue
import OAI.Hierarchy.DescentUniformPublishedRegisters

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset D drift : ℕ) {ι : ℕ→Type*}
    (tailCost chosenJ sites age size degree root previous nextM base : ∀h,ι h→ℕ)
    (old : ∀h,ι h→Prior)
local notation "sample" h:arg i:arg => originalSample G op t f g reset (tailCost h i) D drift (chosenJ h i)
  (sites h i) (age h i) (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i)
  (base h i) (old h i)
local notation "z" => fun h i=>sample h i
local notation "out_" => fun h i=>(sample h i).output G board D f g op.C op.w

local notation "S_" h:arg i:arg => (sample h i).sched
local notation "k_" h:arg i:arg => (sample h i).k
local notation "tail_" h:arg i:arg => (sample h i).tail
local notation "c_" h:arg i:arg => (S_ h i).groupWidth (k_ h i) (tail_ h i) (age h i)
/-- A single numerical address proof over an index containing unrelated
calendars, heights and previous register images. -/
theorem uniform_point_space (a : ∀h,ι h→PhysicalReset) (floor : ∀h,ι h→ℕ)
    (entry : EntranceRoom a floor)
    (point : ∀h i,AreaPoint G board D f g op.C op.w h (sample h i) (old h i) (a h i) (floor h i))
    (before : ∀h i,age h i<(S_ h i).length)
    (host : ∀h i,(old h i).venue.hosts=(S_ h i).hostSize (age h i))
    (group : ∀h i,(old h i).venue.groups=(S_ h i).groupCount (age h i))
    (block : ∀h i,(old h i).venue.k=k_ h i) :
    PhysicalReset.ScalarRoom a (fun h i=>(a h i).stageStart (floor h i)) :=by
  let p:=out_
  have level : ∀ᶠ h:ℕ in atTop,id h≤h:=Eventually.of_forall fun _=>le_rfl
  have cal:=CalendarInputs.of_local_numbers G board D f g op.C op.w z
    (fun h i=>(point h i).localNumbers) (fun h i=>(point h i).fibres)
  have priced : Installed p:=Eventually.of_forall fun h i=>(point h i).installed
  have date (h : ℕ) (i : ι h) :=(point h i).layout
  have payload (h : ℕ) (i : ι h) :=(point h i).payload
  have oldH : Bounded fun h i=>(S_ h i).hostSize (age h i):=
    ⟨3,Eventually.of_forall fun h i=>(point h i).oldHost⟩
  have newH : Bounded fun h i=>(S_ h i).hostSize (age h i+1):=
    ⟨3,Eventually.of_forall fun h i=>(point h i).newHost⟩
  have matrices : Bounded fun h i=>2^((c_ h i+k_ h i)*(c_ h i+k_ h i)) :=
    Bounded.pow_of_linear (K:=1) (Eventually.of_forall fun h i=>by
      simp only [Nat.one_mul]
      exact (point h i).matrix.trans (Nat.div_le_self ..))
  have oldG : Bounded fun h i=>2^(c_ h i) := matrices.of_le fun h i=>
    Nat.pow_le_pow_right (by decide) ((Nat.le_add_right ..).trans (Nat.le_mul_self _))
  have newG : Bounded fun h i=>(S_ h i).groupCount (age h i+1) :=oldG.of_le fun h i=>by
    rw [←(S_ h i).group_power (k:=k_ h i) rfl rfl (age h i+1)]
    apply Nat.pow_le_pow_right (by decide)
    unfold AtomSchedule.groupWidth
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (Nat.le_succ _) _)) _
  have M : Bounded fun h i=>2^(root h i) := oldG.of_le fun h i=>
    Nat.pow_le_pow_right (by decide) ((point h i).cuts.1.trans (point h i).cuts.2)
  have heightRoom : Bounded (fun h (_:ι h)=>h):=
    ⟨1,Eventually.of_forall fun h _=>by simpa only [Nat.one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have m:=uniform_middle G board op t f g reset D drift id tailCost chosenJ sites age size degree root previous nextM base old cal level oldH oldG
    (fun h i=>(point h i).cuts) (Eventually.of_forall fun h i=>(point h i).matrix)
    (Eventually.of_forall fun h i=>(point h i).previousKey) priced
  obtain ⟨front,contacts,private_,sheets,actor⟩:=uniform_region_rooms G board op t f g reset D drift id tailCost chosenJ sites age size degree root previous nextM base old cal level oldH newH oldG newG M matrices priced
  have saved:=uniform_published G board op t f g reset D drift id tailCost chosenJ sites age size degree root previous nextM base old cal level oldH newH newG M priced
  obtain ⟨setup,role⟩:=uniform_operand_setup G board op t f g reset D drift id tailCost chosenJ sites age size degree root previous nextM base old cal level oldH newH oldG newG M matrices before
    (Eventually.of_forall fun h i=>(point h i).oldCaps)
    (heightRoom.of_le fun h i=>(point h i).operandLanes) (heightRoom.of_le fun h i=>(point h i).roleLanes)
    (Eventually.of_forall fun h i=>(point h i).archive) (Eventually.of_forall fun h i=>(point h i).selected) priced
  have fund:=uniform_funded_room G board op t f g reset D drift tailCost chosenJ sites age size degree root previous nextM base old oldH
    (oldG.of_le fun h i=>((S_ h i).group_power (k:=k_ h i) rfl rfl (age h i)).ge) matrices
    (fun h i=>(point h i).cuts.1.trans (point h i).cuts.2) host group block
    (Eventually.of_forall fun h i=>(point h i).paid) priced
  have venue:=uniform_venue_room G board op t f g reset D drift id tailCost chosenJ sites age size degree root previous nextM base old cal level oldH newH oldG newG M host block priced
    ⟨1,Eventually.of_forall fun h i=>by
      simp only [Nat.one_mul]
      exact (point h i).mask⟩
  have nodeKey : ∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;(v.nodeBits*v.nodes+v.nodeBits)*v.receiver.lanes≤h := by
    filter_upwards [priced] with h keys
    intro i
    let v := p h i
    have key : v.nodeBits * v.nodes + v.nodeBits ∈ v.receiverUnits := by simp [receiverUnits]
    exact (keys i _ (.inr key)).trans (Nat.div_le_self ..)
  constructor
  case canvas => exact entry.canvas
  case radix => exact entry.radix
  case axes => exact entry.axes
  case initialBook => exact entry.book
  case groups => exact entry.groups
  case lanes => exact entry.lanes
  case reblock => exact entry.reblock
  all_goals simp only [date]
  case setup => exact setup
  case actor => exact actor
  case jointDigits => exact saved.jointDigits
  case privateViews => exact private_
  case contactOutput => exact contacts
  case candidatesFront => exact front
  case candidatesSheets => exact sheets
  case weighted => exact m.stencil
  case oldBlocks => exact m.blocks
  case signedLanes => exact m.lanes
  case signedRatio => exact m.ratio
  case signedPorts => exact m.ports
  case signedHosts => exact m.hosts
  case signedDimension => exact m.dimension
  case signedHigh => exact m.high
  case signedWord => simp only [payload]; exact m.word
  case signedMatrix => simp only [payload]; exact m.matrix
  case rootGroups => exact m.rootGroups
  case rootShapes => exact m.shapes
  case rootField => exact m.field
  case rootLawWidth => exact m.law
  case blocks => exact sheets.blocks
  case capacity => exact saved.cap
  case packedLanes => exact sheets.lanes
  case receiverHosts => exact sheets.hosts
  case receiverGroups => exact sheets.groups
  case candidates => exact sheets.candidates
  case «fields» => exact saved.fields
  case argumentSlots => exact saved.arguments
  case transfer => exact role
  case birth => exact saved.birth
  case primitive => exact saved.primitive
  case metadata => exact saved.metadata
  case funded => exact fund
  case venue => exact venue
  case rotorBins => exact Bounded.const (ι:=ι) (2^n)
  case degrees => exact Bounded.const (ι:=ι) D
  case nodes => exact cal.nodes.bounded level
  case controlDigits =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.controlDigits
  case rankKey =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.rankKey
  case nodeKey =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact nodeKey
  case keepDigits =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.keepDigits
  case dictionaries =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.dictionaries
  case retileKey =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact m.retile.mono fun h word i => (word i).trans (Nat.div_le_self ..)
  case rootHosts => exact m.hosts
  case rootLanes => exact sheets.lanes
  case rootBlocks => exact sheets.blocks

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
