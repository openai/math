import OAI.Hierarchy.DescentPhysicalResetLeft
import OAI.Hierarchy.DescentPhysicalResetReceipt

namespace OAI
/-! # Address space for the original rotation and its selected output page -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.PackedFlow DescentPackedWalsh DescentGLPacked
open DescentGLPacked.BankImage DescentGLPacked.BankImage.Dated DescentSIMDLookup DescentGL
open DescentPlainTerminal.Suffix DescentGLNielsen ProtocolRAM ThreeFlat.RAM
open ThreeFlat.Routing CallPool
noncomputable section
set_option quotPrecheck false
section PhysicalBounds
variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ)
local notation "P" => a.stencilPhase sh floor count hub g Y
local notation "p" => a.chart floor
local notation "E" => a.estimator floor
local notation "d" => a.high+a.low
local notation "hrows" => (p).routedHosts
local notation "chart₀" => (P).chart

private theorem pointer_before_output {k base : ℕ} (i : Fin k) :
    PhysicalTrajectory.pointer k base i.val < PhysicalTrajectory.outputBase k base :=by
  have step:=(Nat.mul_le_mul_right (3*2^k+1) (Nat.succ_le_of_lt i.isLt))
  rw [Nat.succ_mul] at step
  unfold PhysicalTrajectory.pointer PhysicalTrajectory.outputBase RowStageRAM.placed
  dsimp only
  omega

/-- The true contact pages and the original host page lie in the estimator's
immutable prefix, before every one of the later remixed columns. -/
theorem stencil_original_banks (bound : (E).endAddress<2^w) :
    (P).counts.Fits w (P).origin ∧ ∀i,((P).peers i).Fits w (P).origin :=by
  have stops:=(p).stops
  obtain ⟨early,first,totals,scratch,header,depth,gain⟩:=stops
  have span₀:=(p).estimator_range a.payload a.gain a.positive
  have held : (p).endAddress≤(E).endAddress:=span₀.1.trans span₀.2.1
  have old : (p).totals≤(p).endAddress:=by omega
  have cap : (p).first+DescentPackedWalsh.page a.hosts a.high≤(E).endAddress:=by
    have one:=Nat.mul_le_mul_right (DescentPackedWalsh.page a.hosts a.high) (Nat.succ_le_succ (Nat.zero_le d))
    rw [Nat.one_mul] at one
    exact ((Nat.add_le_add_left one (p).first).trans first).trans (old.trans held)
  constructor
  · apply DescentSixParty.PackedFlow.Canvas.Placement.fitsOf _ _ bound
    exact cap
  · intro j
    apply DescentSixParty.PackedFlow.Canvas.Placement.fitsOf _ _ bound
    have index : j.val<a.ports:=j.isLt.trans_le sh.ports.le
    have step:=Nat.mul_le_mul_right (a.flow floor).pitch (Nat.succ_le_of_lt index)
    rw [Nat.succ_mul] at step
    change (p).middle+j.val*(a.flow floor).pitch+(a.flow floor).pitch≤(E).endAddress
    have upto : (p).middle+a.ports*(a.flow floor).pitch≤(p).first:=early
    omega

/-- The actual final rotation page still lies below the saved-basis location, including the
zero-step rotation. Its row capacity is the entire high Walsh plane. -/
theorem stencil_chosen_chip (saveRoom : (P).first<2^w)
    (area : Size (chart₀) hrows a.high a.low a.bits w) :
    (P).chip.Fits w (P).fresh ∧ hrows*2^a.high≤(P).chip.size :=by
  have lower : (P).fresh≤(P).first:=by unfold PackedFlow.ResetMiddle.first PackedFlow.ResetMiddle.saved;omega
  have cutoff:=(lower.trans_lt saveRoom)
  cases steps : (P).stages with
  | zero =>
    have chip : (P).chip=(chart₀).input:=by rw [PackedFlow.ResetMiddle.chip,steps];rfl
    rw [chip]
    obtain ⟨_,_,edge⟩:=area.input
    have here : (chart₀).start≤(P).fresh:=by
      change (chart₀).start≤((chart₀).start+6*(schedule d).length*(chart₀).page)+_
      omega
    exact ⟨DescentSixParty.PackedFlow.Canvas.Placement.fitsOf _ (edge.trans here) cutoff,area.inputSize⟩
  | succ n =>
    have chip : (P).chip=⟨(chart₀).heap d+n*(chart₀).page,(chart₀).bits⟩:=by
      rw [PackedFlow.ResetMiddle.chip,steps];rfl
    rw [chip]
    refine ⟨DescentSixParty.PackedFlow.Canvas.Placement.fitsOf _ ?_ cutoff,area.rows⟩
    change (chart₀).heap d+n*(chart₀).page+(chart₀).page≤(chart₀).heap d+((P).stages+1)*(chart₀).page
    rw [steps,Nat.succ_mul,Nat.succ_mul];omega

theorem stencil_native_room
    (cut : (P).S.c≤a.high+a.re+a.e) (endRoom : (P).endAddress<2^w)
    (operands : StencilBook.Geometry (P).S (P).X (P).base (P).bank w)
    (short : (P).S.M*max ((P).S.n*Stencil.count (P).S.r ((P).S.degree+(P).S.degree))
      ((P).S.t*2^(P).S.r)≤w/2) (word : (P).S.n*(P).S.M≤w) : (P).Room w :=by
  have firstBase : (P).first≤(P).base:=by unfold PackedFlow.ResetMiddle.base Subwords.finish Subwords.destination;omega
  have baseEnd : (P).base ≤ (P).endAddress := by
    rw [PackedFlow.ResetMiddle.endAddress, (P).S.extent]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  have firstRoom:=firstBase.trans_lt (baseEnd.trans_lt endRoom)
  have freshRoom : (P).fresh<2^w:=by
    have ff : (P).fresh≤(P).first:=by unfold PackedFlow.ResetMiddle.first PackedFlow.ResetMiddle.saved;omega
    exact ff.trans_lt firstRoom
  have originFresh : (E).endAddress≤(P).fresh:=((p).estimator_range a.payload a.gain a.positive).2.2
  have original:=a.stencil_original_banks sh floor count hub g Y w (originFresh.trans_lt freshRoom)
  have sized:=BankImage.Dated.sized (E).endAddress hrows a.high a.low a.bits w freshRoom
  obtain ⟨area,words,fence,power,offsets,switches,planes⟩:=sized
  have countSize : (P).sheets=hrows:=by
    change ((1+a.successor.middle.stencil.maxPorts)+a.successor.middle.stencil.m)*a.successor.middle.stencil.hosts=((1+a.ports)+d)*a.hosts
    rw [sh.ports,sh.dimension,sh.hosts]
  have ef : (P).first<2^w:=firstRoom
  have afterFresh : (P).fresh≤(P).first:=by unfold PackedFlow.ResetMiddle.first PackedFlow.ResetMiddle.saved;omega
  obtain ⟨chosenFit,chosenRoom⟩:=a.stencil_chosen_chip sh floor count hub g Y w ef area
  have chips : (P).chip.Fits w (P).first ∧ hrows*2^a.high≤(P).chip.size :=
    ⟨⟨chosenFit.1,chosenFit.2.1,chosenFit.2.2.trans afterFresh⟩,chosenRoom⟩
  have span : chunks (2^(P).S.c) ((P).ratio*(P).S.M)≤2^a.high :=by
    apply (ceilDiv_le_iff_le_mul (Nat.mul_pos (P).ratioPos (P).batchPos)).2
    change 2 ^ a.successor.middle.stencil.c ≤ (2 ^ a.re * a.successor.middle.stencil.M) * 2 ^ a.high
    change a.successor.middle.stencil.c ≤ a.high + a.re + a.e at cut
    rw [sh.lanes,←pow_add,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨le_rfl,original.1,original.2,?_,words,fence,power,offsets,switches,planes,?_,firstRoom,
    chips.1,?_,baseEnd.trans_lt endRoom,operands,endRoom,short,word⟩
  · change Size (chart₀) (((1+a.successor.middle.stencil.maxPorts)+d)*a.successor.middle.stencil.hosts)
      a.high a.low a.successor.middle.stencil.b w
    rw [sh.ports,sh.hosts,sh.bits]
    exact area
  · intro i
    exact (pointer_before_output (base:=(E).solveAt) i).trans_le
      (((Nat.le_add_right ..) : PhysicalTrajectory.outputBase d (E).solveAt≤(E).endAddress).trans originFresh)
  · rw [countSize]
    exact (Nat.mul_le_mul_left hrows span).trans chips.2

end PhysicalBounds

/-- Every public calendar uses the selected high Walsh digit count and the
ratio/lanes split of the same low count. -/
theorem calendar_chip_cut (S : DescentCompiler.AtomSchedule) (k tail age radix p f degree payload e n t : ℕ)
    (calendar : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank) (out : ResetOutput) :
    let a:=fromCalendar S k tail age radix p f degree payload e n t calendar addr roster out
    a.successor.middle.stencil.c≤a.high+a.re+a.e :=by
  let dim:=S.groupWidth k tail age+k
  dsimp only
  change S.groupWidth k tail age≤(dim-_)+(_-k-e)+e
  dsimp only [dim]
  omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
