import OAI.Hierarchy.DescentPhysicalOperandMenu
import OAI.Hierarchy.DescentPreparedOperandPairRead
import OAI.Hierarchy.DescentPreparedSavedRegister
import OAI.Hierarchy.DescentResetPrefixRoom
import OAI.Hierarchy.DescentResetPriorRegisterRoom

namespace OAI
/-! # Original reset operands fit at the chronological input of the receiver -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentSixParty DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentOperandRootPull DescentDyadicSpan DescentResetOperandSetup ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (m : OperandMenu z roots)
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ)
local notation "v" => a.successor
local notation "B" => (v).middle
local notation "C" => (v).setup
local notation "RC" => a.rootPhase sh floor count hub g Y roots w
local notation "book" => atlasBook z sh floor count hub g Y roots w
local notation "b₀" => a.rebased floor
local notation "A₀" => (v).operandFloor b₀
local notation "dir" => (v).actor.directory ((B).stop b₀)

/-- Only physical end addresses and the original prepared root book are needed.
The same instance includes the two rooted packet operands, the earlier saved
permutation, both compact-directory registers, and the original signed windows. -/
theorem setup_ready (safe : (RC).PreparedFits book) (held : (RC).preparedEnd book≤A₀)
    (directory : (dir).endAddress≤A₀) (rootRoom : A₀<2^w)
    (roles : (C).retained.priorMetaLimit m.initial m.previousMeta≤A₀)
    (args : (C).retained.priorOperandLimit m.previousArguments≤A₀)
    (ptr receivers groups blocks pitch : ℕ)
    (pair : (C).packets=preparedPair (RC) book ptr receivers groups blocks pitch)
    (shape : groups*blocks=2^(B).stencil.c) (parent : ptr+span receivers≤A₀)
    (positive : 0<pitch) (someBlocks : 0<blocks)
    (lanes : 0<(C).lanes) (placedBlocks : 0<(C).placement.blocks) :
    (C).Ready (m.banks sh floor count hub g Y w) w A₀ :=by
  have widen {s : Bank} {old new : ℕ} (bounded : s.Fits w old) (before : old≤new) :
      s.Fits w new:=⟨bounded.1,bounded.2.1,bounded.2.2.trans before⟩
  obtain ⟨left,center,right⟩:=(C).before A₀
  have start : A₀≤(C).placed A₀:=(left.trans center).trans right
  have h:=(book).limits (RC).projectionEnd (B).signedHosts (2^(B).stencil.c) (B).signedLanes
  have head : (RC).projectionEnd≤(RC).headerEnd book:=h.1.trans (h.2.1.trans h.2.2)
  have endAt:(RC).headerEnd book≤(RC).preparedEnd book:=Nat.le_add_right ..
  have pro : (RC).projectionEnd≤A₀ :=head.trans (endAt.trans held)
  have fits:=(dir).fits (directory.trans_lt rootRoom)
  refine ⟨?_,lanes,placedBlocks,?_,widen ((RC).saved_register_room book safe) held,
    widen fits.2.2.2.1 directory,widen fits.2.2.2.2 directory,?_,m.window_fits sh floor count hub g Y w safe held⟩
  · rw [pair]
    exact prepared_pair_fits (RC) book _ _ _ _ _ _ safe shape (held.trans start)
      (parent.trans start) positive someBlocks
  · intro i
    exact (C).retained.prior_registers m.initial m.previousMeta m.previousArguments A₀ w roles args rootRoom i
  · intro i
    exact ⟨widen ((RC).window_fits _ (pro.trans_lt rootRoom)) pro,trivial⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
