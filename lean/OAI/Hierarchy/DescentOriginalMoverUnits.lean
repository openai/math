import OAI.Hierarchy.DescentOriginalMoverApertures
import OAI.Hierarchy.DescentOriginalPrimitiveLimits

namespace OAI
/-! # A fixed calendar exponent for the original home-filtered role transfer -/

namespace Hierarchy.DescentRetainedHomeMover.Layout
open DescentCompiler DescentCompiler.TerminalScale DescentResetRetainedSetup DescentPlacedInvoiceVolume
noncomputable section
def fixedUnits (L : ℕ) :=
  let n:=3*L*L
  let channels:=2*L
  let lits:=DescentResetRetainedSetup.Layout.literalLinear n L channels 1 1 1 1
  let gl:=DescentResetRetainedSetup.Layout.computeLinear n channels (1+L*23) lits 1 1
  109+(2*L)*8192+DescentResetRetainedSetup.Layout.mountFee L+DescentResetRetainedSetup.Layout.mountFee (2*L)+
    gl+(109+channels*8192)+controlFactor L 7+printed (channels+L)+
    (stemFactor (L*L) L (14+channels*(25+11))+suffixFactor L L L)

theorem units_le (z : DescentRetainedHomeMover.Layout) (L : ℕ) (d : z.transfer.high+z.transfer.low≤L)
    (small : z.transfer.previousNodes≤L) (noArgs : z.transfer.previousArgs=0) (nodes : z.transfer.nodes≤L)
    (oldBlocks : z.transfer.blocks≤L) (blocks : z.blocks≤L) (shapes : z.shapes≤L) :
    z.invoiceUnits≤fixedUnits L:=by
  let width:=z.transfer.high+z.transfer.low
  have sw:(DescentGLNielsen.schedule width).length≤3*L*L:=(DescentGLNielsen.length_le width).trans (by
    dsimp [width];gcongr)
  simp only [invoiceUnits,fixedUnits,queryBudget,DescentResetRetainedSetup.Layout.movementUnits,
    DescentResetRetainedSetup.Layout.glUnits,DescentResetRetainedSetup.Layout.computeLinear,
    DescentResetRetainedSetup.Layout.literalLinear,DescentResetRetainedSetup.Layout.retainedFieldWork,
    DescentResetRetainedSetup.Layout.sources,DescentResetRetainedSetup.Layout.channels,
    DescentResetRetainedSetup.Layout.fields,noArgs,Nat.mul_zero,Nat.add_zero,DescentResetRetainedSetup.Layout.mountFee,
    controlFactor,printed,stemFactor,suffixFactor,volumeFactor]
  gcongr

theorem fixed_units_height (J e : ℕ) : fixedUnits (scale J e)≤(2^64)*scale J (8*e):=by
  let L:=scale J e
  have polynomial:fixedUnits L≤(2^56)*(L+1)^8:=by
    unfold fixedUnits DescentResetRetainedSetup.Layout.literalLinear DescentResetRetainedSetup.Layout.computeLinear
      DescentResetRetainedSetup.Layout.mountFee controlFactor printed stemFactor suffixFactor volumeFactor
    ring_nf;omega
  have positive:1≤L:=Nat.two_pow_pos _
  have plus:L+1≤2*L:=by omega
  have exp:L^8=scale J (8*e):=by
    change (2^(e*(J+1)))^8=2^((8*e)*(J+1))
    rw [←pow_mul];congr 1;ring
  calc _≤(2^56)*(L+1)^8:=polynomial
       _≤(2^56)*(2*L)^8:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left plus _)
       _=(2^64)*scale J (8*e):=by rw [mul_pow,exp];ring
end
end Hierarchy.DescentRetainedHomeMover.Layout

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentRetainedHomeMover Filter
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset D : ℕ)
local notation "E" => primitiveLocalExponent G board op t f g reset D

theorem original_mover_units (τ drift B : ℕ) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
    ∀sites age p degree e previous lanes nextM base old,p≤h→degree≤bound→
      let z:=originalSample G op t f g reset τ D drift J sites age p degree h e previous lanes nextM base old
      old.nodes≤z.sched.retainedNodes→
        (z.output G board D f g op.C op.w).roleTransfer.invoiceUnits≤(2^64)*scale J (8*E):=by
  filter_upwards [original_fields G board op t f g reset τ D drift B positive branch bound,
    original_primitive_limits G board op t f g reset D τ drift B positive branch bound] with h active limits
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro sites age p degree e previous lanes nextM base old hp hd
  let z:=originalSample G op t f g reset τ D drift J sites age p degree h e previous lanes nextM base old
  let v:=z.output G board D f g op.C op.w
  intro prior
  have p₀:=limits sites age p degree e previous lanes nextM base old hp hd
  have dims:=active sites age p degree e previous lanes nextM base old hp hd
  have pos : localExponent G board op t f g reset D≤E:=
    (Nat.le_add_right _ _).trans (Nat.le_add_right ..)
  have d:z.sched.groupWidth z.k z.tail z.age+z.k≤ scale J E:=
    dims.dim.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ pos))
  have geom:v.roleTransfer.transfer.CalendarPitch (z.sched.groupWidth z.k z.tail z.age) z.k h v.retainedRoleUnit:=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  apply le_trans _ (Layout.fixed_units_height J E)
  apply Layout.units_le
  · rw [(DescentResetRetainedSetup.Layout.CalendarPitch.geometry _ geom).1]
    exact d
  · exact prior.trans p₀.nodes
  · rfl
  · exact p₀.nodes
  · exact p₀.blocks
  · exact p₀.blocks
  · exact p₀.shapes

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
