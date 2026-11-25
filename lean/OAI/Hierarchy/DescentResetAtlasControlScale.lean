import OAI.Hierarchy.DescentResetRootControlScale

namespace OAI
/-! The numerical controls appearing in the original root traffic all share one
height exponent, uniformly in clipping and all original dates. -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentPlainTerminal.Suffix
open DescentNamedFundedChart DescentFallbackPeriod Filter LinearAlgebra.SpectralBooks ThreeFlat
noncomputable section

theorem atlas_controls_at {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B D n : ℕ) (den : 0 < B) :
    ∀ᶠ h : ℕ in atTop, ∀ M age p e previous : ℕ, p ≤ h →
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let xs:=capCalendar G.b S.rounds g S.height
      let cap:=(xs.take age).prod*256
      let m:=fromCalendar S k (tail τ J) age p f D h e previous n (GroupStage.depthBound D n f g) xs
      let b:=S.localWalshBits p (S.groupWidth k (tail τ J) age+k) f (quota S.rounds)
      let u:=scale J (13*localRate G t f g reset D n)
      m.rootControlBits cap ≤ u ∧ 2^k ≤ u ∧ b ≤ u := by
  filter_upwards [root_controls_at G t f g reset τ B D n den] with h root
  intro M age p e previous hp J S k xs cap m b u
  have top:m.rootControlBits cap ≤ u:=root M age p e previous hp
  have ar:=m.rootControl_le cap
  let A:=Projected.Receiver.arityLimit D (2^k) cap n k
  have size : A ≤ m.rootControlBits cap := ar _ (by simp [m,A,fromCalendar])
  have cells:inputCount D (2^k) cap n k ≤ A:=le_max_right ..
  have blocks:2^k ≤ A:=by unfold inputCount at cells;omega
  have N:m.stencil.n ≤ m.rootControlBits cap := ar _ (by simp)
  have width:b ≤ m.stencil.n := by change b ≤ k+b+2;omega
  exact ⟨top,blocks.trans (size.trans top),width.trans (N.trans top)⟩

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
