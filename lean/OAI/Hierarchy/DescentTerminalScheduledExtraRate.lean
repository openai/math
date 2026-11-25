import OAI.Hierarchy.DescentTerminalPublicImageRate
import OAI.Hierarchy.DescentTerminalPublicRowRates
import OAI.Hierarchy.DescentTerminalRangeCalibration

namespace OAI
/-! # The contiguous original terminal advice at the common dated entry -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentPrimitivePalette
open DescentMixedRouter Catalyst Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The address exponent is fixed before the tail parameter and logarithmic cutoff. The
actual output includes the optional final bin, the original raw rows and the public pins. -/
theorem scheduled_extra_rate (op : RotorSpec) (drift t f g reset n degree C : ℕ)
    (branch : G.b≤2^(capRate G t g)) :
    ∃L:ℕ,∀τ B:ℕ,0<B →
      2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B →
      2*((τ+groupRate G t f g reset+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2)≤B →
    ∀ᶠ h:ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M:ℕ,2^h≤M→M≤(2^h)^2→
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let W:=NativeBranch.binLimit (k:=k) S
      let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
      let piece:=h/(16*(q*W))
      let p:=W*piece
      let cap:=NativeBranch.privateSlotCapacity G S drift
      let tags:=DescentBundleTagKeys.capacity (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
        (max 8 (2^S.capGain)) cap p drift
      let codes:=DescentTerminalScalarHeader.range q tags cap (S.epochPower^S.localTokenExponent) cap p
        (S.groupCount S.length*2^k)
      ∀{cp pins : ℕ}(X:Approximation F cp pins)(j rest bundles rawRows:ℕ),10*(X.size+1)≤M →
        j+(j+rest)=S.groupWidth k (tail τ J) 0+k →
        bundles*W≤terminalPool X G S p q W n degree C f g+W →
        rawRows≤terminalRawRows X G S p q n degree C f g →
        DescentTerminalPublicIdentity.total bundles W q piece codes rawRows
          (Fintype.card (Port pins X.width)*2^(j+rest))≤2^(L*h) := by
  obtain ⟨A,linear⟩:=terminal_public_row_rates G t f g reset n degree C
  let B₀:=max A 1
  refine ⟨B₀+7,?_⟩
  intro τ B pos cohort route
  filter_upwards [linear τ B,terminal_format_calibration G op drift t f g reset τ B branch pos cohort route,
    eventually_ge_atTop 1] with h rows ranges hh
  dsimp only
  intro M small large cp pins X j rest bundles rawRows initial shape bought raw
  obtain ⟨rawBound,poolBound,publicBound⟩:=rows M small large X j rest initial shape
  obtain ⟨dense,connector,alphabet⟩:=ranges M
  have a : A*h≤B₀*h:=Nat.mul_le_mul_right h (Nat.le_max_left ..)
  have one : h≤B₀*h:=by simpa only [one_mul] using Nat.mul_le_mul_right h (Nat.le_max_right A 1)
  have wide : 2^(A*h)≤2^(B₀*h):=Nat.pow_le_pow_right (by decide) a
  have half : h/2≤B₀*h:=(Nat.div_le_self h 2).trans one
  apply (DescentTerminalPublicIdentity.total_envelope _ _ _ _ _ _ _ (B₀*h)
    (bought.trans (poolBound.trans wide)) (raw.trans (rawBound.trans wide)) (publicBound.trans wide)
    (dense.trans half) (connector.trans half)
    ((Nat.le_succ _).trans (alphabet.trans (Nat.pow_le_pow_right (by decide) half)))).trans
  apply Nat.pow_le_pow_right (by decide)
  rw [Nat.add_mul]
  omega

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
