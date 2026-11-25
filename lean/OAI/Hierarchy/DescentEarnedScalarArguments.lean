import OAI.Hierarchy.DescentTerminalRangeCalibration
import OAI.Hierarchy.DescentNamedScalarPrintRoom

namespace OAI
/-! # The named terminal preflight's actual scalar menu arguments -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

structure EarnedScalarArguments (j s p q W tags pageBits printBits h w : ℕ) : Prop where
  rect : q*p = 2^j*s
  roles : 0 < tags
  spare : 0 < pageBits
  page : 32*pageBits ≤ h
  bins : 32*W ≤ h
  packed : 16*(q*p) ≤ h
  large : 10 ≤ h
  addressBits : h/2 ≤ w
  printed : 2^printBits < 2^w

/-- All original fields of the normalized preflight share its ambient height. -/
theorem earned_scalar_arguments_from_print (op : RotorSpec) (drift t f g reset τ B : ℕ)
    (branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < B)
    (cohortBudget : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B)
    (routingBudget : 2*((τ+groupRate G t f g reset+4)+
      (localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2) ≤ B)
    (printed : ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
        let cap:=(capCalendar G.b S.rounds g S.height).prod*256
        2+S.groupCount S.length*max (max 1 (Nat.clog 2 (q+1)))
          (DescentSignedCableCodec.width 3 cap) ≤ h) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M _headerRows _paidRows w : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let W:=NativeBranch.binLimit (k:=k) S
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let q:=2^j*(G.b^(t*J)*G.b)
        let p:=W*(h/(16*(q*W)))
        let s:=S.firstWidth G.b p
        let tags:=DescentBundleTagKeys.capacity (colors G s (S.grainAt G.b p 0) op)
          (max 8 (2^S.capGain)) (NativeBranch.privateSlotCapacity G S drift) p drift
        let pageBits:=max 1 ((S.groupCount S.length*2^k)*actualSpan G S op q p drift)
        let cap:=(capCalendar G.b S.rounds g S.height).prod*256
        let printBits:=2+S.groupCount S.length*max (max 1 (Nat.clog 2 (q+1)))
          (DescentSignedCableCodec.width 3 cap)
        3*h ≤ w → EarnedScalarArguments j s p q W tags pageBits printBits h w := by
  filter_upwards [terminal_cohort_span G op drift t f g reset τ B branch positive cohortBudget,
    native_format_widths G t f g reset τ B positive routingBudget,printed,
    eventually_ge_atTop 32] with h spans widths printRoom late
  intro J M headerRows paidRows w S k W j q p s tags pageBits cap printBits word
  obtain ⟨binBound, packedBound, pBound, qBound, _, _⟩ := widths M
  have page : 32*((S.groupCount S.length*2^k)*actualSpan G S op q p drift) ≤ h :=
    spans M p q pBound qBound
  have printWidth : printBits ≤ h := printRoom M
  refine ⟨?_,terminal_tag_capacity_pos G S op p drift,?_,?_,binBound,packedBound,by omega,
    by omega,Nat.pow_lt_pow_right (by decide) (by omega : printBits < w)⟩
  · change (2^j*(G.b^(t*J)*G.b))*p = 2^j*(S.grainAt G.b p 0*G.b)
    rw [S.grain_initial]
    change _ = 2^j*(p*G.b^(t*J)*G.b)
    ring
  · change 0 < max 1 _
    omega
  · change 32*max 1 ((S.groupCount S.length*2^k)*actualSpan G S op q p drift) ≤ h
    rcases le_total 1 ((S.groupCount S.length*2^k)*actualSpan G S op q p drift) with yes|no
    · rwa [max_eq_right yes]
    · rw [max_eq_left no]
      omega

/-- The paid signed calendar supplies the printed-width bound for the same named preflight. -/
theorem earned_scalar_arguments (op : RotorSpec) (drift t f g reset τ B : ℕ)
    (branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < B)
    (cohortBudget : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B)
    (routingBudget : 2*((τ+groupRate G t f g reset+4)+
      (localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2) ≤ B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M _headerRows _paidRows w : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let W:=NativeBranch.binLimit (k:=k) S
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let q:=2^j*(G.b^(t*J)*G.b)
        let p:=W*(h/(16*(q*W)))
        let s:=S.firstWidth G.b p
        let tags:=DescentBundleTagKeys.capacity (colors G s (S.grainAt G.b p 0) op)
          (max 8 (2^S.capGain)) (NativeBranch.privateSlotCapacity G S drift) p drift
        let pageBits:=max 1 ((S.groupCount S.length*2^k)*actualSpan G S op q p drift)
        let cap:=(capCalendar G.b S.rounds g S.height).prod*256
        let printBits:=2+S.groupCount S.length*max (max 1 (Nat.clog 2 (q+1)))
          (DescentSignedCableCodec.width 3 cap)
        3*h ≤ w → EarnedScalarArguments j s p q W tags pageBits printBits h w := by
  apply earned_scalar_arguments_from_print G op drift t f g reset τ B branch positive cohortBudget
    routingBudget
  have paid : 2*(τ+2) ≤ B := by omega
  filter_upwards [named_scalar_print_room G t f g reset τ B paid] with h rooms
  intro J M S q cap
  have bound:=rooms M
  change 32*(2+S.groupCount S.length*max (max 1 (Nat.clog 2 (q+1)))
    (DescentSignedCableCodec.width 3 cap)) ≤ h at bound
  omega


end
end Hierarchy.DescentSixParty

end OAI
