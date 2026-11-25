import OAI.Hierarchy.DescentStageCopyRoom
import OAI.Hierarchy.DescentPrivateDonorBillNumbers

namespace OAI
/-! # Uniform address rates for the actual cofinal degree and host schedule -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- One bit rate independent of the date, the initial arity and the realized
state covers the complete calendar length, source radix, groups, host page and
capacity ceiling. The only changing upper bound on initial arity is the genuine 4^h. -/
theorem stage_address_scalars (t f g reset τ : ℕ) :
    ∃A : ℕ,∀ h J M tail i : ℕ,0<h → (J+1)^2≤h → M≤4^h → tail≤τ*h →
      let S:=stageNumbers G t J f g reset M tail
      i≤S.length →
      S.length+1≤2^(A*h) ∧ S.radix≤2^(A*h) ∧ S.groupCount i≤2^(A*h) ∧
      2^Nat.clog 2 (S.hostSize i)≤2^(A*h) ∧ 2^(8+S.capGain*i)≤2^(A*h) := by
  let c:=hostRate t reset
  let e:=capRate G t g
  let K:=τ+privateGroupRate t c e (cutRate t f g)
  let A:=16+(t+1)+2+K+c*(t+1)+e*(t+1)
  refine ⟨A,?_⟩
  intro h J M tail i hh age initial seed S dated
  have Jle : J≤h := by nlinarith only [age,Nat.zero_le (J*J)]
  have date : S.length≤(t+1)*h := Nat.mul_le_mul_left _ Jle
  have index : i≤(t+1)*h:=dated.trans date
  have initial' : M≤2^(2*h) := by simpa only [Nat.pow_mul] using initial
  have cp : S.copies≤2^(K*h) :=stage_copies_word G t J f g reset M tail τ h hh age seed
  have base : 0<S.baseGroups:=Nat.two_pow_pos _
  have radix : 0<S.radix:=Nat.two_pow_pos _
  have gm : 0<S.groupCount i:=Nat.mul_pos base (Nat.pow_pos radix)
  have groups : S.groupCount i≤S.copies := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right radix (by omega))
  have rle : S.radix≤S.copies := by
    have step : S.radix≤S.radix^(S.length+1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right radix (show 1≤S.length+1 by omega)
    exact step.trans (Nat.le_mul_of_pos_left _ base)
  have ex {x y : ℕ} (le : x≤y) : 2^(x*h)≤2^(y*h):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
  have cpf : 2^(K*h)≤2^(A*h) := ex (by dsimp [A];omega)
  have hrow : S.hostSize i≤2^((2+K+c*(t+1))*h) := by
    have row := (Nat.le_mul_of_pos_right (S.hostSize i) (Nat.mul_pos gm radix)).trans (S.slot_reserve dated)
    have hex : (2^S.hostGain)^S.length≤2^((c*(t+1))*h) := by
      rw [←Nat.pow_mul,Nat.mul_assoc];exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left c date)
    have book:=Nat.mul_le_mul (Nat.mul_le_mul initial' cp) hex
    simpa only [Nat.add_mul,Nat.pow_add] using row.trans book
  have hpad:2^Nat.clog 2 (S.hostSize i)≤2*S.hostSize i+1:=by
    by_cases live:0<S.hostSize i
    · exact (DescentCompiler.TerminalScale.hostRows_double live).trans (Nat.le_succ _)
    · have empty:S.hostSize i=0:=by omega
      simp [empty]
  have hu : (2+K+c*(t+1))*h+2≤A*h := by
    have := Nat.mul_le_mul_right h (show 2+K+c*(t+1)+2≤A by dsimp [A];omega)
    rw [Nat.add_mul (2+K+c*(t+1)) 2] at this
    omega
  have pad:=Nat.pow_le_pow_right (by decide : 0<2) hu
  rw [Nat.pow_add] at pad
  have one:=Nat.two_pow_pos ((2+K+c*(t+1))*h)
  have dates : S.length+1≤2^(A*h) := by
    apply (Nat.lt_two_pow_self (n:=S.length)).trans_le
    exact Nat.pow_le_pow_right (by decide) (date.trans (Nat.mul_le_mul_right h (by dsimp [A];omega)))
  refine ⟨dates,rle.trans (cp.trans cpf),groups.trans (cp.trans cpf),by omega,?_⟩
  apply Nat.pow_le_pow_right (by decide)
  have cap:= Nat.mul_le_mul_left e index
  change 8+e*i≤A*h
  have coeff:=Nat.mul_le_mul_right h (show 8+e*(t+1)≤A by dsimp [A];omega)
  rw [Nat.add_mul,Nat.mul_assoc] at coeff
  omega

end
end Hierarchy.DescentSixParty.NativeBranch

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale
variable {F:Type} [Field F]

/-- Both bounds hold at every physical choice, before observing its candidate stream. -/
theorem observed_word_room {G : PoweredGadget F} (t f g reset τ : ℕ) :
    ∃factor : ℕ,∀ h J M tail i : ℕ,0<h → (J+1)^2≤h → M≤4^h → tail≤τ*h →
      let S:=stageNumbers G t J f g reset M tail
      i≤S.length → ∀w:ℕ, factor*h≤w →
        S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w ∧
        (S.groupCount i*hostRows (S.hostSize i)*S.radix)*2^(8+S.capGain*i)<2^w := by
  obtain ⟨c,book⟩:=NativeBranch.stage_address_scalars G t f g reset τ
  refine ⟨4*c+1,?_⟩
  intro h J M tail i positive dates inputs residual S age w word
  obtain ⟨_,radix,groups,hosts,cap⟩:=book h J M tail i positive dates inputs residual age
  change hostRows (S.hostSize i)≤2^(c*h) at hosts
  have three : S.groupCount i*hostRows (S.hostSize i)*S.radix≤(2^(c*h))^3 := by
    simpa only [pow_succ,pow_zero,one_mul] using Nat.mul_le_mul (Nat.mul_le_mul groups hosts) radix
  have four := Nat.mul_le_mul three cap
  have sky : (2^(c*h))^4 < 2^w := by
    rw [←pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by nlinarith)
  have whole := four.trans_lt (show (2^(c*h))^3*2^(c*h)<2^w from sky)
  exact ⟨(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans_lt whole,whole⟩

end Hierarchy.DescentSixParty

end OAI
