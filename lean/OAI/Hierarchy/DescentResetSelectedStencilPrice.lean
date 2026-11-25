import OAI.Hierarchy.DescentResetSelectedStencilClock

namespace OAI
/-! Cofinal tariff for the actual public receiver width on a reset date. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh
open DescentPlainTerminal.Suffix ProtocolRAM DescentStaticWordColumn Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F)

def StencilDatePrice (t f g reset τ B D n ratio receiver saving lead exponent : ℕ) : Prop :=
  ∀ᶠ h : ℕ in atTop,∀ copies i p w d chart z : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tailBits:=tail τ J
      let S:=stageNumbers G t J f g reset copies tailBits
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀ (rates : ResetRates G S k D n d chart f g z tailBits) (drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
        (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ) (count : Bank),
      let prev:=resetCut S k tailBits p f h i
      let date:=PhysicalReset.selected G S rates.board k tailBits i p f g drift degree h prev nextM chart packet
        oldLanes primitiveLanes printedBits old io.wire io.roster floor
      let shape:=selected_stencil_shape (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
      let R:=date.stencilPhase shape (date.stageStart floor) count io.hubs g (2^n)
      let b:=S.localWalshBits p (S.groupWidth k tailBits i+k) f (quota S.rounds)
      let unit:=lead*TerminalScale.scale J exponent+remixFactor ratio*TerminalScale.scale J (5*stencilRate G t f g reset)
      i<S.length→p≤h→2^h≤copies→w≤ratio*h→ old.degree=D→8*b≤h→8*date.successor.groupWidth≤h→
      date.successor.groupWidth≤ TerminalScale.scale J receiver →
      (R.time w+7*names (R.code w))*w ≤
        S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+2*(copies/(2^J)^saving)

/-- The lead and exponent can be chosen before the tail and depth denominator. -/
theorem selected_stencil_uniform (t f g reset D n ratio receiver saving : ℕ) :
    ∃lead exponent : ℕ,∀τ B,0 < B → 2*(3*stencilRate G t f g reset+1) ≤ B →
      StencilDatePrice G t f g reset τ B D n ratio receiver saving lead exponent := by
  let rate:=stencilRate G t f g reset
  obtain ⟨lead,ex,quote⟩:=clipped_date_price 1200000 (3*rate) 3 rate receiver ratio saving
  refine ⟨lead,ex,?_⟩
  intro τ B den bought
  unfold StencilDatePrice
  filter_upwards [quote,endpoint_shape_at G t f g reset τ B D n den bought,
    remix_date_tariff G t f g reset τ B D n ratio saving den] with h budget geometry remix
  intro copies i p w d chart z J tb S k rates drift degree nextM packet oldLanes primitiveLanes printedBits old io floor count
    prev date shape R bits unit live small ambient machine degreeAt bitsRoom rootRoom width
  let original:=S.endpointBook k tb i p f old.degree h n
  let lo:=laneBits original.m h original.b
  let cap:=stencilCapacity k bits old.degree n
  let chosen:=PhysicalReset.receiverCut G S rates.board k tb i p f g drift degree h prev nextM chart packet oldLanes primitiveLanes printedBits old
  have clean:R.X.count.work≤6:=by rfl
  rw [←degreeAt] at geometry remix
  obtain ⟨localCap,_,range,positive,oldFits,_,_,_,_,_,_,_,_,_⟩:=geometry copies i p R.X live.le small clean
  have depth:original.r=k:=by change S.groupWidth k tb i+k-S.groupWidth k tb i=k;omega
  have inside:k≤lo:=by change S.endpointExponent k tb i p f old.degree h n+original.r≤lo at oldFits;omega
  have H:0<S.hostSize i:=by
    have m:0<copies:=(Nat.two_pow_pos h).trans_le ambient
    change 0<copies*(2^(hostRate t reset)*2^k)^i
    positivity
  have spend:=selected_stencil_clock (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io floor count w H inside bitsRoom rootRoom range
  have chartFit:R.chart.bits=DescentGLPacked.BankImage.chartBits (((1+old.degree)+original.m)*original.hosts) original.high lo original.b:=by
    change DescentGLPacked.BankImage.chartBits _ _ _ _=_
    have split:original.high+lo=original.m:=Nat.sub_add_cancel (Nat.min_le_left ..)
    congr 1
    change ((1+old.degree)+(original.high+lo))*original.hosts=((1+old.degree)+original.m)*original.hosts
    rw [split]
  obtain ⟨_,first⟩:=remix copies i p w R.chart R.origin R.solve R.fresh R.counts R.peers live.le small ambient machine chartFit
  change cap+1≤ TerminalScale.scale J rate at localCap
  have block:2^k≤ TerminalScale.scale J rate:=le_trans (by dsimp [cap,stencilCapacity];omega) localCap
  have field:bits≤ TerminalScale.scale J rate:=by
    have sized : bits ≤ bits+old.degree+n+7 :=
      ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
    have weighted := sized.trans (Nat.le_mul_of_pos_left _ (by decide : 0<8))
    exact (weighted.trans (Nat.le_add_left ..)).trans ((Nat.le_succ cap).trans localCap)
  have price:1200000*(cap+1)^3≤1200000*TerminalScale.scale J (3*rate):=by
    have fit:=Nat.pow_le_pow_left localCap 3
    have lift:(TerminalScale.scale J rate)^3=TerminalScale.scale J (3*rate):=by unfold TerminalScale.scale;rw [←pow_mul];congr 1;ring
    exact Nat.mul_le_mul_left _ (fit.trans_eq lift)
  have scans:=selected_root_rows (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io.wire io.roster floor live bitsRoom rootRoom
  have groups:=S.group_power (tail:=tb) (k:=k) rfl rfl i
  let rows:=chunks (S.groupCount i) (2^chosen)
  have paidRows:rows*h≤(2+2^k)*h+S.groupCount i*(32*2^k*bits+16*date.successor.groupWidth):=by
    change chunks (2^(S.groupWidth k tb i)) date.successor.middle.rootLanes*h ≤ _ at scans
    have inv:=PhysicalReset.selected_inventory G S rates.board k tb i p f g drift degree h prev nextM chart packet
      oldLanes primitiveLanes printedBits old io.wire io.roster floor
    rw [inv.2.2.2,groups] at scans
    exact scans
  let suffix:=1200000*(cap+1)^3*(S.hostSize i+S.hostSize i*rows+(h+1)^3*2^(h/2))
  have last:=budget J (S.hostSize i) (S.groupCount i) S.radix copies (1200000*(cap+1)^3) (2^k) bits
    date.successor.groupWidth rows w suffix (Nat.div_le_self ..) ambient price block field width machine paidRows le_rfl (Nat.two_pow_pos _)
  change _≤remixInvoice original R.chart R.origin R.solve R.fresh R.counts R.peers h w R.positive+
    (1200000*(cap+1)^3*(S.hostSize i+S.hostSize i*chunks (2^S.groupWidth k tb i) (2^chosen)+(h+1)^3*2^(h/2)))*w at spend
  rw [groups] at spend
  change _≤_+suffix*w at spend
  have budgetSum (x y u v shared : ℕ) :
      (x*u+y*u+shared)+(x*v+y*v+shared) =
      x*(v+u)+y*(v+u)+2*shared := by ring
  exact spend.trans ((Nat.add_le_add first last).trans_eq
    (budgetSum (S.hostSize i*h) (S.hostSize i*(S.groupCount i*S.radix)) _ _ _))

theorem selected_stencil_date_tariff (t f g reset τ B D n ratio receiver saving : ℕ)
    (den : 0<B) (bought : 2*(3*stencilRate G t f g reset+1)≤B) :
    ∃lead exponent : ℕ, StencilDatePrice G t f g reset τ B D n ratio receiver saving lead exponent := by
  obtain ⟨lead,ex,late⟩:=selected_stencil_uniform G t f g reset D n ratio receiver saving
  exact ⟨lead,ex,late τ B den bought⟩

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
