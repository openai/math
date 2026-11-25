import OAI.Hierarchy.DescentResetIngressSelectedPrice
import OAI.Hierarchy.DescentResetIngressScale

namespace OAI
/-! Charging the original funded and signed planes in the selected incoming
venue at the genuine date's clipped batch and chronological cap. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook DescentResetCanvasIngress DescentStaticWordColumn ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {P : Type} {degree : ℕ} {bs : P→ℕ}
    (W : MarkedWorld F degree P bs) (q ε : ℝ)

theorem selected_ingress_date_tariff_all (t f g reset τ B D n d C z ratio saving : ℕ) (tailPos : 0<τ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀ (P₀ : Type) (d₀ : ℕ) (bs₀ : P₀→ℕ) (world : MarkedWorld F d₀ P₀ bs₀) (q₀ ε₀ : ℝ),∀ copies i p w state wire hist : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(r : Reached world G q₀ ε₀ S k i state D wire hist) (rates : ResetRates G S k D n d C f g z tb)
        (drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ) (ordinary : ℕ→Dated.Ordinary)
        (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ),
      let a:=PhysicalReset.selected G S rates.board k tb i p f g drift degree h (resetCut S k tb p f h i)
        nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
      let phase:=a.ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
      let cap:=((capCalendar G.b S.rounds g S.height).take i).prod*256
      let b:=S.localWalshBits p (S.groupWidth k tb i+k) f (quota t)
      let unit:=ingressUnit G t f g reset τ B (quota t) ratio J
      i<S.length → i%(S.rounds+1)=S.rounds → p≤h → 2^h≤copies → w≤ratio*h → 8*b≤h →
      old.degree=D → old.paidBits=S.censusBits p → old.lanes=incoming S k tb p f h ordinary i →
      r.placement.cap=cap → (∀x : Fin (2^k),(io.atoms x.val).work≤7) →
      (phase.ticks+7*names phase.program)*w≤S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+copies/(2^J)^saving := by
  filter_upwards [ingress_date_scale G t f g reset τ B (quota t) ratio saving tailPos den] with h charged
  intro P₀ d₀ bs₀ world q₀ ε₀ copies i p w state wire hist J tb S k r rates drift degree nextM packet oldLanes primitiveLanes printedBits ordinary old io floor
    a phase cap b unit live boundary payload ambient hardware bitsRoom branch precision pitch capEq expr
  have H:0<S.hostSize i:=by
    have pos:0<copies:=(Nat.two_pow_pos h).trans_le ambient
    change 0<copies*(2^(hostRate t reset)*2^k)^i
    positivity
  have bounded:cap≤2^(8+(S.capGain-(G.b+3))*i):=by
    rw [←capEq];exact r.valid.bundleCapacity
  have native:=selected_ingress_price r rates p h drift degree (resetCut S k tb p f h i) nextM packet oldLanes
    primitiveLanes printedBits ordinary io.wire io.roster old floor w ratio branch precision pitch H hardware live boundary capEq bitsRoom
  have oldLanesPos:0<old.lanes:=by rw [pitch];simp only [incoming,ite_eq_left live,ite_eq_left boundary];exact Nat.two_pow_pos _
  have code:=Nat.mul_le_mul_right w (a.ingress.price floor w 7 io.hubs (fun x => io.atoms x.val) (fun t => io.wire t.1.val t.2.val) expr oldLanesPos (Nat.two_pow_pos _))
  have term:=charged copies i p cap live.le payload ambient bounded
  apply code.trans (native.trans _)
  change S.hostSize i*h*(65536*(2^k+2^k*(2*cap)+1)*ratio)+
    S.hostSize i*2^S.groupWidth k tb i*(65536*(2^k+2^k*(2*cap)+1)*ratio*(16*2^k*b))+
    (65536*(2^k+2^k*(2*cap)+1)*ratio*(h+1)^3)*2^(h/2)≤_
  rw [S.group_power (k:=k) (tail:=tb) rfl rfl i]
  exact term

theorem selected_ingress_date_tariff (t f g reset τ B D n d C z ratio saving : ℕ) (tailPos : 0<τ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀ copies i p w state wire hist : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(r : Reached W G q ε S k i state D wire hist) (rates : ResetRates G S k D n d C f g z tb)
        (drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ) (ordinary : ℕ→Dated.Ordinary)
        (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ),
      let a:=PhysicalReset.selected G S rates.board k tb i p f g drift degree h (resetCut S k tb p f h i)
        nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
      let phase:=a.ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
      let cap:=((capCalendar G.b S.rounds g S.height).take i).prod*256
      let b:=S.localWalshBits p (S.groupWidth k tb i+k) f (quota t)
      let unit:=ingressUnit G t f g reset τ B (quota t) ratio J
      i<S.length → i%(S.rounds+1)=S.rounds → p≤h → 2^h≤copies → w≤ratio*h → 8*b≤h →
      old.degree=D → old.paidBits=S.censusBits p → old.lanes=incoming S k tb p f h ordinary i →
      r.placement.cap=cap → (∀x : Fin (2^k),(io.atoms x.val).work≤7) →
      (phase.ticks+7*names phase.program)*w≤S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+copies/(2^J)^saving := by
  exact (selected_ingress_date_tariff_all G t f g reset τ B D n d C z ratio saving tailPos den).mono fun _ h=>h P _ bs W q ε

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
