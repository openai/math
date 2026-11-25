import OAI.Hierarchy.DescentRegisteredResetDatePrice
import OAI.Hierarchy.DescentRegisteredStageCalibration

namespace OAI
/-! Choose the complete dated host/group budget from the true reset and
ordinary constants before choosing the residual tail and the bus size. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (K : Parameters)
    (ordinaryLead ordinaryRate share saving packing : ℕ)
structure DateBook (lead exponent τ B h : ℕ) : Prop where
  resets : ∀a : Sample G board op K τ B h,a.Geometry→a.ReachedAt→
    let J:=Nat.log 2 h/(2*B)
    a.code.tariff ≤ a.hostWork*(lead*scale J exponent)+a.groupWork*(lead*scale J exponent)+
      a.copies/(2^J)^saving
  rows : ∀copies p : ℕ,let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G K.t J K.f K.g K.reset copies (tail τ J)
    let price:=(max lead ordinaryLead+max 1 share+137*K.ratio)*scale J (max exponent ordinaryRate)
    h ≤ p*scale J packing → ((S.length+1)*(price+1))*h ≤ p*2^(tail τ J) ∧
      (S.length+1)*(2^S.hostGain)^S.length*price*2^J ≤ p

theorem purchased_calendar :
    ∃lead exponent minimumTail minimumBus : ℕ,∀τ B : ℕ,minimumTail ≤ τ → 2*τ+minimumBus ≤ B →
    ∀ᶠ h : ℕ in atTop,DateBook G board op K ordinaryLead ordinaryRate share saving packing lead exponent τ B h:=by
  obtain ⟨lead,ex,cutoff,original⟩:=reset_date_price G board op K saving
  let rate:=max ex ordinaryRate
  let tailLow:=rate+2+packing
  let busLow:=cutoff+rate+4+hostRate K.t K.reset*(K.t+1)+packing
  refine ⟨lead,ex,tailLow,busLow,?_⟩
  intro τ B large reserve
  have den : 0 < B:=by dsimp [busLow] at reserve;omega
  have positive : 0 < τ:=by dsimp [tailLow] at large;omega
  have bought : 2*τ+cutoff ≤ B:=by dsimp [busLow] at reserve;omega
  have room : rate+3+hostRate K.t K.reset*(K.t+1)+packing < B:=by dsimp [busLow] at reserve;omega
  have branch : G.b ≤ 2^(capRate G K.t K.g):=(show G.b ≤ capRate G K.t K.g by unfold capRate;omega).trans Nat.lt_two_pow_self.le
  filter_upwards [original τ B positive den bought branch,registered_rows G K.t K.f K.g K.reset
    (max lead ordinaryLead+max 1 share+137*K.ratio) rate packing τ B large den room] with h resets dated
  exact ⟨resets,dated⟩

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
