import OAI.Hierarchy.DescentMeasuredHistory
import OAI.Hierarchy.DescentResetSplicePrice

namespace OAI
/-! # Following every profile through the measured subrounds of one reset epoch -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

universe v
variable {F : Type} [Field F] {d : ℕ} {P : Type} {bits : P→ℕ}
variable (G : PoweredGadget F) {u ε : ℝ} (he : 0≤ε)

/-- The next placement is read on the actual outgoing graph of its own parent
history. There are no weight or coefficient conclusions among the input fields. -/
def Schedule : (t : ℕ) → Histories.{0, 0, v} F d P bits → Type (max 1 v)
  | 0,_ => PUnit
  | t+1,H => Σ data : SubroundInput H G (u:=u) he, Schedule t (H.extend he data)

namespace Schedule

def finish : {t : ℕ} → {H : Histories.{0, 0, v} F d P bits} →
    Schedule G (u:=u) he t H → Histories.{0, 0, v} F d P bits
  | 0,H,_ => H
  | t+1,H,c => @finish t (H.extend he c.1) c.2

theorem finish_value {t : ℕ} (H : Histories F d P bits) (run : Schedule G (u:=u) he t H) (x : Ports bits) :
    (finish G he run).value x=H.value x := by
  induction t generalizing H with
  | zero => rfl
  | succ t ih =>
    change ((finish G he run.2).value x)=H.value x
    exact (ih _ run.2).trans (H.extend_value he run.1 x)

/-- The error at each color choice is multiplied by the actual geometric
factor of the remaining stages. All branches retain the same exterior cap. -/
theorem finish_bill {t : ℕ} (H : Histories F d P bits) (run : Schedule G (u:=u) he t H)
    (hu : 0≤u) (E X : ℝ)
    (before : ∀c,u*(H.state c).tetherWidth≤E ∧ u*(H.state c).liveWidth≤X)
    (c : (finish G he run).Choice) :
    let ρ := 1-(2-G.rate)/4
    let B := 257*E+ε
    u*((finish G he run).state c).tetherWidth≤E ∧
      u*((finish G he run).state c).liveWidth≤ρ^t*X+(1-ρ^t)*B := by
  induction t generalizing H X with
  | zero => simpa [finish] using before c
  | succ t ih =>
    let ρ := 1-(2-G.rate)/4
    let B := 257*E+ε
    let H' := H.extend he run.1
    have next : ∀c,u*(H'.state c).tetherWidth≤E ∧ u*(H'.state c).liveWidth≤ρ*X+(1-ρ)*B :=
      H.extend_bill he run.1 hu before
    have after := ih H' run.2 (ρ*X+(1-ρ)*B) next c
    refine ⟨after.1,after.2.trans_eq ?_⟩
    dsimp only [ρ,B]
    rw [pow_succ]
    ring

/-- For the rotor's fixed number of measured subrounds, the only multiplier
on the incoming core is the degree-independent internal rotor rate. The
exceptional and external contacts enter additively. -/
theorem reset_bill {t : ℕ} (H : Histories F d P bits) (run : Schedule G (u:=u) he t H)
    (hu : 0≤u) (E X : ℝ) (Epos : 0≤E) (Xpos : 0≤X)
    (before : ∀c,u*(H.state c).tetherWidth≤E ∧ u*(H.state c).liveWidth≤X)
    (c : (finish G he run).Choice) (h C tetherHops : ℕ)
    (menu : DescentResetInvoice.reentryRate h C*(1-(2-G.rate)/4)^t≤1/2)
    {rotorCost : ℝ} (receipt : rotorCost≤DescentResetInvoice.reentryRate h C*
      (u*((finish G he run).state c).liveWidth+ε)+DescentResetInvoice.reentryExteriorRate h C 256 tetherHops*E) :
    rotorCost≤X/2+(258*DescentResetInvoice.reentryRate h C+
      DescentResetInvoice.reentryExteriorRate h C 256 tetherHops)*(E+ε) := by
  let ρ := 1-(2-G.rate)/4
  let A := DescentResetInvoice.reentryRate h C
  let C' := DescentResetInvoice.reentryExteriorRate h C 256 tetherHops
  have r : 0≤ρ := by dsimp [ρ];linarith [G.rate_nonneg]
  have a : 0≤A := by dsimp [A,DescentResetInvoice.reentryRate,DescentResetInvoice.splicedRate,DescentResetInvoice.internalRate];positivity
  have ext : 0≤C' := by dsimp [C',DescentResetInvoice.reentryExteriorRate,DescentResetInvoice.splicedExteriorRate,DescentResetInvoice.exteriorRate,DescentResetInvoice.internalRate];positivity
  have paid := (finish_bill G he H run hu E X before c).2
  have upper : u*((finish G he run).state c).liveWidth≤ρ^t*X+(257*E+ε) := by
    nlinarith only [paid,mul_nonneg (pow_nonneg r t) (show 0≤257*E+ε by positivity)]
  have halved := mul_le_mul_of_nonneg_right menu Xpos
  have state := mul_le_mul_of_nonneg_left upper a
  change rotorCost≤X/2+(258*A+C')*(E+ε)
  change rotorCost≤A*(u*((finish G he run).state c).liveWidth+ε)+C'*E at receipt
  change A*ρ^t*X≤1/2*X at halved
  nlinarith only [receipt,state,halved,mul_nonneg a Epos,mul_nonneg a he,mul_nonneg ext he]

end Schedule
end
end Hierarchy.DescentSixParty

end OAI
