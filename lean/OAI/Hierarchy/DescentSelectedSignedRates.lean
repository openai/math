import OAI.Hierarchy.DescentSignedRateNumbers
import OAI.Hierarchy.DescentSignedStageRates
import OAI.Hierarchy.DescentPrivateDonorActual

namespace OAI
/-! # The selected 21-job signed renderer on every ordinary transition -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree DescentDatedAddressBook
open Filter
open scoped BigOperators
noncomputable section

variable {F : Type} [Field F]

variable {P : Type} {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {S : AtomSchedule} {price u ε : ℝ} {k i z z' D D' wire hist : ℕ}
    {W : MarkedWorld F d P bits} {prior : Reached W G price ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {p : (T.result he).Choice}
    {n : Normalize ((T.result he).state p)} {next : Reached n.result G price ε S k (i+1) z' D' wire hist}

namespace OrdinaryLink
variable (ticket : OrdinaryLink prior he T p n next)

include ticket in
theorem selected_signed_rates {t f g reset J M tail : ℕ}
    (calendar : S=stageNumbers G t J f g reset M tail)
    (radix : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (H H' groups payload : ℕ) :
    let q : SignedStage:=⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
      H,H',groups,G.b,G.C,G.k⟩
    let r:=signedRates G t f g reset
    q.unit ≤ scale J r.amount ∧ (q.format payload).feedFactor (max q.newDegree 88) ≤ scale J r.controls := by
  subst S
  have degree:=ticket.degree_limit
  have age:i≤(t+1)*J:=ticket.hubRows.choose.le
  have cap:=prior.valid.capacity.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (Nat.add_le_add_left (Nat.mul_le_mul_left (capRate G t g) age) 8))
  have rates:=(signedRates G t f g reset).bounds J _ _ H H' groups payload degree cap
  rw [←radix] at rates
  have newDegree : next.placement.degree = ordinaryDegree prior.placement.degree :=
    next.branch.trans (ticket.nextDegree.trans (congrArg ordinaryDegree prior.branch.symm))
  have newCap : next.placement.cap =
      2 ^ gainExponent 20 prior.placement.degree * G.b * prior.placement.cap :=
    ticket.capacity.trans (congrArg (fun d => 2 ^ gainExponent 20 d * G.b * prior.placement.cap)
      prior.branch.symm)
  dsimp only
  simpa only [newDegree, newCap] using rates

/-- The signed lanes on the actual stage are positive and accept the full block
projector for the single word chosen for the entire execution. -/
theorem selected_signed_room (G : PoweredGadget F) (t f g reset B : ℕ)
    (budget : (signedRates G t f g reset).amount<B) :
    ∀ᶠ payload : ℕ in atTop,
      2*scale (Nat.log 2 payload/(2*B)) (signedRates G t f g reset).amount≤payload :=
  AgeBound.payload_room _ B budget

end OrdinaryLink

end
end Hierarchy.DescentSixParty.Chronology

end OAI
