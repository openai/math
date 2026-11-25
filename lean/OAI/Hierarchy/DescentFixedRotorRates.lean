import OAI.Hierarchy.DescentFixedEpochRotor
import OAI.Hierarchy.DescentStageRates
import OAI.Hierarchy.DescentResetRateData

namespace OAI
/-! # The original ordinary and reset rates on a single fixed rotor at every epoch scale -/
namespace Hierarchy.DescentSixParty.EpochRotor
open DescentCompiler DescentHostDegree DescentResetInvoice DescentRotor DescentBaseProfile
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} (c : EpochRotor G)

/-- The reset rate witnesses for every height, input size, and terminal tail use
the same physical adjacency map and the same literal bit width. -/
theorem issued_rates (J M last : ℕ) (positive : 0<J) :
    let S:=stageNumbers G c.rounds J c.f c.g c.reset M last
    let cut:=cutRate c.rounds c.f c.g
    let k:=groupBits c.rounds J S.hostGain S.capGain cut
    OrdinaryRates G S k cut ∧
      ∃r : ResetRates G S k (atRound c.rounds) c.nodesLog c.degree c.multiplicity c.f c.g cut last,
        r.board=c.board ∧ r.bitsR=c.bits :=by
  intro S cut k
  obtain ⟨ord,host,cap,fc,gk,start,_,_⟩:=
    fixed_ordinary_rates G c.rounds J c.f c.g c.reset M last positive
  have fine : c.g ≤ S.capGain-(G.b+3) := by
    change c.g ≤ 3+c.g+G.b+_-(G.b+3)
    omega
  have depth : atRound c.rounds*2^DescentBaseProfile.decayExponent (atRound c.rounds) ≤ quota c.rounds :=
    Nat.le_succ _
  let r : ResetRates G S k (atRound c.rounds) c.nodesLog c.degree c.multiplicity c.f c.g cut last :=
    { board:=c.board, bitsR:=c.bits, enough:=c.capacity, degree:=depth, bits_positive:=c.bits_pos,
      rows:=c.packed, menu:=c.configures, loss:=c.loss, base:=rfl, radix:=rfl, fixed:=rfl,
      height:=positive, fcut:=fc, gk:=gk, gain:=c.reserve, host:=host, cap:=cap, fineCap:=fine, seed:=start }
  exact ⟨ord,r,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.EpochRotor

end OAI
