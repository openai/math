import OAI.Hierarchy.DescentFromDyadicStageHosts

namespace OAI
/-! # The dyadic host required at one actual schedule height -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Catalyst CatalystSubstitution CorrectionBatch CollapseOracle Filter
open scoped Classical
noncomputable section

def DyadicHostAt {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B cost h : ℕ) : Prop :=
  let J:=Nat.log 2 h/(2*B)
  ∀j : ℕ, let M:=(2:ℕ)^j
        2^h≤M → M≤(2^h)^2 → ∀{k n : ℕ} (X : Approximation F k n), 10*(X.size+1)≤M →
        let S:=stageNumbers G t J f g reset M (tail τ J)
        let r:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let q₀:=2^Nat.clog 2 (NativeBranch.localLimit G S)
        let W:=NativeBranch.binLimit (k:=r) S
        let U:=G.b^(t*J)*G.b
        let grain:=W*(h/(16*((q₀*U)*W)))
        let d:=S.copies*S.firstWidth G.b grain
        let Y:=referenceReplacement (F:=F) h k
        ∃ calls : ℕ, ∃ H : Host F k (d*n) (Sockets (List.replicate calls (tagCall h Y))),
          Agrees (independentCopies d X)
            (tableApprox H.width (exactValue (List.replicate calls (tagCall h Y)) H)) ∧
          hostSize H*2^J ≤ cost*d*(M+2^J*Fintype.card (Port n X.width))

theorem descent_of_priced_dyadic_hosts {F : Type} [Field F] (G : PoweredGadget F)
    (t f g reset τ B cost : ℕ) (pos : 0<B)
    (bought : let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
      2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤B)
    (built : ∀ᶠ h : ℕ in atTop, DyadicHostAt G t f g reset τ B cost h) :
    CollapseOracle.Descent F :=
  descent_of_dyadic_native_stage_hosts G t f g reset τ B cost pos bought built

end
end Hierarchy.DescentSixParty

end OAI
