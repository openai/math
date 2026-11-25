import OAI.Hierarchy.DescentFromNativeStageHosts
import OAI.Hierarchy.DescentDyadicOpenNetworks

namespace OAI
/-! # Native terminal host construction may use the same dyadic site count at every date -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Catalyst CatalystSubstitution CorrectionBatch CollapseOracle Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The compiler receives dyadic sites. The concluding descent prices every allowed
original input size, including those between successive powers of two. -/
theorem descent_of_dyadic_native_stage_hosts (t f g reset τ B cost : ℕ)
    (pos : 0<B)
    (bought : let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
      2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤B)
    (built : ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
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
          hostSize H*2^J ≤ cost*d*(M+2^J*Fintype.card (Port n X.width))) :
    CollapseOracle.Descent F := by
  apply descent_of_native_stage_hosts G t f g reset τ B (2*cost) pos bought
  filter_upwards [built] with h make
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M ambient window k n X size
  obtain ⟨cover,double,low,high⟩:=dyadic_site_budget ambient window
  obtain ⟨calls,H,reached,spent⟩:=make (Nat.clog 2 M) low high X (size.trans cover)
  refine ⟨calls,H,reached,?_⟩
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let r:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)
  let W:=NativeBranch.binLimit (k:=r) S
  let grain:=W*(h/(16*((q*(G.b^(t*J)*G.b))*W)))
  let d:=S.copies*S.firstWidth G.b grain
  let E:=Fintype.card (Port n X.width)
  have charge : hostSize H*2^J≤cost*d*(hostRows M+2^J*E):=spent
  have cap : hostRows M+2^J*E≤2*(M+2^J*E):=by omega
  calc
    hostSize H*2^J≤cost*d*(hostRows M+2^J*E):=charge
    _≤cost*d*(2*(M+2^J*E)):=Nat.mul_le_mul_left _ cap
    _=(2*cost)*d*(M+2^J*E):=by ring

end
end Hierarchy.DescentSixParty

end OAI
