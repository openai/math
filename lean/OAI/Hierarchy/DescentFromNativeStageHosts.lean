import OAI.Hierarchy.DescentFromSplitStageHosts
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # Oracle descent at the exact local port, terminal bin and source copy counts -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Catalyst CatalystSubstitution CorrectionBatch CollapseOracle Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The compiler uses the least dyadic aperture covering the actual local arity.
Both the terminal bin height and the source copy set are fixed before any
choice of replacement, execution history, or certificate. -/
theorem descent_of_native_stage_hosts (t f g reset τ B cost : ℕ)
    (pos : 0<B)
    (bought : let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
      2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤B)
    (built : ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M : ℕ, 2^h≤M → M≤(2^h)^2 → ∀{k n : ℕ} (X : Approximation F k n), 10*(X.size+1)≤M →
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
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  apply descent_of_split_stage_hosts G t f g reset τ (localSocketRate G t g) (τ+κ+4) B cost pos bought
  filter_upwards [built] with h issued
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M ambient window k n X room
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let r:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q₀:=2^Nat.clog 2 (NativeBranch.localLimit G S)
  let W:=NativeBranch.binLimit (k:=r) S
  obtain ⟨_,_,socket,live,rows,_,_,_⟩:=native_socket_scale G t J f g reset M τ
  exact ⟨q₀,W,Nat.two_pow_pos _,live,socket,rows,issued M ambient window X room⟩

end
end Hierarchy.DescentSixParty

end OAI
