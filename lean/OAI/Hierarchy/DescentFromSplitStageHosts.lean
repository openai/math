import OAI.Hierarchy.DescentOpenSplitStageCount
import OAI.Hierarchy.DescentOpenHostRate

namespace OAI
/-! # Discharging the descent quantifiers from one compiled host at each priced input -/

namespace Hierarchy.DescentSixParty
open DescentCompiler Catalyst CatalystSubstitution CorrectionBatch CollapseOracle Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Only the physical sockets of the tagged gate are used to construct the host.
This representative has the required arity at every catalyst dimension. -/
def referenceReplacement (h k : ℕ) : Approximation F k (Tagged.pins h h) :=
  tableApprox (fun _=>0) (fun _=>0)

/-- The grain and multiplicity come from the original stage, including its terminal
radix. Physical agreement and the integral tariff on one host suffice for all
replacements, with a single pair of positive real constants. -/
theorem descent_of_split_stage_hosts (t f g reset τ a δ B cost : ℕ)
    (pos : 0<B) (bought : 2*(a+δ)+Nat.clog 2 G.b*(t+1)≤B)
    (built : ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M : ℕ, 2^h≤M → M≤(2^h)^2 → ∀{k n : ℕ} (X : Approximation F k n), 10*(X.size+1)≤M →
        ∃q W : ℕ, 0<q ∧ 0<W ∧ q≤2^(a*(J+1)) ∧ W≤2^(δ*(J+1)) ∧
        let S:=stageNumbers G t J f g reset M (τ*(J+1))
        let U:=G.b^(t*J)*G.b
        let grain:=W*(h/(16*((q*U)*W)))
        let d:=S.copies*S.firstWidth G.b grain
        let Y:=referenceReplacement (F:=F) h k
        ∃ calls : ℕ, ∃ H : Host F k (d*n) (Sockets (List.replicate calls (tagCall h Y))),
          Agrees (independentCopies d X)
            (tableApprox H.width (exactValue (List.replicate calls (tagCall h Y)) H)) ∧
          hostSize H*2^J ≤ cost*d*(M+2^J*Fintype.card (Port n X.width))) :
    CollapseOracle.Descent F := by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let L:=(τ+κ)*(t+2)+1
  let C:=L+2*cost+1
  have Lbound : (L:ℝ)≤C := by exact_mod_cast (by dsimp only [C];omega : L≤C)
  have costBound : 2*(cost:ℝ)≤C := by exact_mod_cast (by dsimp only [C];omega : 2*cost≤C)
  obtain ⟨powPos,powShort⟩:=open_host_exponent B pos
  refine ⟨1/(2*(B:ℝ)),C,powPos,powShort,?_,?_⟩
  · exact_mod_cast (by dsimp only [C];omega : 0<C)
  filter_upwards [stage_open_split_counts G t f g reset τ a δ B pos bought,built,
    eventually_ge_atTop 1] with h counts wired large
  intro M enough upper k n X input
  obtain ⟨q,W,hq,hW,cq,cW,calls,H,agrees,price⟩:=wired M enough upper X input
  obtain ⟨_,_,_,_,_,positive,copies⟩:=counts M q W hq hW cq cW
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (τ*(J+1))
  let U:=G.b^(t*J)*G.b
  let grain:=W*(h/(16*((q*U)*W)))
  let d:=S.copies*S.firstWidth G.b grain
  refine ⟨d,calls,positive,copies.trans (mul_le_mul_of_nonneg_right Lbound (sq_nonneg _)),?_⟩
  intro Y
  obtain ⟨target,correct,small⟩:=open_host_all_replacements X B h cost d M calls pos large
    (referenceReplacement (F:=F) h k) H agrees price Y
  refine ⟨target,correct,small.trans ?_⟩
  have nonneg : 0≤(M:ℝ)/(h:ℝ)^(1/(2*(B:ℝ)))+Fintype.card (Port n X.width) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right costBound (Nat.cast_nonneg d)) nonneg

end
end Hierarchy.DescentSixParty

end OAI
