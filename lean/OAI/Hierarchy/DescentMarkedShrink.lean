import OAI.Hierarchy.DescentRecordedCore
import OAI.Hierarchy.DescentPackingAllowance

namespace OAI
/-! # A subround shrinks the true marked core in every summand -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable {I C : Type} [Fintype I]

/-- The square-root and unused destination terms are charged to the actual
selected demand pairs. The half-tensor expansion, the tether bill and the
new marked-core bill all use the very same family of physical graphs. -/
theorem shrink_paid (A : MarkedWorld F D P bits) (G : PoweredGadget F)
    (pick : I×Fin 2 ↪ A.graph.Edge) (z : I → ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b) (pack : A.graph.Site→C)
    (picked : ∀t,pick t ∈ A.core) (u : ℝ) (hu : 0 < u)
    (cut B Q roots mass E ε β K : ℝ)
    (hc : 0<cut) (hB : 0<B) (hQ : 0≤Q) (hE : 0≤E) (he : 0≤ε) (hβ : 0≤β) (hK : 0≤K)
    (cutoff : 481*128*(K+1) ≤ cut)
    (count : Q ≤ roots+240*mass/(cut*B)) (slack : roots*(cut*B)≤ε)
    (full : mass ≤ 2*(u*A.liveWidth)+(β+1)*E+ε)
    (paired : (u*A.liveWidth)/2-Real.sqrt (B*Q*(u*A.liveWidth))/2-2*B*K*Q ≤
      u*(G.b*(∑i,z i):ℕ)) :
    let branch := selected A G pick z hz fit pack
    (∀ pins, (∑ p,(branch p).value pins)=A.value pins) ∧
      ∀ p,(branch p).tetherWidth≤A.tetherWidth ∧
        u*(branch p).liveWidth ≤ (1-(2-G.rate)/4)*(u*A.liveWidth) +
          (2-G.rate)*(((β+1)*E+ε)/4) := by
  let branch := selected A G pick z hz fit pack
  have invoice := DescentCompiler.colony_invoice hc hB count slack
  have enough := DescentCompiler.paid_quarter hB.le hQ
    (mul_nonneg hu.le (Nat.cast_nonneg _)) hE he hβ hK cutoff invoice full paired
  refine ⟨selected_sum A G pick z hz fit pack, fun p => ⟨selected_tether A G pick z hz fit pack p, ?_⟩⟩
  apply (G.subround_bound enough ?_).2
  have raw := selected_core A G pick z hz fit pack picked p
  push_cast at raw ⊢
  have scaled := mul_le_mul_of_nonneg_left raw hu.le
  nlinarith only [scaled]

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
