import OAI.Hierarchy.ProbeFixedPacketRates

namespace OAI
/-! # Funding rates and actual menu widths on both frozen layout shapes -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage StripDirectory
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def RowFunding {I : Type*} (width : I→ℕ) (arity : ℕ) (margin t : ℝ) : Prop :=
  (∃ embed : I→v.payloadPackets.index⊕v.boughtPackets.index,∀i,v.menu.width (embed i)=width i) ∧
    v.menu.margin≤ margin ∧ (arity:ℝ)/v.copyScale≤t*v.a*v.menu.margin

theorem payload_row_funding {N : ℕ} (count : N=publicStages v.W) (t : ℝ) (date : (v.finish:ℝ)/2≤t) :
    let menu:=payloadMenu F N k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt v.geometry.cutoff.1
      v.cost.payload v.cost.payload_nonneg 0
    v.RowFunding (fun i=>(menu.packet i).width) (Fintype.card ((PayloadStrip.Columns N × Fin k) ⊕ PayloadStrip.Quotes N k)) menu.margin t := by
  subst N
  exact ⟨⟨Sum.inl,fun _=>rfl⟩,(v.local_funding date).2.2.1,(v.local_funding date).1⟩

theorem purchased_row_funding (t : ℝ) (date : (v.finish:ℝ)/2≤t) :
    v.RowFunding (fun i=>(v.boughtPackets.packet i).width)
      (Fintype.card ((ChainStrip.Columns v.depth × Fin k) ⊕ ChainStrip.Axes v.depth k)) v.boughtPackets.margin t :=
  ⟨⟨Sum.inr,fun _=>rfl⟩,(v.local_funding date).2.2.2,(v.local_funding date).2.1⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
