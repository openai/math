import OAI.Hierarchy.TaggedWidePeerRoom
import OAI.Hierarchy.TaggedWidePassiveRows

namespace OAI
/-! # Bounded ends and low portions of occupied physical role slots -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open LinearAlgebra.SpectralBooks ChordGraph
open WireTelescope NamedAperture AdaptiveProbe Tagged PassiveWindow
open scoped Classical BigOperators

variable {S N D cap : ℕ} (ends : Fin N→Chord S) (qty : Fin N→ℕ) (s : Fin S)
  (bounded : ∀i,qty i≤cap) (slots : EndsAt ends qty s ↪ Fin D) {t : Widths S}
  (shape : installedWidths ends qty=t)
local notation "o" => carried ends qty s bounded slots shape
theorem carried_top (whole : ∀p : (portGraph S).Port s,t p.val.1≤cap) (i : Fin D) :
    (o).base i+(o).width i≤cap := by
  by_cases held : i∈Set.range slots
  · obtain ⟨a,rfl⟩:=held
    exact ((o).top _ _ (seat_value ends qty s bounded slots shape a).1).trans (whole _)
  · have absent:=seat_vacant ends qty s bounded slots shape i held
    rw [absent.2.1,absent.2.2]
    exact Nat.zero_le _

theorem sheet_low_le {P I : Type*} {total : P→ℕ} (tab : Parts P I cap total) (low : P→ℕ)
    (bound : ∀p,low p≤cap) (i : I) : (tab.view low i).low≤cap := by
  change (tab.owner i).elim 0 low≤cap
  cases h:tab.owner i with
  | none=>exact Nat.zero_le _
  | some p=>exact bound p

end Hierarchy.ProtocolRAM.SiteControls

end

end OAI
