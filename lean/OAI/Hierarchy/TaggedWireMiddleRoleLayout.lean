import OAI.Hierarchy.TaggedWideCalendarMiddle
import OAI.Hierarchy.TaggedWideNamedWidths

namespace OAI
/-! # Preserve the actual corrected-sheet role and digit while transporting its width -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor WireTelescope WireTelescope.CalendarTape AdaptiveProbe ReportSockets

variable {h W k attempts n cap : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (order : Fin n≃Source S π depth marks) (bits : Fin n→ℕ)
    (capacity : Public S h W k attempts→ℕ)
    (fit : ∀i side,bits i≤capacity (named S π depth marks unique order (i,side)))
    (within : ∀r,capacity r≤cap)
local notation "K" => siteLast h (2^W) k+1
local notation "deg" => stride k S.degree attempts
local notation "original" => statePlace S π depth marks unique order bits capacity fit
local notation "chart" => LedgerStep.rolesChart capacity within (shelfSlot S)
variable {B : Widths (siteLast h (2^W) k+1)}
    (eqn : installedWidths (sorted S π depth marks ∘ order) bits = B)

def placedMiddle : (Σt,SiteBit B t) ↪ Fin K×Fin (deg*cap) :=
  by
    subst B
    exact (original).trans chart

theorem placedMiddle_site (s : Fin K) (j : SiteBit B s) :
    (placedMiddle S π depth marks unique order bits capacity fit within eqn ⟨s,j⟩).1=s := by
  subst B
  let p := ((original) ⟨s,j⟩).1
  change (finProdFinEquiv.symm (finProdFinEquiv
    (name (site S p), (⟨code S p, code_bound S p⟩ : Fin deg)))).1 = s
  rw [Equiv.symm_apply_apply]
  exact statePlace_site S π depth marks unique order bits capacity fit ⟨s,j⟩

theorem placedMiddle_range :
    Set.range (placedMiddle S π depth marks unique order bits capacity fit within eqn)=Set.range ((original).trans chart) := by
  subst B
  rfl

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles
end

end OAI
