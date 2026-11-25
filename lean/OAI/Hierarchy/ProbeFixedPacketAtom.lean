import OAI.Hierarchy.ProbeFixedCalendarParameters
import OAI.Hierarchy.ProbeCoreBoard

namespace OAI
/-! # The packet menu, native code, and actual number of terms at a public attempt -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.CoreBoard StripDirectory
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (z : ℕ)

/-- Selectors in the fixed format are indexed by the actual finite packet menus. -/
def payloadPacketMenu (N : ℕ) := payloadMenu F N k v.positive v.radius (Nat.cast_nonneg _)
  v.toleranceAt v.geometry.cutoff.1 v.cost.payload v.cost.payload_nonneg 0

def purchasePacketMenu := purchasedMenu F v.depth k v.positive v.radius (Nat.cast_nonneg _)
  v.toleranceAt v.geometry.cutoff.1 v.cost.purchase v.cost.purchase_nonneg 0

def menuCodes (N : ℕ) := max (Fintype.card (v.payloadPacketMenu N).index) (Fintype.card v.purchasePacketMenu.index)

local notation "N" => Stages z (2^v.W)

def wideBallotParties (a : Attempt) : ℕ :=
  match a with
  | .outer .. => Fintype.card (ColumnSite (PayloadStrip.Columns N) k)
  | .inner .. => Fintype.card (ColumnSite (ChainStrip.Columns v.depth) k)

/-- The native one-based recommendation uses the index type of its own dated menu. -/
def widePacketMenuIndex (a : Attempt) : Type :=
  match a with
  | .outer .. => (v.payloadPacketMenu N).index
  | .inner .. => v.purchasePacketMenu.index

def widePacketNumber (a : Attempt) : v.widePacketMenuIndex z a → ℕ := by
  cases a with
  | outer phase trial => exact fun i => (Fintype.equivFin (v.payloadPacketMenu N).index i).val+1
  | inner phase trial tick inner => exact fun i => (Fintype.equivFin v.purchasePacketMenu.index i).val+1

theorem widePacketNumber_injective (a : Attempt) : Function.Injective (v.widePacketNumber z a) := by
  cases a with
  | outer phase trial =>
    intro i j eq
    apply (Fintype.equivFin (v.payloadPacketMenu N).index).injective
    exact Fin.ext (Nat.add_right_cancel eq)
  | inner phase trial tick inner =>
    intro i j eq
    apply (Fintype.equivFin v.purchasePacketMenu.index).injective
    exact Fin.ext (Nat.add_right_cancel eq)

def widePacketTerms (a : Attempt) : v.widePacketMenuIndex z a → ℕ := by
  cases a with
  | outer phase trial => exact fun i => ((v.payloadPacketMenu N).packet i).terms
  | inner phase trial tick inner => exact fun i => (v.purchasePacketMenu.packet i).terms

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
