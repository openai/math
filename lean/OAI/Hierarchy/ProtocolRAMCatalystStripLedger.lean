import OAI.Hierarchy.ProtocolRAMCatalystLedgerFit
import OAI.Hierarchy.ProtocolRAMCatalystStripLedgerReads
import OAI.Hierarchy.ProtocolRAMCatalystDatedPorts
import OAI.Hierarchy.ProtocolRAMCatalystBirthOwner
import OAI.Hierarchy.ProtocolRAMCatalystArchiveTerminal
import OAI.Hierarchy.ProbeCatalystCashEntry

namespace OAI
/-! # The terminal owner ledger on the physical strip-port occurrence rows -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open scoped Classical Fin.CommRing

namespace CatalystArchive
open ColumnWires Calendar
variable {R C H E G : Type*} [Fintype C] [Fintype H] [Fintype E]
variable {balls D k count payload w : ℕ}

section Cash
open LinearAlgebra.SpectralBooks.ChordGraph
variable {F J : Type*} {A B C₀ H₀ R₀ G₀ : Type} [Field F] [Fintype A] [Fintype B] [Fintype C₀] [Fintype H₀]
  [Fintype J] [Nonempty (Fin k)] [Nonempty (Role C₀ H₀ (A⊕B) k)]
  {M ε tree : ℝ} {len : H₀→ℝ} {cap : A→ℝ} {N z d q K : ℕ}
variable {sites : ℕ} [Nonempty (Fin sites)]
  {e : Role C₀ H₀ (A⊕B) k→ Chord sites} {menu : Probe.FixedMenu F e
    (demand (I:=C₀) (H:=H₀) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C₀) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}

omit [Nonempty (Fin k)] in
/-- The same installed signed-cash packet that supplies `cash_entry_word`
supplies the owner entry for the terminal checkout on its native date. -/
theorem PortROM.of_cashEntry (x : StripInput menu w z d q D)
    (ballsAt : R₀ ↪ Fin x.raw.market.rows) (columns : R₀ × C₀ ↪ G₀) (keys : G₀ × Fin k ↪ Fin count)
    (idle : Fin count) (scale : 0<K) (stock : x.Addresses) (catalogue : PacketWidths J) (includeMenu : menu.index→J)
    (widths : ∀i,catalogue.width (includeMenu i)=(menu.packet i).width) (mass : x.board.copies=catalogue.copiesAt K payload)
    (expr : Expr) (dated : Memory w)
    (rom : ∀z,expr.eval dated ((finProdFinEquiv (portCell ballsAt x.ports z)).val:Word w)=
      ((keys (physical columns z)).val:Word w)) :
    PortROM expr dated (cashEntry x ballsAt columns keys idle scale stock catalogue includeMenu widths mass) := by
  unfold cashEntry
  apply PortROM.of_readEntry
  exact rom

end Cash

end CatalystArchive

namespace Calendar.StripChart

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
