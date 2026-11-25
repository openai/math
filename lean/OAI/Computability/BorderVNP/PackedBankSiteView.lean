import OAI.Computability.BorderVNP.PackedCellWireView
import OAI.Computability.BorderVNP.ShortenPhysicalHookBank

/-! # Physical word views at the two ends of a sewn cable

Each cell supplies its internal guesses, staging bits and received words. Reading
the packed port at either end gives the corresponding site-local physical
assignment at the same cable lane.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankSite

open Crossing CellSparse Shortening.StaticRows
open scoped Classical

variable {D : ℕ} {P C : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → C)
variable (aux : N.Site → ℕ)

/-- The three blocks of the arbitrary bit assignment in each owning cell. -/
structure CellBanks where
  /-- Internal cable bits are guessed once per cell. -/
  guessed : ∀ c, Fin (CellAddresses.guessedSize N cell c) → Bool
  /-- Auxiliary words reserved for all sites in the cell. -/
  staged : ∀ c, Fin (CellAddresses.siteSize N cell c aux) → Bool
  /-- Endpoint and exterior data supplied to the owning cell. -/
  supplied : ∀ c, Fin (CellAddresses.suppliedSize N cell c) → Bool

variable {N cell aux} (W : CellBanks N cell aux) {ne np : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)

/-- The bank queried by a sparse record at a fine site. -/
noncomputable def CellBanks.read (v : N.Site) : ℕ → Bool :=
  let c := cell v
  lookup (CellAddresses.bank N cell c aux (W.guessed c) (W.staged c) (W.supplied c))

/-- The complete assignment obtained by extending the site's local physical wire values. -/
noncomputable def CellBanks.wires (v : N.Site) : N.Assignment :=
  let c := cell v
  CellAddresses.assignment N cell c edgeID portID (W.guessed c) (W.supplied c)

variable (N cell aux)

/-- The actual cable word base at the named source or destination. -/
noncomputable def cableBase (z : N.Edge) (src : Bool) : ℕ :=
  let v := incidentSite N z src
  CellAddresses.wireBase N cell (cell v) edgeID portID aux ⟨v,rfl⟩ (incidentWire N z src)

/-- The canonical contiguous bit at either end is precisely the chosen physical
assignment. Self-loops share their one guessed cable word. -/
theorem cable_read (z : N.Edge) (src : Bool) (k : Fin (N.width z)) :
    W.read (incidentSite N z src) (cableBase N cell aux edgeID portID z src+k.val) =
      W.wires edgeID portID (incidentSite N z src) z k := by
  let v := incidentSite N z src
  exact CellAddresses.assignment_at N cell (cell v) edgeID portID aux (W.guessed _) (W.staged _) (W.supplied _)
    ⟨v,rfl⟩ (incidentWire N z src) k

end Packing.BankSite

end BorderVNP
end Computability
end OAI
