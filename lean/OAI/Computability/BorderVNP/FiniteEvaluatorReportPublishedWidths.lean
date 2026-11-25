import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenProfile

/-! # Physical canonical widths after private placement and demand publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open VPVNP.BurstRAM RoutingISA Crossing CellAddresses CellAddressCircuit CellAddressPhysical

variable {dim sites cables ports cells cellBits lenBits bits w frame origin next gap : ℕ}
variable {P σ : Type*} [Fintype P] [Fintype σ] {sizes : P → ℕ} (N : Network dim P sizes)
variable (cell : N.Site → Fin cells) (aux : N.Site → ℕ)
variable (siteID : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin cables) (portID : P ↪ Fin ports)
variable (F : Fields sites cables ports cells cellBits lenBits bits σ) {x : σ → Bool}
variable (D : Directory.Layout) (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
variable (pp lp : ℕ → ℕ × ℕ) {profile placed : Memory w}
local notation "tables" => bases origin cables cells D.entries
local notation "plan" => privateLayout frame origin cables cells D.entries D.description gap

/-- Private placement and demand publication preserve the entire cable
geometry and canonical-width prefix, including every occupied and unused row. -/
theorem published_geometry {D : Directory.Layout} {frame origin cables cells next gap : ℕ}
    (pp lp : ℕ → ℕ × ℕ) {profile placed : Memory w}
    (place : (privateLayout frame origin cables cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (a : ℕ) (start : origin ≤ a) (stop : a < (bases origin cables cells D.entries).counters) :
    readings (Directory.ISA.publish placed frame next (D.directory pp lp)) a=readings profile a := by
  have packed := Nat.mul_le_mul_left 7 (D.directory_length_le pp lp)
  dsimp only [bases] at stop
  have old := place.outside a (fun j _ => by dsimp only [privateLayout,bases]; omega)
    (Or.inl (by dsimp only [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]; omega))
  exact (congrArg Fin.val (CableTriples.published_outside placed frame next (D.directory pp lp) a
    (by omega) (.inr (by omega)))).trans old

/-- Publishing the sparse demand directory preserves the native canonical
supplied widths. Each width is the original network's true sum of supplied
bits at this cell, also for a cell with no incoming data. -/
theorem Image.published_supplied
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings profile))
    (net : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fits : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (place : (plan).Image (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin) (c : Fin cells) :
    readings (Directory.ISA.publish placed frame next (D.directory pp lp))
      ((tables).ends+2*cables+c.val)=suppliedSize N cell c := by
  have orig := (image.placed N cell aux siteID edgeID portID F net codes fits original live origin (readings profile)).2.1 c
  let a := (tables).ends+2*cables+c.val
  have hi := c.isLt
  have addr : a=(tables).supplied+c.val := by dsimp only [a,bases]; rw [Nat.mul_comm cables 2]
  exact (published_geometry pp lp place low reserve a (by dsimp only [a,bases]; omega)
    (by dsimp only [a,bases]; omega)).trans (addr ▸ orig)

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
