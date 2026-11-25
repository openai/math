import OAI.Computability.BorderVNP.PackedFinalTieNatural
import OAI.Computability.BorderVNP.PackedFinalTieTerminal
import OAI.Computability.BorderVNP.PackedBankSortedCell

/-! # Absolute binding words consumed by the final sparse-cell template -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening.PublicCapacity CellAddresses CellAddressCircuit CellAddressPhysical
open ParseBatchSort VPVNP.VerifierNetwork FrozenTape

variable {s : Shape} {np C d k w : ℕ} {σ : Type*} [Fintype σ]
    (F : Fields s.sites s.edges np C d k w σ) (occupied : Fin s.edges → σ) (portUsed : Fin np → Bool)
variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (rows : Rows s N) (ports : P ↪ Fin np) (cell : N.Site → Fin C) (state : N.Site → Site)
    (x : σ → Bool) (rep : Represents N cell (fun v => (state v).size) rows.site rows.edge ports F x)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c (fun v => (state v).size) + suppliedSize N cell c < 2^w)
    (inc : ∀ v, (state v).incoming = incoming N v) (one : 1 < 2^w)
    (live : ∀ i, x (occupied i) = true ↔ i ∈ Set.range rows.edge)
    (used : ∀ i, portUsed i = true ↔ i ∈ Set.range ports)

include rep fit inc one live used in
/-- The ordinary terminal-site codebook and its recovered work fields yield exactly
the natural-cell directory's binding rows for every real host. The records already
contain absolute cell-local starts, so their native fields are read with offset zero. -/
theorem terminal_bindings (ordinal : ∀ i, (F.sites i).val = i.val) :
    (tieSchema s.edges np w).Section ((terminalTape F occupied portUsed).eval x)
      (rows.site.trans Fin.valEmbedding)
      (FinalCell.binding N (fun v => (cell v).val) rows.site rows.edge ports state) := by
  have h := terminal_id_section F occupied portUsed N rows ports cell state x rep fit inc one live used ordinal
  exact ⟨h.owners,fun v => (h.atSite v).trans (congrArg (List.map marked)
    (binding_nat N cell rows.site rows.edge ports state v).symm)⟩

include rep fit inc one live used in
/-- An arbitrary injective physical site codebook can also feed the same natural-cell
template. The public key translation restores the raw site ID before extraction. -/
theorem index_bindings (work : Fin s.sites → Fin w → σ)
    (workRead : ∀ v, value (x ∘ work (rows.site v)) = (state v).work) :
    (tieSchema s.edges np w).Section ((indexTape F work occupied portUsed).eval x)
      (rows.site.trans Fin.valEmbedding)
      (FinalCell.binding N (fun v => (cell v).val) rows.site rows.edge ports state) := by
  have h := indexTape_section F work occupied portUsed one N rows ports cell state rep fit inc workRead live used
  exact ⟨h.owners,fun v => (h.atSite v).trans (congrArg (List.map marked)
    (binding_nat N cell rows.site rows.edge ports state v).symm)⟩

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
