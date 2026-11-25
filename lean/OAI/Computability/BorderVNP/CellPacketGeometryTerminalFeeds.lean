import OAI.Computability.BorderVNP.CellPacketGeometryHistoryOutput
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryTables
import OAI.Computability.BorderVNP.PackedTerminalRetainedEmitter
import OAI.Computability.BorderVNP.PackedFinalTieBinding

/-! # The terminal packet from the installed site program and genuine physical address fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.Terminal

open Crossing Shortening Shortening.PublicCapacity Packing Packing.Inherited FrozenTape
open CellSparse Packet CellAddressCircuit CellAddressPhysical CellAddresses VPVNP.VerifierNetwork ParseBatchSort
open PackedHistoryCircuit.Retained

variable {s : Shape} {n C d k w t : ℕ} {Z H R B E Orig : Type}
variable [Fintype Z] [Fintype H] [Fintype R] [Fintype B] [Fintype E]
variable (F : Fields s.sites s.edges n C d k w Z) (occupied : Fin s.edges → Z) (portUsed : Fin n → Bool)
variable (boxes : Fin s.sites → List (Source.Box Orig))
variable (old : Frame (Z ⊕ H) (Pins R B t)) (fields : Frame (Z ⊕ H) (E × Fin w)) (valid : Z)

/-- Use the chronological, already post-sewn program together with the
absolute final bindings and the physical cell, bit, and box prefix scans. -/
noncomputable def feeds : Feeds (Z ⊕ H) R B (FinalTies.Row s.edges n)
    (FinalTies.Row s.edges n × Fin 9 × Fin w) E s.sites t d k w where
  history := old
  binding := lift (FinalTies.terminalTape F occupied portUsed)
  table := lift ((TerminalTable.bank F boxes).select fun z => TerminalTable.pin z.1 z.2)
  field := fields
  valid := .inl valid

local notation3 "f₀" => feeds F occupied portUsed boxes old fields valid
variable (z : Z → Bool) (h : H → Bool) (cp : 0<C)
local notation3 "x₀" => Sum.elim z h

/-- The three per-site numerical table assumptions of the packet reducer are
actual physical cell, bit and stable box scans. -/
theorem table_values (room : ∀ c, (BankBoxOrdinal.table (fun j => (TerminalTable.cell F cp z j).val) boxes c).length < 2^w) :
    (∀ i, value (fun j => (f₀).table.eval x₀ (i,.inl j)) = (TerminalTable.cell F cp z i).val) ∧
    (∀ i b, value (fun j => (f₀).table.eval x₀ (i,.inr (b,j))) =
      (if b then TerminalTable.boxStart F boxes cp z else TerminalTable.bitStart F z) i) := by
  constructor
  · intro i
    simp only [feeds,lift_eval,Frame.select_eval]
    exact TerminalTable.bank_cell F boxes cp z i
  · intro i b
    cases b
    · simp only [feeds,lift_eval,Frame.select_eval,Bool.false_eq_true,ite_false]
      exact TerminalTable.bank_bits F boxes z i
    · simp only [feeds,lift_eval,Frame.select_eval,ite_true]
      exact TerminalTable.bank_boxes F boxes cp z room i

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (rows : Rows s N) (ports : P ↪ Fin n) (cell : N.Site → Fin C) (state : N.Site → Site)
variable (rep : Represents N cell (fun v => (state v).size) rows.site rows.edge ports F z)
variable (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)

include rep sizeFit in
/-- The true, emitted absolute final incidence tape realizes the entire
site-local binding list of the same sorted network directory. -/
theorem bindings (incoming : ∀ v, (state v).incoming=Inherited.incoming N v) (one : 1<2^w)
    (live : ∀ i, z (occupied i)=true ↔ i∈Set.range rows.edge)
    (used : ∀ i, portUsed i=true ↔ i∈Set.range ports) (ordinal : ∀ i, (F.sites i).val=i.val) :
    (FinalTies.tieSchema s.edges n w).Section ((f₀).binding.eval x₀) (rows.site.trans Fin.valEmbedding)
      (FinalCell.binding N (fun v => (cell v).val) rows.site rows.edge ports state) := by
  have eqn : (f₀).binding.eval x₀ = (FinalTies.terminalTape F occupied portUsed).eval z :=
    funext fun j => lift_eval _ _ _ j
  rw [eqn]
  exact FinalTies.terminal_bindings F occupied portUsed N rows ports cell state z rep sizeFit incoming one live used ordinal

include rep sizeFit in
/-- On every actual host the computed two offsets are precisely those used by
the semantic final directory, including the relabeling of inherited box IDs. -/
theorem starts (fs : Orig → List Factor)
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots rows.site (fun v => (state v).boxes) i)
    :
    (∀ v, TerminalTable.bitStart F z (rows.site v) =
      siteBase N (fun v => (cell v).val) (cell v).val rows.site (fun v => (state v).size) ⟨v,rfl⟩) ∧
    (∀ v, TerminalTable.boxStart F boxes cp z (rows.site v) =
      FinalCell.firstBox rows.site (fun j => (TerminalTable.cell F cp z j).val) state v) := by
  have same i : (boxes i).length = (FinalCell.slots rows.site (fun v => (state v).boxes) i).length :=
    (List.length_map ..).symm.trans (congrArg List.length (resolved i))
  exact ⟨TerminalTable.bitStart_live F N cell rows.site rows.edge ports state rep sizeFit,fun v => by
    simp only [TerminalTable.boxStart,FinalCell.firstBox,same]⟩

end CellPacketGeometry.History.Native.Terminal

end BorderVNP
end Computability
end OAI
