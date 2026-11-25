import OAI.Computability.BorderVNP.DiagonalTallyAllocatedTaskSource

/-! # The delivered host and report bits through the typed producer and descriptor patches -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM CellPacket.Supplement.Batch TypedTaskBuilder

/-- Each raw word of the live host-bank interval, including its already written report
tail, survives both the seven-word task producer and the native supplemental patch loop.
The reserved descriptor positions lie below the host bank and the merged counters,
compact task table and call directory lie above it. -/
theorem supplement_cell_word {w : ℕ} {Site : Type} (rows : CellControlRows.Layout)
    (old next : Memory w) (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ)
    (extra : ℕ → List CellSparse.Record) (room : rows.toLayout.Room (readings old) w)
    (image : readings next=rows.toLayout.published (readings old))
    (span : ∀ c < rows.cells, readings old (rows.sorted+rows.padded+(rows.stops+c))-readings old (rows.sorted+rows.padded+c)-1 =
      3*((placed c).parts.length+3))
    (bank stop : ℕ) (lo : rows.sorted+rows.padded ≤ bank ∧ rows.frame+91 ≤ bank)
    (hi : stop ≤ rows.merged ∧ stop ≤ rows.tasks ∧ stop ≤ rows.calls)
    {addr : ℕ} (mem : bank ≤ addr ∧ addr < stop) :
    let owned := produced rows (readings old) placed geom extra
    let count := rows.before (readings old) rows.cells
    written next (fun i => (owned i).cell) count addr = old addr := by
  intro owned count
  apply (preserve next _ (i:=0) (Nat.zero_le count) addr ?_).trans
  · apply Fin.ext
    change readings next addr = readings old addr
    rw [image,task_published_outside]
    change ¬((rows.tasks ≤ addr ∧ addr < _) ∨ (∃ c < rows.cells,addr=rows.calls+3*c) ∨ addr=rows.frame+90)
    rintro (⟨_,_⟩|⟨c,_,_⟩|_) <;> omega
  · intro i _ ix
    obtain ⟨merged,_,tail,_⟩ := produced_addresses rows (readings old) placed geom extra room ix span
    change (owned i).layout.merged=rows.merged+_ at merged
    change (owned i).layout.tail+12 < rows.sorted+rows.padded at tail
    change addr ≠ (owned i).layout.merged ∧ (_ ∨ (owned i).layout.tail+12 ≤ addr)
    exact ⟨by omega,Or.inr (by omega)⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
