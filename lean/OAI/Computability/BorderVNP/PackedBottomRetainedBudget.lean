import OAI.Computability.BorderVNP.PackedSeedCoreChoices
import OAI.Computability.BorderVNP.PackedBankMergedLoad

/-! # Actual retained bottom bundles meet the supplemented private-call bounds -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing Shortening CellSparse CellAddresses Inherited
open scoped Classical

variable {D : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → ℕ) (state : N.Site → Site)
variable {s : ℕ} (siteID : N.Site ↪ Fin s) (host : J ↪ N.Site) (bundle : J → Bundle)

/-- The delivered metadata identifies an actual retained birth at its true final
cell offset. Its one-copy table, copied box record and sparse source count all
come from the same original. -/
def RetainedBirths : Prop :=
  ∀ j, (bundle j).header.boxBase = siteBase N cell (cell (host j)) siteID (fun v => (state v).size) ⟨host j,rfl⟩ ∧
    ∃ birth : Site, (bundle j).Birth birth ∧ Nonempty (birth.Retention (state (host j)))

/-- The actual prewired private payload and true original hosts supply the
three numerical premises of the supplemented cell evaluator. Its clock counts
the stable list of sparse rows, and its bit budget counts their true copies. -/
theorem retained_call_bounds (inventory : RetainedBirths N cell state siteID host bundle)
    (c M E gadgets digits : ℕ) (origins : List J) (nd : origins.Nodup)
    (owner : ∀ j ∈ origins, cell (host j) = c)
    (positive : ∀ j ∈ origins, 0 < (bundle j).header.copies ∧ 0 < (bundle j).header.stride)
    (incoming : ∀ v, (state v).incoming = Inherited.incoming N v)
    (publicLoad : localRecords N false (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
      (fun v => cell v = c) ≤ M)
    (expandedLoad : localRecords N true (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
      (fun v => cell v = c) ≤ M) (room : 3*M+gadgets*digits ≤ E) :
    let bs := origins.map bundle
    (bs.map (fun x => count x.factors)).sum + bs.length ≤ 2*(M+1) ∧
      suppliedSize N cell c + gadgets*digits + (bs.map Bundle.useBits).sum ≤ E ∧
      ∀ x ∈ bs, count x.factors ≤ x.header.cap ∧ x.header.copies ≤ 4*(M+E+1)^3 ∧
        x.header.boxBase+x.header.orig+x.header.cap ≤ 4*(M+E+1)^3 := by
  intro bs
  have operands : RetainedOperands N cell state siteID host bundle := by
    intro j
    obtain ⟨atHost,birth,matchBirth,ret⟩ := inventory j
    exact ⟨atHost,birth,matchBirth.work,ret⟩
  have cap (j : J) : count (bundle j).factors ≤ (bundle j).header.cap := by
    obtain ⟨_,_,matchBirth,_⟩ := inventory j
    exact matchBirth.capacity
  have stride (j : J) : (bundle j).header.stride = bottomStride (bundle j).header.orig (bundle j).header.cap := by
    obtain ⟨_,_,matchBirth,_⟩ := inventory j
    exact matchBirth.stride
  have rows := supplemental_rows_le N cell state host bundle c origins nd owner (by
    intro j hj
    obtain ⟨_,birth,matchBirth,ret⟩ := inventory j
    obtain ⟨wire,table⟩ := matchBirth.boxes
    exact ⟨birth,_,ret,table,by simp⟩)
  have uses := supplemental_uses_le N cell state host bundle c siteID operands cap stride origins nd owner
  have bank := (merged_bank_capacity N state cell c incoming).trans (Nat.mul_le_mul_left 3 expandedLoad)
  have scale : M+E+1 ≤ (M+E+1)^3 := Nat.le_self_pow (by decide) _
  constructor
  · exact (rows.trans publicLoad).trans (by omega)
  constructor
  · dsimp only [bs]
    omega
  · rintro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    obtain ⟨hc,hs⟩ := positive j hj
    have endAt := retained_box_end N cell state siteID host bundle operands j
    have scalar := retained_report_scalar N cell state siteID host bundle operands j (bundle j).header.cap
      le_rfl (stride j) hc
    rw [owner j hj] at endAt scalar
    have mult := Nat.mul_le_mul_left (bundle j).header.copies hs
    rw [Nat.mul_one] at mult
    exact ⟨cap j,by omega,by omega⟩

end Packing.BottomReports

namespace Packing.DeckGrid

open GridPlacement Cover

/-- Nonempty batch parameters give a nonempty public original work stride,
including at tiles with no live private sources. -/
theorem seedSiteCapacity_pos {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (q depth : ℕ) :
    0 < seedSiteCapacity n r q depth := by
  let V := Fintype.card (Fin q → Deck (depth+2))
  have hv : 0 < V := Fintype.card_pos
  have slots : r*n ≤ V*blockWidth (r*n) V := (ceilDiv_le_iff_le_mul hv).mp le_rfl
  have block : 0 < blockWidth (r*n) V := by
    by_contra! h
    have hz : blockWidth (r*n) V = 0 := by omega
    rw [hz,Nat.mul_zero] at slots
    exact (Nat.mul_pos hr hn).not_ge slots
  change 0 < blockWidth (r*n) V + _ + _
  omega

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
