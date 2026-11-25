import OAI.Computability.BorderVNP.PackedTerminalSignedIndexRange
import OAI.Computability.BorderVNP.PackedBundleSortPhysical

/-! # Actual marked-sort dimensions of the resident original bundle banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open Inherited.FrozenTape CellPacketGeometry.History CellSparse.Packet

/-- The six words of each original bundle are sorted between the initial
and final marker of each cell. Both RAM banks use this common power-of-two
rectangle. -/
def markedDepth (cells originals : ℕ) : ℕ := Nat.clog 2 (cells+6*originals+cells)

/-- The signed scalar volume already pays for every original descriptor and
every cell marker. Thus the real sort depth fits a native index, and both
padded banks together use at most 32 routing rows of words per row. -/
theorem signed_header_depth {Row B U V : Type} {sites cells J g digits native rows : ℕ}
    (S : Schema Row B) (T : Schema U V) (boxes : Fin sites → List (Source.Box (Fin J)))
    (one : 1 ≤ rows) (cs : cells ≤ rows) (js : J ≤ rows)
    (room : 256*sourceVolume S T boxes (FinalReports.Spare.reports (C:=cells) (g:=g)
      (digits:=digits) (E:=Fin J)) < 2^native) :
    let b := markedDepth cells J
    cells+6*J+cells ≤ 2^b ∧ b ≤ native ∧ 2^b ≤ 16*rows ∧ 2^b+2^b ≤ 32*rows := by
  intro b
  let len := cells+6*J+cells
  let volume := sourceVolume S T boxes (FinalReports.Spare.reports (C:=cells) (g:=g)
    (digits:=digits) (E:=Fin J))
  have counts : len ≤ 8*volume := by
    dsimp only [len,volume]; rw [FinalReports.Spare.sourceVolume_eq]
    simp only [Fintype.card_fin]
    omega
  have padded : 2^b ≤ 16*rows := by
    by_cases empty : len=0
    · change 2^Nat.clog 2 len ≤ _
      simp [empty]; omega
    · exact (TeamSorting.padding_lt_twice (Nat.pos_of_ne_zero empty)).le.trans (by dsimp only [len]; omega)
  have fits : len ≤ 2^native := counts.trans (by change 256*volume < 2^native at room; omega)
  exact ⟨Nat.le_pow_clog (by decide : 1<2) len,Nat.clog_le_of_le_pow fits,padded,by omega⟩

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
