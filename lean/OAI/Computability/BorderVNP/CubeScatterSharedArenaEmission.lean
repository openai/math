import OAI.Computability.BorderVNP.CubeScatterSharedArenaFields

/-! # The real shared-range writer from scheduled rows and published data demands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.TeamContraction
open Transmission CubeLengths
open private public_image_word from OAI.Computability.BorderVNP.CubeScatterWriterSources

/-- The same post-data memory supplies the actual source fields, the genuine
size/disjointness bounds, and the emitted seven words of every compact strict
row. Each returning shared-emitter execution has the specified image. -/
theorem Layout.shared_emission (a : Layout) {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (bank : Bank w) (team : ℕ) (axis : Fin (a.n+1)) (owner : Fin a.header.d → ℕ)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ)
    (m₀ m₁ m₂ : Memory w) (cells : CellBanks.Layout) (pairs : PairDirectory.Layout)
    (seed : a.ScannerWords (pub 0).val team axis.val owner (readings pub) (readings m₀) rows)
    (cellWords : readings m₁ = cells.written (readings m₀) cells.cells)
    (pairWords : PairDirectory.Image pairs (readings m₁) pairs.count (readings m₂))
    (frameLow : (pub 0).val+112 ≤ a.header.header) (axes : a.header.a = a.n+1)
    (cellDir : cells.dest = a.hostDirectory) (pairDir : pairs.table = a.pairDirectory)
    (cap : ∀ p j, rows p j ≤ a.header.cap) (high : a.stop < 2^w) :
    let data := DataWriter.layout (readings pub) (readings m₂)
    let m := DataWriter.publish data pub m₂
    let g := a.sharedRows (pub 0).val axis.val data.count
    data.output = a.records → data.count+a.header.d.choose 2 ≤ a.maxRows →
      g.Fits w (readings m) ∧ g.Fields (readings m) ∧
        TestRun pub mac SharedRows.program bank m (SharedRows.budget a.header.d) True
          (fun z => g.Emitted (readings m) z.mem) := by
  intro data m g output space
  have table : StoredRows (readings m) (a.header.header+13+a.header.entries) rows := by
    intro x y j
    let k := entryOrder a.header.d (a.n+1) ((x,y),j)
    have key : k.val < a.header.d*a.header.d*(a.n+1) := k.isLt
    have below := a.declaration_before_schedule axes
    have low : a.header.header+13+a.header.entries+k.val < a.pairDirectory := by
      have ow := below.trans ((min_le_right ..).trans (min_le_right ..))
      unfold Layout.pairDirectory; omega
    have other : a.header.header+13+a.header.entries+k.val ≠ (pub 0).val+13 := by omega
    exact (public_image_word a (readings m₀) pub cells pairs data m₁ m₂ cellWords pairWords cellDir pairDir output _ low other).trans
      (seed.table x y j)
  have fits := a.shared_fits w (pub 0).val data.count axis (readings m) rows table cap frameLow axes space high
  have count : data.count < 2^w := by
    have hc := fits.countFit
    change data.count+a.header.d.choose 2 < _ at hc; omega
  have fields := a.shared_fields pub team axis.val owner rows m₀ m₁ m₂ cells pairs seed cellWords pairWords
    frameLow cellDir pairDir output count
  exact ⟨fits,fields,(SharedRows.run_program pub mac g bank m fits rfl fields).asTest (by decide)⟩

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
