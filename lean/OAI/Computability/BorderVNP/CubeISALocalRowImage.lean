import OAI.Computability.BorderVNP.CubeISALocalRowArena
import OAI.Computability.BorderVNP.CubeISAHeaderGeometryRun
import OAI.Computability.BorderVNP.RoutingISACubePowers

/-! # Row setup words from the actual power-table and public-header returns

The program installs powers first and then writes the secondary header, its
decoded coordinate, the dense row words and the column totals. All these
writes have known addresses in the concrete cube arena.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally CubeHeaderInstall

/-- The shared-memory image of the actual secondary-header write and declaration decoding. -/
def headerImage (stat : Inputs) (n width saved : ℕ) (old : ℕ → ℕ) : ℕ → ℕ :=
  (stat.decoder saved).finalImage (stat.image n width old)

/-- Every address before the header or from the packet bank onward survives
both header phases. -/
theorem headerImage_outside (stat : Inputs) (n width saved : ℕ) (old : ℕ → ℕ)
    (x : ℕ) (outside : x < stat.header ∨ stat.packetBase ≤ x) :
    headerImage stat n width saved old x = old x := by
  let l := stat.decoder saved
  have cnt : l.entries = stat.entries := rfl
  have endBank : stat.packetBase = stat.header+13+2*stat.entries+stat.a := rfl
  have high : stat.header+13 ≤ stat.packetBase := by omega
  have dense : l.dense = stat.header+13+stat.entries := rfl
  have sums : l.totals = stat.header+13+2*stat.entries := rfl
  have ah : l.a = stat.a := rfl
  change l.finalImage _ x = old x
  rw [l.finalOutside _ (by change x ≠ stat.header+5; omega) (by omega) (by omega)]
  simp [Inputs.image,show ¬(stat.header ≤ x ∧ x < stat.header+13) by omega]

/-- Static secondary fields other than the decoded grouping coordinate retain
the exact contents written by the native initializer. -/
theorem headerImage_field (stat : Inputs) (n width saved : ℕ) (old : ℕ → ℕ)
    (k : ℕ) (hk : k < 13) (hk5 : k ≠ 5) :
    headerImage stat n width saved old (stat.header+k) = stat.value n width k := by
  let l := stat.decoder saved
  change l.finalImage _ _ = _
  rw [l.finalOutside _ (by change stat.header+k ≠ stat.header+5; omega)
    (.inl (by change stat.header+k < stat.header+13+stat.entries; omega))
    (.inl (by change stat.header+k < stat.header+13+2*stat.entries; omega))]
  simp [Inputs.image,hk]

/-- Compose the exact native power installation and the header return in their
actual order in the fixed public scheduling program. -/
def powerHeaderImage (a : CubeArena.Layout) (saved : ℕ) (old : ℕ → ℕ) :=
  headerImage a.header a.n (selectorWidth a.n a.K a.h) saved
    (CubePowers.image a.header.d a.powerBase (a.n+1) old)

/-- Every primary frame read, secondary header word and positional divisor of
local row setup is supplied by the two real installed images. The primary
metadata comes from the pinned physical frame before the power program. -/
theorem loaded_of_powerHeader (a : CubeArena.Layout) (pub : Arg → ℕ) (saved : ℕ) (old : ℕ → ℕ)
    (stat : a.header.Loaded pub old) (axes : a.header.a = a.n+1)
    (bc : frameField pub old 61 = a.h*a.b) (p62 : frameField pub old 62 = a.powerBase)
    (before : pub 0+112 ≤ a.header.header) :
    let l := rowLayout a.header a.b a.h a.powerBase
    let m := powerHeaderImage a saved old
    l.Loaded a.n pub m ∧ m a.header.header = a.header.header+13 ∧
      m (a.header.header+1) = a.header.header+13+a.header.entries := by
  intro l m
  let pw := CubePowers.image a.header.d a.powerBase (a.n+1) old
  have sep := arenaExtents a
  have ep : a.header.packetBase ≤ a.powerBase := by
    have := sep.1
    have := sep.2.1
    change a.packetEnd+8+a.h ≤ a.powerBase at this
    omega
  have hp : a.header.header+13 ≤ a.header.packetBase := by unfold Inputs.packetBase; omega
  have primary (k : ℕ) (hk : k < 112) : frameField pub m k = frameField pub old k := by
    change headerImage a.header a.n (selectorWidth a.n a.K a.h) saved pw (pub 0+k) = old (pub 0+k)
    rw [headerImage_outside _ _ _ _ _ _ (.inl (by omega))]
    simp only [pw,CubePowers.image,ite_eq_right (show ¬(a.powerBase ≤ pub 0+k ∧ pub 0+k-a.powerBase < a.n+1) by omega)]
  have field (k : ℕ) (hk : k < 13) (hk5 : k ≠ 5) :
      m (a.header.header+k) = a.header.value a.n (selectorWidth a.n a.K a.h) k :=
    headerImage_field _ _ _ _ _ _ hk hk5
  have power (j : ℕ) (hj : j ≤ a.n) : m (a.powerBase+j) = a.header.d^j := by
    change headerImage a.header a.n (selectorWidth a.n a.K a.h) saved pw (a.powerBase+j) = _
    rw [headerImage_outside _ _ _ _ _ _ (.inr (by omega))]
    simp [pw,CubePowers.image,hj]
  exact ⟨⟨(primary 59 (by decide)).trans stat.d,(primary 60 (by decide)).trans (stat.a.trans axes),
    (primary 61 (by decide)).trans bc,(primary 62 (by decide)).trans p62,
    (primary 63 (by decide)).trans stat.header,field 7 (by decide) (by decide),
    field 8 (by decide) (by decide),power⟩,field 0 (by decide) (by decide),field 1 (by decide) (by decide)⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
