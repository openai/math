import OAI.Computability.BorderVNP.CubeTeamOwnedCanonicalPrefix

/-! # Accepted group capacities on each real return from label selection -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube CubeHeaderInstall

/-- Inputs used by the signed writer schedule on an honest, already published
physical table. The budget refers to the memory reached by the native prefix. -/
structure CanonicalInput {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (f : BroadcastFrame) (a : CubeArena.Layout) (ext : Fin 81 → Word w) (raw : List Bool)
    (R X index : ℕ) (reg : Bank w) (m : Memory w) : Prop where
  /-- The copied public broadcast and reference operands. -/
  boot : BootPins pub f ext raw m
  /-- Sparse endpoints, arithmetic and scratch room for label selection. -/
  fit : LabelPrefixFits (pub 0).val w (readings m)
  /-- Number of physical cells in the published frame. -/
  cells : readings m ((pub 0).val+11) = a.cells
  /-- The physical budget holds on every returned selected memory. -/
  guard : ∀ {tr mid selected}, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare)
    reg m tr mid selected →
    let input := powerHeaderImage a f.dst (readings selected)
    let wl := weightLayout a (pub 0).val index
    (∑ j ∈ Finset.range a.header.d, wl.weight input j) < 2^w ∧ capacities wl (teamLayout a R) X input

/-- The two public selection passes have unique returned memory, so a capacity
proof on one reached state covers every native return. -/
theorem canonicalInput_of_selected {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {f : BroadcastFrame} {a : CubeArena.Layout} {ext : Fin 81 → Word w} {raw : List Bool}
    {R X index : ℕ} {reg : Bank w} {m selected : Memory w} {tr mid}
    (boot : BootPins pub f ext raw m) (fit : LabelPrefixFits (pub 0).val w (readings m))
    (cells : readings m ((pub 0).val+11) = a.cells)
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg m tr mid selected)
    (bounds : let input := powerHeaderImage a f.dst (readings selected)
              let wl := weightLayout a (pub 0).val index
              (∑ j ∈ Finset.range a.header.d, wl.weight input j) < 2^w ∧ capacities wl (teamLayout a R) X input) :
    CanonicalInput pub mac f a ext raw R X index reg m := by
  refine ⟨boot,fit,cells,?_⟩
  intro es t mt other
  obtain ⟨_,_,rfl⟩ := other.unique_of_deterministic (by decide) run
  exact bounds

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
