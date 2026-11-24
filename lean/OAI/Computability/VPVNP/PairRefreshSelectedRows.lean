import OAI.Computability.VPVNP.PairRefreshSelectedParser
import OAI.Computability.VPVNP.PairRefreshHookNative

/-! # Exact execution of the chronological refresh parser on the native table -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

set_option maxHeartbeats 1500000
open scoped Fin.CommRing

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles ShrinkRoleDirectory DFS LiveProgram VertexImage

variable {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → K} {hf : B.IsSolution f}
  (n hist w start positions blocks width : ℕ) (leaf : TaggedLayer) (passes : List (SelectedLevel B f hf))
  (room : Rooms n hist w start positions blocks leaf passes) (order : B.Entry ≃ Fin hist) (m : Memory w)
local notation "site₀" => rowSite n hist w start positions blocks width leaf passes room
local notation "reader₀" => SelectedRows.parser n hist w start positions blocks width leaf passes room order
local notation "ready₀" => Prepared n hist w start positions blocks width leaf passes room
local notation "ties₀" => RefreshBlockPlan.order B
local notation "stride₀" => PortRefresh.LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)
variable (fit : layerBase B.recordLimit (endAddress (BlockProgram.layout B start positions blocks))
    (leaf :: outputTags passes) (passes.length + 1) ≤ 2 ^ w)

variable (constants : Constants) (p q : ℕ) {pcs regs : ℕ}
local notation "segments₀" => TerminalProgram.nativeSegments B constants p q order
variable (V : Placement (TerminalProgram.nativeSegments B constants p q order) pcs regs) (M : Machine w pcs regs 11)

include fit in
/-- At any prepared node, success and rejection of the chronological parser
are those of the fixed instruction table on the supplied choice tape. -/
theorem exactOn (contains : Contains V M)
    (published : ∀ x : Row passes, ((site₀) x).Published (ties₀) (stride₀) M.publicData m) :
    ((reader₀) M.publicData m).ExactOn (ready₀) M (V.entry .refresh) (V.dfsPC 3) V.dfs m := by
  have read := read_at n hist w start positions blocks width leaf passes room order M.publicData m fit
  have exactLocal (x : Row passes) := ((site₀) x).site_exact_installed constants p q order V M m contains (published x)
  constructor
  · intro node s ready bits job tail result
    obtain ⟨x, hx⟩ := ready
    rw [read x node s hx bits] at result
    exact (exactLocal x).success node s hx bits job tail result
  · intro node bits c top pending ready pc nodeEq stack ptr h5 h6 one failed
    obtain ⟨x, hx⟩ := ready
    rw [read x node _ hx bits] at failed
    exact (exactLocal x).reject node bits c top pending hx pc nodeEq stack ptr h5 h6 one failed

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
