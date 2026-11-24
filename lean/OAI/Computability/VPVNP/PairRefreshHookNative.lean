import OAI.Computability.VPVNP.PairRefreshHookExact
import OAI.Computability.VPVNP.PairTerminalNativeTable

/-! # The selected refresh parser in the compressed pair's physical table

The full eleven-operand vertex image supplies the refresh rows, their register
separation and their return address. A published selected site can therefore
be interpreted using the canonical numerical template itself.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression CompressorRecords VertexImage LiveProgram

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {n hist bits pcs regs : ℕ}
  (R : Site B n hist bits) (constants : Constants) (p q : ℕ) (order : B.Entry ≃ Fin hist)
local notation "segments" => TerminalProgram.nativeSegments B constants p q order
local notation "ties" => RefreshBlockPlan.order B
local notation "stride" => PortRefresh.LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)

/-- The exact hook at the refresh entry of the actual linked vertex image. -/
theorem site_exact_installed (V : Placement segments pcs regs) (M : Machine bits pcs regs 11) (m : Memory bits)
    (contains : Contains V M) (facts : R.Published ties stride M.publicData m) :
    (R.hook ties stride order M.publicData m).ExactOn R.Prepared M (V.entry .refresh) (V.dfsPC 3) V.dfs m := by
  apply R.site_exact ties stride order (V.stage .refresh) V.dfs V.saved (V.localRegs .refresh) (V.dfsPC 3) M m
  · exact stage_linked V M contains .refresh
  · intro i j
    exact V.reg.injective.ne (by simp)
  · intro i j
    exact V.reg.injective.ne (by simp)
  · exact facts

set_option maxHeartbeats 1500000 in
/-- The canonical instruction and register numbering meets the same exact
hook specification for every resident selected site. -/
theorem site_exact_native (pub : Fin 11 → Word bits) (m : Memory bits) (facts : R.Published ties stride pub m) :
    let V := placement segments
    let M := (template segments).instantiate bits pub
    (R.hook ties stride order pub m).ExactOn R.Prepared M (V.entry .refresh) (V.dfsPC 3) V.dfs m := by
  intro V M
  exact R.site_exact_installed constants p q order V M m (template_contains segments pub) facts

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
