import OAI.Computability.VPVNP.PairShrinkScanCoefficient
import OAI.Computability.VPVNP.PairShrinkNodeRates
import OAI.Computability.VPVNP.PairShrinkPrologueBudget
import OAI.Computability.VPVNP.PairRefreshHookBudget
import OAI.Computability.VPVNP.PairSelectedLevelChecks

/-! # A single probe coefficient for the installed terminal role programs -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RatedRoles

open BurstRAM PrivateRAM Compression CompressorRecords DFS LocalHistory
open NetworkKernel NodeArguments TreeDecode

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {labels : ℕ}
    (names : B.Entry ≃ Fin labels)

/-- Each entry is the probe rate for the native program at its role tag.
The shrinking entry includes the full resident map loop and its prologue. -/
noncomputable def roleRate : NodeDispatch.Role → ℕ
  | .leaf => 2
  | .shrink => ShrinkNodeCost.probeRate S (ShrinkRole.MapWitness.scanCoefficient B names)
      (ShrinkNodeCost.prologueCoefficient B)
  | .refresh =>
      RefreshHook.Site.scan B (RefreshBlockPlan.order B) (RefreshBlockPlan.shape B).stride names

/-- This coefficient is fixed by the templates and their label ordering. -/
noncomputable def scan : ℕ :=
  max 2 (max (roleRate B names .shrink) (roleRate B names .refresh))

theorem role_le (role : NodeDispatch.Role) : roleRate B names role ≤ scan B names := by
  cases role with
  | leaf => exact le_max_left ..
  | shrink => exact (le_max_left ..).trans (le_max_right ..)
  | refresh => exact (le_max_right ..).trans (le_max_right ..)

variable {w endAddr n : ℕ}

/-- The local job bound is preserved for the same events and scratch update. -/
theorem job (role : NodeDispatch.Role) (j : VisitPath w endAddr)
    (checked : ordinalJobCost n 1 (roleRate B names role) j) :
    ordinalJobCost n 1 (scan B names) j :=
  ⟨checked.1.trans (Nat.mul_le_mul_right _ (role_le B names role)),checked.2⟩

variable {geometry rootFields leaf shrink refresh : Segment} {p regs : ℕ}
    {A : Placement (segments geometry rootFields leaf shrink refresh) p regs}
    {M : Machine w p regs 11}
    {m : Memory w} {allow : ℕ → Prop} {R : Type*} [CommRing R] {f : B.Entry → R}
    {valid : List Packet → Scratch w endAddr → Prop} {hist : Scratch w endAddr → B.Entry → ℕ}

/-- The decoded jobs, their exponents and their complete source reports stay
together under the common scan allowance. -/
theorem emits (role : NodeDispatch.Role) {N : Network} {P : SiteParsers f N}
    {input : Packets N} {jobs : JobsFor P}
    (native : Emits valid hist (JobGuard A M m allow
      (ordinalJobCost n 1 (roleRate B names role))) P input jobs) :
    Emits valid hist (JobGuard A M m allow (ordinalJobCost n 1 (scan B names))) P input jobs :=
  emits_withCost native (job B names role)

/-- The observed two-probe leaf bound and its measured private clock give
the common allowance on every emitted leaf visit. -/
theorem leafEmits {N : Network} {P : SiteParsers f N}
    {input : Packets N} {jobs : JobsFor P}
    (hn : 1 ≤ n) (native : Emits valid hist (JobGuard A M m allow
      (fun j => countProbes j.trace ≤ 2 ∧ j.trace.length + 17 ≤ n ^ 40)) P input jobs) :
    Emits valid hist (JobGuard A M m allow (ordinalJobCost n 1 (scan B names))) P input jobs :=
  emits_withCost native (fun _ h => leaf_ordinal_cost hn (role_le B names .leaf) h)

/-- The selected pass keeps its row, parser and emitted jobs when its
role-specific rate is charged to the common coefficient. -/
theorem levelChecks (role : NodeDispatch.Role) {hf : B.IsSolution f} {hook : HookParser w endAddr}
    {cap base : ℕ} {v : SelectedLevel B f hf}
    (native : LevelChecks B f hf hook valid hist (JobGuard A M m allow
      (ordinalJobCost n 1 (roleRate B names role))) cap base v) :
    LevelChecks B f hf hook valid hist (JobGuard A M m allow
      (ordinalJobCost n 1 (scan B names))) cap base v :=
  ⟨native.1,emitsNode_withCost native.2 (job B names role)⟩

end PairSimulation.VertexImage.RatedRoles

end VPVNP
end Computability
end OAI
