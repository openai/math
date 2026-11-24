import OAI.Computability.VPVNP.PairRefreshHookNative
import OAI.Computability.VPVNP.PairRefreshGuardLayout
import OAI.Computability.VPVNP.PairRefreshHookWrites
import OAI.Computability.VPVNP.PairRefreshHookBudget
import OAI.Computability.VPVNP.PairDispatchedRowEffects

/-!
# The guarded refresh visit at the physical role dispatcher

The role tag, the placed node's source ranges and its accepted native parser
determine one DFS job. The linked execution of that job preserves external
memory, avoids both scheduler control cells, and satisfies the ordinal work
and probe bounds at all sufficiently large lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace
open PortRefresh NewSlots NodeArguments TreeDecode VertexImage DFS
open TraversalControllerInputs LiveProgram Filter
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {hist : ℕ} (order : B.Entry ≃ Fin hist)

local notation "ties" => RefreshBlockPlan.order B
local notation "stride" => LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)

variable (constants : Constants) (p q : ℕ)
local notation "segments" => TerminalProgram.nativeSegments B constants p q order

/-- All parts of the guard refer to the same role job recovered by this
successful parse, including its exact read support and its enclosing dispatch. -/
theorem eventually_dispatched_guard :
    ∀ᶠ n : ℕ in atTop, ∀ {w pcs regs : ℕ} (R : Site B n hist w)
      (V : Placement segments pcs regs) (M : Machine w pcs regs 11) (m : Memory w)
      (start positions blocks : ℕ)
      (prev next : Fin (BlockProgram.layout B start positions blocks).levels),
      Contains V M → R.Published ties stride M.publicData m →
      GuardLayout B R M.publicData m start positions blocks prev next →
      NodeDispatch.role (m (R.roleOffset + word R.parent).val) = .refresh →
      R.later ≤ (S.steps + 1) * (n.log2 + 1) →
      ∀ (power scanCap : ℕ), 1 ≤ power → scan B ties stride order ≤ scanCap →
      ∀ (s : Scratch w n) (bs tail : List Bool) (body : VisitPath w n),
        R.Prepared (word R.parent) s →
        (R.hook ties stride order M.publicData m).read (word R.parent) s bs = some (body, tail) →
        let job := dispatchJob m R.roleOffset (word R.parent) s body
        job.enabled s ∧ JobGuard V M m (TerminalLink.workerCell (TerminalLink.header M.publicData))
          (ordinalJobCost n power scanCap) job := by
  filter_upwards [eventually_ordinal_cost B ties stride order] with n clock
  intro w pcs regs R V M m start positions blocks prev next installed facts layout tag later
    power scanCap hp hs s bs tail body prepared hit
  let pub := M.publicData
  let node : Word w := word R.parent
  let job := dispatchJob m R.roleOffset node s body
  have native := (R.site_exact_installed constants p q order V M m installed facts).success
    node s prepared bs body tail hit
  obtain ⟨⟨out, rest⟩, found, equal⟩ := Option.map_eq_some_iff.mp hit
  have eqBody : body.trace = out.trace := by
    exact (congrArg VisitPath.trace (Prod.mk.inj equal).1).symm
  have eqRest := (Prod.mk.inj equal).2
  subst rest
  have rawMem : after m body.trace = m :=
    eqBody ▸ R.read_after ties stride order pub m found
  have rawRead := R.read_worker_layout order pub m start positions blocks prev next facts
    layout.size layout.below layout.headerFit layout.oldHead layout.newHead layout.scratch
    layout.oldCols layout.newCols layout.levels layout.parentBefore layout.listBefore
    prepared.1 found
  let allowed := TerminalLink.workerCell (TerminalLink.header pub)
  have rawGuard : RoleJobGuard V M m .refresh allowed (fun _ => True) body :=
    ⟨native.2.2.2, rawMem, eqBody ▸ rawRead, trivial⟩
  have tagCell : allowed (R.roleOffset + node).val :=
    TerminalLink.workerCell_of_lt (by
      change (TerminalLink.header M.publicData).val + 31 < 2 ^ w
      have := layout.headerFit
      omega) layout.tagBefore
  have small := clock R pub m R.roleOffset node s bs out tail job later found
    (congrArg (dispatchEvents m R.roleOffset node ++ ·) eqBody)
  have bound : ordinalJobCost n power scanCap job := by
    refine ⟨small.1.trans (Nat.mul_le_mul hs ?_), small.2⟩
    exact Nat.pow_le_pow_right (Nat.succ_pos _) hp
  exact ⟨⟨rfl, native.2.1⟩, dispatchJob_guard installed prepared.2.1 tag tagCell native.1 rawGuard
    (fun _ => bound)⟩

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
