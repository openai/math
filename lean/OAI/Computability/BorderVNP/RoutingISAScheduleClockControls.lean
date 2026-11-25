import OAI.Computability.BorderVNP.RoutingISAScheduleClockCube
import OAI.Computability.BorderVNP.RoutingISAScheduleClockRawGroup
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSuffix
import OAI.Computability.BorderVNP.CubeISALocalRowGroupLayout

/-! # The owned and control prefix at one returning processor

The scheduling guard bounds the incidence and declared tails actually seen
by this team. Its native owned rows are charged using the received bits, and
the subsequent padding, cable scatter, bundle and control passes begin at
the same returned memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube Physical TeamRowClock TeamRowSources Finset VPVNP.BurstRAM
open BorderVNP.FiniteEvaluator.OpenSuffix
open private returning_test_cost from OAI.Computability.BorderVNP.RoutingISAScheduleClockLocalRoles

/-- The owned loop consults the owner word only at a valid symbol ordinal. -/
theorem ownerTicks_congr (l : TeamRowPrepare.Layout) (owner other cost : ℕ → ℕ)
    (agree : ∀ u : Fin l.d, owner u.val=other u.val) : TeamRows.ticks l owner cost=TeamRows.ticks l other cost := by
  unfold TeamRows.ticks
  congr 2
  apply sum_congr rfl
  intro j hj
  let q : Fin (l.d*l.d) := ⟨j,mem_range.mp hj⟩
  have eq := agree q.divNat
  change owner (j/l.d)=other (j/l.d) at eq
  rw [eq]

variable {w r X width : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {a : CubeArena.Layout} {orig assigned : ℕ → ℕ} {D : LengthDeclaration a.n a.header.d} {team : Fin (r+1)}
    {A : Type*} [Fintype A] {label : Fin a.cells → Label (a.n+1) a.header.d} {recv : A → Fin a.cells} {incoming : A → ℕ}
    {initial middle final : Memory w} {s u t : Bank w} {es fs : List (TeamRAM.Event w)}

set_option quotPrecheck false

local notation "head" => (pub 0).val
local notation "weights" => LocalRow.weightLayout a head D.1.val
local notation "teams" => LocalRow.teamLayout a r
local notation "owner" => (fun z : Fin a.header.d => assigned (a.ownerBase+z.val))
local notation "host" => HostScatter.Layout.fromFrame head (readings middle)
local notation "pad" => Padding.Layout.fromFrame head (readings middle)

/-- The two real returning fragments fit the local cube window, plus the
public six-word bundle and owned-control arrays. The source premises concern
only this processor's incoming intervals and the public schedule. -/
theorem ownedControls_charge (copies : 1 ≤ a.K) (room : a.ReplayRoom w head)
    (words : a.ScannerWords head team.val D.1.val owner (readings pub) (readings initial) D.2)
    (views : LocalReceived a head team.val D owner initial)
    (schedule : GroupWeights.ScheduleResult weights teams orig assigned)
    (image : GroupWeights.PhysicalImage weights orig a.header.blocks a.b a.K a.h D label recv incoming)
    (positive : 0 < a.h*a.b) (alphabet : 0 < a.header.d)
    (pass : (TeamBudget.Layout.mk (r+1) X a.teamTotals).Passes assigned) (used : ℕ → ℕ)
    (tail : Padding.TailHeader D.1 owner (Function.Embedding.refl ℕ) team.val pad (readings middle) used
      a.header.blocks a.b a.h a.K a.s)
    (site : (host).team=team.val) (cables : (host).ScheduledCables (readings middle) (a.header.blocks*(a.h*a.b)) D.1 owner)
    (H : Inputs) (ready : Ready H head (readings middle) w)
    (groups : Runs pub mac (TeamRows.ownedGroups a.n a.b a.h a.K a.s) s initial es u middle)
    (control : Runs pub mac code u middle fs t final) :
    traceCost es+traceCost fs ≤
      82*(host).count+cubeCoefficient a.n a.b a.h a.K a.s width*(a.alphabet^2+X+1)+
        (Packing.BundleDirectory.setup.slots+16*H.bundles.cells+30*H.bundles.bundles+1)+
        (CellControlRows.setup.slots+H.control.cells*(CellControlRows.body.slots+1)+1+CellControlRows.finish.slots) ∧
      readings final=H.image head (readings middle) := by
  let l := a.scanner head team.val D.1.val a.rowSelectorBits
  let role := TeamRows.physicalCostAt l a.header.blocks a.b a.h a.K a.s D.1
  have owned := rawOwnedGroups_of_words a head team.val D copies owner room words views groups
  change traceCost es ≤ 4+(TeamRows.ticks l (TeamRows.wordOwner owner) role+11) at owned
  have same := ownerTicks_congr l (TeamRows.wordOwner owner) (fun j => assigned (a.ownerBase+j)) role
    (fun j => by have hj : j.val < a.header.d := j.isLt; simp only [TeamRows.wordOwner,dite_eq_left hj])
  rw [same] at owned
  have native := BorderVNP.FiniteEvaluator.OpenSuffix.run H (pub:=pub) (mac:=mac) (s:=u) ready
  have cap := returning_test_cost native (by decide) control
  have body := cubeTicks_le schedule image team l rfl rfl X a.s width positive alphabet pass pad (readings middle) used tail
    host (readings middle) site cables
  dsimp only at body
  rw [HostScatter.program_ticks] at body
  change 4+(TeamRows.ticks l (fun j => assigned (a.ownerBase+j)) role+11)+(pad).budget (readings middle)+
    (68+82*(host).count+22*(host).incident (readings middle))+_+_ ≤
    82*(host).count+cubeCoefficient a.n a.b a.h a.K a.s width*(a.alphabet^2+X+1) at body
  dsimp only [Inputs.cost] at cap
  exact ⟨by omega,(native.sound control).2⟩

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
