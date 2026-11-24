import OAI.Computability.VPVNP.CompressorRefreshBeforeMatch
import OAI.Computability.VPVNP.CompressorRefreshEmitCost
import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.CompressorPassTimeline

/-! # Source packets of a complete refresh occurrence -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshEmit

open BurstRAM BlockPlanner Compression DescriptorSpace PassTimeline Schedule SourceOnline
open ScheduledTrace PairSimulation.TraversalRoles PairSimulation.LocalHistory PortRefresh
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → R) (hf : B.IsSolution f) {g w : ℕ} (base : Word w)
variable (positions blocks t cap n : ℕ) (initial : TaggedLayer) (initialFrame : Fin 8 → Word w)
variable (past : List (SelectedLevel B f hf)) (X : State S.portExponent (S.portExponent + g))

local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "loc" => (Located.mk t (Pass.refresh (steps := S.steps)))
local notation "start" => Located.first loc B
local notation "o" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "he" => Nat.two_pow_pos S.expanderExponent
local notation "Choice" => Refresh.DyadicRefreshChoice X S.graph he hc B.refresh
local notation "P" => SourceOnline.Packet scr w
local notation "logs" => (fun ps : List P => List.flatMap SourceWalk.Packet.reports ps)
local notation "hr" => ScheduledRates.headerRate (BlockProgram.geometry B)
  (Scalars.Pass.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent)
local notation "cr" => Build.chargeFactor S.graph he hc B.refresh
  (LevelRecipe.Shape.ties (RefreshBlockPlan.shape B))
local notation "res" =>
  CompiledResident.resident B f hf base positions blocks n initial initialFrame

/-- All branches begin at the same completed preparation. The only choice
packet is the native motif selector, with the term's own encoded choices. -/
structure Sources (encode : Choice → List Bool) (m : Memory w) (hs ds : List P)
    (term : Choice → P) (tail : Choice → List P) : Prop where
  before : RefreshBefore.Before B f hf base positions blocks t X cap m hs ds
  first : SourceOnline.Group scr L base cap start (directoryRows L) m (hs ++ ds)
  middle : ∀ c, SourceOnline.Group scr L base cap (start + (hs ++ ds).length) (directoryRows L)
    (post m (hs ++ ds)) [term c]
  last : ∀ c, SourceOnline.Group scr L base cap (start + (hs ++ ds).length + 1) (directoryRows L)
    (term c).output (tail c)
  termBits : ∀ c, (term c).stage.choices = List.ofFn (workerTapes o w c)
  emptyTail : ∀ c, ∀ p ∈ tail c, p.stage.choices = List.replicate p.stage.choices.length []
  lengths : ∀ c, start + (hs ++ ds).length + 1 + (tail c).length = (loc).finish B
  stored : ∀ c, res (past ++ [RefreshPlacement.selectedLevel B f hf X c (encode c)])
    (Refresh.dyadicRefreshNext X S.graph he hc B.refresh S.port_order (And.right S.degree_bounds) c)
    (post (term c).output (tail c))
  rawCharge : ∀ c, RAMBuckets.cost Report.probes (logs ((hs ++ ds) ++ term c :: tail c)) ≤
    hr + cr * X.positions + X.positions * (18 * 2 ^ (S.degreeExponent 0) + 4) + 27

end CompressorRecords.RefreshEmit

end

end VPVNP
end Computability
end OAI
