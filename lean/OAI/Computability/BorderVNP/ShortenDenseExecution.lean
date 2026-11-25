import OAI.Computability.BorderVNP.ShortenSourceSelectedPath
import OAI.Computability.BorderVNP.ShortenSiteExecution
import OAI.Computability.BorderVNP.ShortenDenseSiteCalibration
import OAI.Computability.BorderVNP.ShortenDenseSiteInputs
import OAI.Computability.BorderVNP.ShortenEpochTerminalChoice
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseSiteRecords

/-!
# Public choices and stored histories of a site-to-site epoch

The prepared path retains each real bin system and its compiled selector.
An execution records the supplied input row order, the actual selected
motion, the stable output numbering, and the final site motion. Thus the
ports, charges, site routes and record counts all refer to one concrete
adaptive history, including its dense storage layout.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Epoch.Round Cover Cover.Frame Shortening Packing Catalog Adaptive
open scoped Classical Topology BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Fixed constants and finite public tables before any absolute level or input pack is chosen. -/
structure SiteSchedule where
  /-- Site move budget at both epoch boundaries. -/
  budget : ℝ
  budget_pos : 0 < budget
  /-- All of the fixed routing generators fit the public move budget. -/
  generators : ∀ s : Cube D → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) →
    s ∈ allowedMoves (Cube D) budget
  /-- Common short scale of geodesic subdivision. -/
  radius : ℝ
  radius_pos : 0 < radius
  radius_small : radius ≤ 1/8
  /-- Radius used to prove the crossing saving. -/
  saving : ℝ
  /-- Relative endpoint tolerance used to prove the crossing saving. -/
  tolerance : ℝ
  /-- Number of physical combining rounds in the epoch. -/
  rounds : ℕ
  rounds_pos : 0 < rounds
  /-- Number of input packs at each combining node. -/
  fanIn : ℕ
  fanIn_two : 2 ≤ fanIn
  /-- Each finite bin system with the actual native selector and its calibrated deviation. -/
  source : SourcePath rounds e radius saving tolerance
  initial_catalog : source.catalog 0 = SiteRoutes.startingSites (Cube D) budget radius
  /-- Fixed word length reserved for the last site motion. -/
  last : ℕ
  /-- Number of candidate one-factor final motions. -/
  motions : ℕ
  /-- The final one-factor motion table. -/
  matrix : Fin motions → SL
  clears : ∀ i, Clears (matrix i) last
  hasMotion : Nonempty (Cube D → Fin motions)
  /-- Final local record multiplier. -/
  finalCap : ℕ
  /-- Coefficient converting geodesic length to final site width. -/
  finalWidth : ℝ
  /-- Coefficient converting geodesic midpoint concentration to site incidence. -/
  finalConcentration : ℝ
  /-- Minimal output offset for all preparations. -/
  floor : ℕ
  /-- Site incidence weight. -/
  weight : ℝ
  weight_pos : 0 < weight
  /-- Additive coefficient per tile in the input cover. -/
  error : ℝ
  error_pos : 0 < error

namespace SiteSchedule

variable {e} (S : SiteSchedule e)

/-- Positive number of packs at each combining node. -/
theorem positiveFanIn : 0 < S.fanIn := Nat.lt_of_lt_of_le (by decide) S.fanIn_two

/-- Complete congruence level drop, including the final motion. -/
def drop := Levels.totalDrop (fun i => (S.source.pattern i).word) S.last

/-- Starting level when the final stored site routes use offset d+1. -/
def high (d : ℕ) := d+1+S.drop

/-- Scheduled level of stage j in this actual epoch. -/
noncomputable def level (d j : ℕ) := S.source.asPath.depth S.last (S.high d) j

/-- The last site rounding operates at the exact required congruence level. -/
theorem finish_level (d : ℕ) : S.level d S.rounds+1 = d+2+2*S.last := by
  let w := fun i => (S.source.pattern i).word
  change Levels.level w (S.high d-S.drop) S.last S.rounds+1 = _
  rw [Levels.finish]
  unfold high; omega

/-- Publicly tracked admissible states on the chosen sequence of levels. -/
abbrev State (d : ℕ) (P : Type) (bits : P → ℕ) (j : ℕ) :=
  S.source.asPath.State P bits S.fanIn S.last (S.high d) j

/-- The input row request at each actual child tuple. -/
abbrev InputRows (d : ℕ) (P : Type) (bits : P → ℕ) :=
  ∀ (i : Fin S.rounds) (c : Fin S.fanIn → S.State d P bits i.val), CableSlots (raw fun j => (c j).val)

/-- The requested public storage rows at each particular attained profile. -/
abbrev OutputRows (d : ℕ) (P : Type) (bits : P → ℕ) :=
  ∀ (i : Fin S.rounds) (c : Fin S.fanIn → S.State d P bits i.val)
    (s : Stage m (S.source.pattern i).bins.Bin (S.level d (i.val+1)) (fun j => (c j).val))
    (q : s.Index e), CableSlots (s.result e q).pack

/-- The actual decoded integral labels and the selected compiled whole-pack samples. -/
abbrev Selections (d : ℕ) (P : Type) (bits : P → ℕ) :=
  ∀ (i : Fin S.rounds) (c : Fin S.fanIn → S.State d P bits i.val),
    (S.source.pattern i).SelectionAt (S.source.stepDepth S.last (S.high d) i) (fun j => (c j).val) S.positiveFanIn

/-- Apply one particular product motion to each site of a terminal pack. -/
noncomputable def terminalMove {d : ℕ} {P : Type} {bits : P → ℕ}
    (p : PlacedPack D P bits K (Cube D) (S.level d S.rounds)) (σ : Cube D → Fin S.motions) (v : p.pack.layout.Site) :=
  productMotion (d+2) (Equiv.refl _) (fun i => S.clears (σ i)) (levelCast (S.finish_level d) (p.site v))

/-- The final publicly scored choice has no larger rounded width than any candidate. -/
def Minimizes {d : ℕ} {P : Type} {bits : P → ℕ}
    (p : PlacedPack D P bits K (Cube D) (S.level d S.rounds)) (σ : Cube D → Fin S.motions) : Prop :=
  ∀ τ, terminalScore p.pack (S.terminalMove p σ) p.active ≤ terminalScore p.pack (S.terminalMove p τ) p.active

end SiteSchedule

variable {e} (S : SiteSchedule e) {d : ℕ} {P : Type} {bits : P → ℕ}

/-- The installed normalized program on prescribed physical input rows, storage
rows and compiled sample selections. All measurements use this one program. -/
structure SiteMachine (d : ℕ) (P : Type) (bits : P → ℕ) where
  /-- Sparse input rows actually used by the sorted allocator. -/
  before : S.InputRows d P bits
  /-- Sparse rows used when each output is stored. -/
  after : S.OutputRows d P bits
  /-- Labels and samples actually requested by the public computation. -/
  select : S.Selections d P bits
  /-- Actual adaptive program on those specific inputs and output profiles. -/
  F : S.source.asPath.ProgramAt P bits S.fanIn S.last (S.high d)
  names : ∀ i c, (F.stage i c).rowCount = (before i c).rows ∧
    ∀ x, ((F.stage i c).slot x).val = ((before i c).number x).val
  measured : ∀ i c, Nonempty (Stage.Measurements (F.stage i c) S.positiveFanIn S.saving S.tolerance
    (S.source.pattern i).mean (S.source.pattern i).motion)
  receipt : ∀ (i : Fin S.rounds) (c : Fin S.fanIn → S.State d P bits i.val), (S.source.pattern i).ReceiptAt (S.source.stepDepth S.last (S.high d) i)
    (fun j => (c j).val) S.positiveFanIn (select i c) (before i c) (F.stage i c)
  records : ∀ i c, (F.stage i c).RecordFactor e (S.source.pattern i).record
  stored : ∀ i c q, (F.advance i c q).val = ((F.stage i c).result e q).dense ((after i c (F.stage i c) q).number)

namespace SiteMachine

variable {S} (M : SiteMachine S d P bits)

/-- The actual destination directory consumed by record replay. -/
noncomputable def saveNames : M.F.SaveNames where
  capacity := fun i c q => (M.after i c (M.F.stage i c) q).rows
  number := fun i c q => (M.after i c (M.F.stage i c) q).number
  stored := M.stored

end SiteMachine

/-- One full normalized execution, including the particular minimizing terminal
motion, the true origin addresses, and the retained charged slots. -/
structure SiteExecution [Fintype P] (M : SiteMachine S d P bits)
    (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget) where
  /-- Actual subdivided leaf states, in row-major order. -/
  flat : Fin (S.fanIn^S.rounds) → S.State d P bits 0
  /-- Original site pack and equality subdivision at every leaf. -/
  initialSites : ∀ i, InitialSites (flat i).val S.budget S.radius_pos
  originalPack : ∀ i, (initialSites i).pack = input i
  originalRoutes : ∀ i, HEq (initialSites i).routes (route i)
  /-- The public terminal selector in each true histogram. -/
  selected : M.F.Hist flat → Cube D → Fin S.motions
  minimum : ∀ i, S.Minimizes (M.F.terminal flat i) (selected i)
  /-- Actual site routes and bounds on every attained terminal network. -/
  out : ∀ i : M.F.Hist flat, SiteOutput (M.F.terminal flat i) (d+1) S.budget S.finalWidth S.finalConcentration S.finalCap
  origins : ∀ i v, reduceMove (d+1) ((out i).routes.origin v) =
    productAddress (d+1) (S.terminalMove (M.F.terminal flat i) (selected i) v)
  charges : ∀ i c, (out i).routes.active c ↔
    let p := M.F.terminal flat i
    p.active c ∧ productAddress (d+1) (S.terminalMove p (selected i) (p.pack.layout.src c)) ≠
      productAddress (d+1) (S.terminalMove p (selected i) (p.pack.layout.dst c))
  first : ∀ i, (out i).routes.FirstAligned
  bound : ∀ i, (out i).routes.potential S.weight / (S.fanIn:ℝ)^S.rounds ≤
    maximumLeaf S.positiveFanIn id (fun j => (route j).potential S.weight)/2 +
      S.error*Fintype.card (Cube D → Deck (S.high d+1))
  tensor : ∀ x, (parallelPacks input).tensor x =
    ∑ i : M.F.Hist flat, (flattenPack S.rounds (M.F.terminal flat i).pack).tensor x

namespace SiteExecution

variable {S} [Fintype P] {M : SiteMachine S d P bits}
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
    (run : SiteExecution S M input route)

/-- Enumerate the true stored dense histograms at their finite output ordinals. -/
noncomputable def enum := (Fintype.equivFin (M.F.Hist run.flat)).symm

/-- Ordinary flat site packs with the calibrated potential and tensor sum, from these same histograms. -/
noncomputable def expansion : Shortening.SiteExpansion (outputDepth := d+1) S.positiveFanIn input route S.weight S.error where
  terms := Fintype.card (M.F.Hist run.flat)
  pack j := flattenPack S.rounds (M.F.terminal run.flat (run.enum j)).pack
  routes j := (run.out (run.enum j)).routes.flatten
  tensor x := (run.tensor x).trans
    (run.enum.sum_comp (fun i => (flattenPack S.rounds (M.F.terminal run.flat i).pack).tensor x)).symm
  bound j := run.bound (run.enum j)

end SiteExecution
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
