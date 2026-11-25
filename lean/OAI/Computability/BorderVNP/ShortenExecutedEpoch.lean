import OAI.Computability.BorderVNP.ShortenSiteExecution

/-!
# Uniform parameters and actual histories of the site-to-site epoch

One prepared schedule includes the number of rounds, the fan-in, all
relative site catalogs, the word cutoffs and the local record factors.
After fixing a deep level and an external port list, one selected program
serves all inputs. The numeric and tensor conclusions also hold for any
other program on that same schedule carrying the specified measurements,
record bounds and literal storage equalities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Cover Epoch Epoch.Round Adaptive Packing Catalog Filter
open scoped Classical Topology BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The finite geometric and quantitative constants of one whole epoch. -/
structure SiteSchedule where
  /-- Public site move budget. -/
  budget : ℝ
  positiveBudget : 0 < budget
  /-- This budget includes the fixed routing generators in each factor. -/
  generators : ∀ s : Cube D → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) →
    s ∈ allowedMoves (Cube D) budget
  /-- Geodesic subdivision scale used throughout the epoch. -/
  radius : ℝ
  positiveRadius : 0 < radius
  smallRadius : radius ≤ 1/8
  /-- The chosen scale and tolerance in the crossing saving. -/
  savingScale : ℝ
  /-- Relative endpoint tolerance in the prepared charts. -/
  tolerance : ℝ
  /-- Number of K-way rounds and the common fan-in. -/
  rounds : ℕ
  positiveRounds : 0 < rounds
  /-- Number of child packs combined at each internal node. -/
  fanIn : ℕ
  atLeastTwo : 2 ≤ fanIn
  /-- The actual prepared relative catalog and motion table in each round. -/
  path : StagePath rounds e (Cube D) radius savingScale tolerance
  /-- Uniform per-child descriptor and expanded-load multipliers. -/
  factors : Fin rounds → ℕ
  /-- Word length reserved for final site rounding. -/
  last : ℕ
  /-- Final local record multiplier under that site motion. -/
  finalCap : ℕ
  /-- Multipliers for the final width and incidence concentration. -/
  finalWidth : ℝ
  /-- Factor for the final rounded incidence norm. -/
  finalConcentration : ℝ
  /-- Lower bound on the level at which the epoch may return its output. -/
  floor : ℕ
  /-- Potential weight and additive error per input tile. -/
  weight : ℝ
  positiveWeight : 0 < weight
  /-- Additive coefficient multiplying the number of input tiles. -/
  error : ℝ
  positiveError : 0 < error

namespace SiteSchedule

variable {e} (S : SiteSchedule e)

/-- A positive input count in each combining round. -/
theorem positiveFanIn : 0 < S.fanIn := Nat.lt_of_lt_of_le (by decide) S.atLeastTwo

/-- Total number of congruence levels used by this epoch. -/
def drop : ℕ := Levels.totalDrop (fun i => (S.path.pattern i).word) S.last

/-- The higher input level, given the lower output offset. -/
def inputLevel (d : ℕ) := d+1+S.drop

/-- The program type, fixed before specifying an actual input tuple. -/
abbrev Machine (d : ℕ) (P : Type) (bits : P → ℕ) :=
  SiteMachine S.path S.factors S.last (S.inputLevel d) S.positiveFanIn P bits

/-- The execution for the actual input tuple and this program, with its original and final site moves. -/
abbrev Execution {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (M : S.Machine d P bits)
    (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.inputLevel d) S.budget) :=
  SiteExecution (low := d+1) M S.positiveRadius input route S.weight S.error
    S.finalWidth S.finalConcentration S.finalCap

end SiteSchedule

/-- Uniform existence of the actual site programs and complete executions.
The arbitrary-program clause lets public reconstruction use its particular
admissible chosen motions and record-bearing program on this schedule. -/
theorem exists_site_executions (hm : 0 < m) :
    ∃ S : SiteSchedule e, ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ),
      Nonempty (S.Machine d P bits) ∧ ∀ (M : S.Machine d P bits)
      (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
      (route : ∀ i, SiteRoutes (input i) (Cube D) (S.inputLevel d) S.budget),
        Nonempty (S.Execution M input route) := by
  let I := Cube D
  obtain ⟨L,hL,hgen,ν,hν,H,hH,b,hb,close⟩ := actual_site_epoch (I := I) e hm
  obtain ⟨h,hh,hshort,prepare⟩ := exists_record_path e hm hH hν
  let initial := SiteRoutes.startingSites I L h
  obtain ⟨path,hpath,C,hC⟩ := prepare b initial
  obtain ⟨V,hV,fits⟩ := path.terminal_catalog (by linarith)
  obtain ⟨a,R,A,Cout,calibrate⟩ := close hh V hV
  obtain ⟨weight,hw,E,hE,k0⟩ := calibrate (fun i => (path.pattern i).Bin)
    (fun i => (path.pattern i).meanFactor) (fun i => (path.pattern i).motionFactor)
    (fun i => (path.pattern i).nonneg.1) (fun i => (path.pattern i).nonneg.2)
  obtain ⟨k,⟨hk,round⟩,hk2⟩ := (k0.and (eventually_ge_atTop 2)).exists
  obtain ⟨startFloor,leaves⟩ := path.initial_leaves (L := L) hh
  let word := fun i => (path.pattern i).word
  let drop := Levels.totalDrop word a
  let floor := max startFloor (∑ i, (path.pattern i).floor)
  let S : SiteSchedule e := ⟨L,hL,hgen,h,hh,hshort,H,ν,b,hb,k,hk2,path,C,a,R,A,Cout,floor,weight,hw,E,hE⟩
  refine ⟨S,?_⟩
  intro d hd P inst bits
  let high := d+1+drop
  have hhigh : path.threshold a 1 ≤ high := by
    change drop + (1 + ∑ i, (path.pattern i).floor) ≤ d+1+drop
    have hf : (∑ i, (path.pattern i).floor) ≤ d := (le_max_right ..).trans hd
    omega
  obtain ⟨F,measured,records,stored⟩ :=
    path.program_at_start_records (P := P) (bits := bits) C hC a 1 high hhigh hk
  refine ⟨⟨⟨F,measured,records,stored⟩⟩,?_⟩
  intro M input route
  obtain ⟨hs,_,hfloor⟩ := Levels.of_start word a 1 (fun i => (path.pattern i).floor) hhigh
  obtain ⟨flat,initialSites,orig,oldCost,oldRoutes⟩ := leaves (k := k) (bits := bits) weight a high hs
    (by dsimp [high]; have := (le_max_left startFloor _).trans hd; omega) hpath input route
  have hfinal : path.depths a high b + 1 = d+2+2*a := by
    change Levels.level word (high-drop) a b + 1 = _
    rw [Levels.finish]; dsimp [high]; omega
  let depth := path.depths a high
  let view := fun n (p : path.State P bits k a high n) => p.val
  have vol (i : Fin b) : (Fintype.card (I → Deck (depth (i.val+1)+1)) : ℝ) ≤ Fintype.card (I → Deck (high+1)) := by
    have hn := Levels.tiles_le_start word I (high-drop) a (i.val+1)
    rw [hs] at hn
    exact_mod_cast hn
  obtain ⟨out,pot,expand⟩ := round depth view M.F (Fintype.card (I → Deck (high+1))) (Nat.cast_nonneg _)
    vol M.measured d hfinal flat initialSites (fits a high M.F M.stored flat)
  refine ⟨{
    flat := flat
    initialSites := initialSites
    originalPack := orig
    originalRoutes := oldRoutes
    out := out
    bound := ?_
    tensor := ?_
  }⟩
  · intro i
    have he := pot i
    rw [funext oldCost] at he
    exact he
  · intro x
    have he := expand x
    rw [funext orig] at he
    exact he

end Shortening

end BorderVNP
end Computability
end OAI
