import OAI.Computability.BorderVNP.ShortenEnrichedSiteEpoch

/-!
# Site shortening on the actual public rows and chosen terminal motions

One schedule fixes the finite stage bins, compiled frame selectors, terminal
motion catalog, congruence drop, fan-in, potential weight and error term.
For every permitted absolute level, every specified row order and valid
compiled selection produces its own normalized program. Every minimizing
final motion yields a site execution of that same program with the exact
formal tensor and the bounds of (6.1).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Epoch.Round Cover Cover.Frame Shortening Packing Catalog Adaptive Filter
open scoped Classical Topology BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}

namespace SiteSchedule

variable (S : SiteSchedule e) (d : ℕ) (P : Type) (bits : P → ℕ)

/-- The prepared public program installs precisely the requested source labels,
whole-pack samples, incoming slot order and saved outgoing slots. -/
def HasPrograms : Prop :=
  Nonempty (S.Selections d P bits) ∧
    ∀ (before : S.InputRows d P bits) (after : S.OutputRows d P bits) (sel : S.Selections d P bits),
      ∃ M : SiteMachine S d P bits, M.before = before ∧ M.after = after ∧ M.select = sel

variable {d P bits} [Fintype P]

/-- Each input tuple has its genuine subdivided leaves, and the site output may
use any specified true minimizing final motion on each attained histogram. -/
def RunsInputs (M : SiteMachine S d P bits) : Prop :=
  ∀ (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget),
    ∃ flat : Fin (S.fanIn^S.rounds) → S.State d P bits 0,
      ∀ (σ : M.F.Hist flat → Cube D → Fin S.motions),
        (∀ i, S.Minimizes (M.F.terminal flat i) (σ i)) →
        ∃ run : SiteExecution S M input route, run.flat = flat ∧ HEq run.selected σ

omit [Fintype P] in
/-- The finite terminal score always has a minimizing product motion. -/
theorem exists_minimum (p : PlacedPack D P bits K (Cube D) (S.level d S.rounds)) :
    ∃ σ, S.Minimizes p σ := by
  have := S.hasMotion
  let f := fun σ => terminalScore p.pack (S.terminalMove p σ) p.active
  obtain ⟨σ,_,hs⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  exact ⟨σ,fun τ => hs τ (Finset.mem_univ τ)⟩

/-- The specified public choices admit a complete physical execution for any
tuple of input packs, without postulating a successful terminal selector. -/
theorem RunsInputs.exists_run {M : SiteMachine S d P bits} (runs : S.RunsInputs M)
    (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget) :
    Nonempty (SiteExecution S M input route) := by
  obtain ⟨flat,exec⟩ := runs input route
  choose σ hσ using fun i : M.F.Hist flat => S.exists_minimum (M.F.terminal flat i)
  obtain ⟨run,_,_⟩ := exec σ hσ
  exact ⟨run⟩

end SiteSchedule

set_option maxHeartbeats 1300000 in
/-- Fully quantified public site epoch with a single finite schedule before
the absolute level, every network and every field entry. Its programs retain
the source selectors and use the dense slot order supplied by the caller. -/
theorem exists_site_executions (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ S : SiteSchedule e, ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ),
      S.HasPrograms d P bits ∧ ∀ M : SiteMachine S d P bits, S.RunsInputs M := by
  obtain ⟨S,hs⟩ := exists_enriched_executions e hm
  refine ⟨S,?_⟩
  intro d hd P fp bits
  obtain ⟨fits,leaves,enriched⟩ := hs d hd
  let source := S.source
  let high := S.high d
  have hk := S.positiveFanIn
  constructor
  · refine ⟨⟨fun i c => ?_⟩,?_⟩
    · exact ((source.pattern i).exists_selectionAt (source.stepDepth S.last high i) (fits.2 i) hk
        (fun j => (c j).val) (fun j => (c j).property)).some
    · intro before after sel
      obtain ⟨F,names,measure,receipt,stored⟩ := source.program_selected S.last high before after hk fits.2 sel
      exact ⟨⟨before,after,sel,F,names,measure,fun i c => (receipt i c).1,fun i c => (receipt i c).2,stored⟩,
        rfl,rfl,rfl⟩
  · intro M input route
    obtain ⟨flat,initial,orig,oldCost,oldRoutes⟩ := leaves input route
    refine ⟨flat,?_⟩
    intro σ hmin
    let view := fun j (p : S.State d P bits j) => p.val
    obtain ⟨out⟩ := enriched view M.F (fun p => p.property) M.measured M.saveNames flat initial σ hmin
    refine ⟨⟨flat,initial,orig,oldRoutes,σ,hmin,out.out,out.origins,out.charges,out.first,?_,?_⟩,rfl,HEq.rfl⟩
    · intro i
      rw [← funext oldCost]
      exact out.bound i
    · intro x
      rw [← funext orig]
      exact out.tensor x

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
