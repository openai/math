import OAI.Computability.BorderVNP.PackedCompleteStageCharges
import OAI.Computability.BorderVNP.PackedHistoryNormalizedEnriched

/-! # All crossing cables in a named program's attained physical histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Packing Adaptive
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ}

namespace SourcePath

variable [Fintype P] {p : SourcePath b e h H ν} {last high : ℕ}
    {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type*}
    {keep : ∀ j, p.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0 < k}
    {nodes : ∀ i : Fin b, p.Node last high V E w k i}
    (r : p.NamedRun last high V E w cap keep hk nodes)

local notation "A" => NamedState.Admissible (p.NamedGood last high V E w cap keep)

/-- On every selected inner histogram, the original site's complete charge mask survives
the prescribed per-child motions, interval replacement, and all dense directory saves. -/
theorem NamedRun.terminal_coversCrossings (flat : Fin (k^b) → A 0)
    (base : ∀ i, (flat i).val.placed.CoversCrossings) (q : r.program.Hist flat) :
    (r.program.terminal flat q).CoversCrossings := by
  let F := r.program
  let ok := fun z : A 0 => z.val.placed.CoversCrossings
  have cover (j : ℕ) (z : (F.system.layer j).Name) (hz : F.system.fromInputs ok j z) :
      ((F.system.layer j).state z).val.placed.CoversCrossings := by
    induction j with
    | zero => exact hz
    | succ j ih =>
      let i : Fin b := ⟨j,z.2.1.down⟩
      let c := fun a => (F.system.layer j).state (z.1 a)
      change (F.advance i c z.2.2).val.placed.CoversCrossings
      rw [r.stored i c z.2.2]
      exact ((p.pattern i).receiptAt_coversCrossings (r.installed i c).receipt
        (fun a => ih (z.1 a) (hz a)) z.2.2).dense _
  exact cover b _ (F.system.fromInputs_histories ok b le_rfl _ (allLeaves_of_flat ok b flat base) q)

end SourcePath

namespace SiteSchedule

variable [Fintype P] {S : SiteSchedule e} {d : ℕ} {A : ℕ → Type*} {view : S.GeometricView d P bits A}
    {F : S.EnrichedProgram d view} {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
    (run : EnrichedExecution F input route)

/-- On a complete physical terminal, the public rounding mask is exactly the test
that its endpoints land in different cells after the selected motion. -/
theorem EnrichedExecution.active_iff_crossing (q : F.Hist run.flat)
    (complete : (F.terminal run.flat q).CoversCrossings) (c : (F.terminal run.flat q).pack.layout.Edge) :
    let p := F.terminal run.flat q
    let s := (run.output.out q).routes
    s.active c ↔ reduceMove (d+1) (s.origin (p.pack.layout.src c)) ≠
      reduceMove (d+1) (s.origin (p.pack.layout.dst c)) := by
  let p := F.terminal run.flat q
  dsimp only
  rw [run.output.charges q c,run.output.origins,run.output.origins]
  refine ⟨And.right,fun hc => ⟨?_,hc⟩⟩
  have hs : p.site (p.pack.layout.src c) ≠ p.site (p.pack.layout.dst c) := by
    intro h
    exact hc (congrArg (fun x => productAddress (d+1)
      (productMotion (d+2) (Equiv.refl _) (fun i => S.clears (run.selected q i))
        (levelCast (S.finish_level d) x))) h)
  exact (p.active_iff c).mpr ⟨complete c hs,hs⟩

end SiteSchedule
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
