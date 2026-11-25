import OAI.Computability.BorderVNP.PackedTerminalSchedule
import OAI.Computability.BorderVNP.PackedHistoryNormalizedEnriched

/-!
# Compiled terminal rounding on the complete stored state

The input directory may be part of an enriched state whose history includes
data beyond its placed tensor network. The motion computed on each such
histogram supplies both the calibrated physical output and the exact
flattened route rows used by the next epoch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SiteSchedule

open Shortening Shortening.Adaptive Shortening.Catalog Epoch Epoch.Round Cover Crossing Terminal Shortening.PublicSegments
open VPVNP.VerifierNetwork (Frame)
open scoped Classical
attribute [local instance] portFintype

universe u v

variable {D m q : ℕ} [NeZero D] {K : Type v} [Field K] {e : PaidIdentity K D m}
    {S : SiteSchedule e} {enum : Fin q ≃ Cube D} {d V E w : ℕ} {Data : Type} [Fintype Data]
    {field : FieldBit (↥(S.source.catalog S.rounds)) (Cube D) (S.level d S.rounds+1) → Data}
    {f : Frame (Terminal.Input Data V E w)
      (Selected D S.motions ↥(allowedMoves (Cube D) S.budget) q (d+2) V E w)}
    {P : Type} [Fintype P] {bits : P → ℕ} {states : ℕ → Type u}
    {view : S.GeometricView d P bits states} {F : S.EnrichedProgram d view}

/-- The public frame on the actual enriched terminal data chooses the common
motion for each complete histogram. The same enriched physical output meets
the calibrated potential and exact tensor bounds, and realizes every public
route row after flattening the exterior ports. -/
theorem RunsEnriched.withReturnedRows (runs : S.RunsEnriched.{u,v} d)
    (cert : S.TerminalFrame enum d V E w field f)
    (placed : ∀ z, PlacedAt (S.source.catalog S.rounds) S.radius (view S.rounds z))
    (measure : ∀ i c, Nonempty (Stage.Measurements (F.stage i c) S.positiveFanIn S.saving S.tolerance
      (S.source.pattern i).mean (S.source.pattern i).motion)) (save : F.SaveNames)
    (flat : Fin (S.fanIn^S.rounds) → states 0)
    (initial : ∀ i, InitialSites (view 0 (flat i)) S.budget S.radius_pos)
    (dir : ∀ i : F.Hist flat, Directory (F.terminal flat i) V E)
    (x : F.Hist flat → Terminal.Input Data V E w → Bool)
    (reads : ∀ i, (dir i).Reads (S.source.catalog S.rounds) field (x i)) :
    ∃ (σ : F.Hist flat → Cube D → Fin S.motions) (out : EnrichedOutput F flat initial σ),
      (∀ i, S.Minimizes (F.terminal flat i) (σ i)) ∧ ∀ i,
      (∀ τ, f.eval (x i) (.inl τ) = decide (τ=σ i)) ∧
      RouteRows.Ready enum (flattenPack S.rounds (F.terminal flat i).pack) (out.out i).routes.flatten
        (boundaryRows (dir i)).flatten (dir i).dummy (f.eval (x i) ∘ Sum.inr) := by
  choose σ hm flags row using fun i => cert (dir i) (x i) (reads i)
  obtain ⟨out⟩ := runs view F placed measure save flat initial σ hm
  refine ⟨σ,out,hm,fun i => ⟨flags i,?_⟩⟩
  exact ((row i).ready (out.out i).routes (out.origins i) (out.charges i) (out.first i)).flatten

/-- The public rows of a prescribed enriched execution at the ordinary
expansion ordinal, with all exterior attachments in row-major order. -/
theorem TerminalFrame.enrichedReturnedRows (cert : S.TerminalFrame enum d V E w field f)
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget} (run : EnrichedExecution F input route)
    (j : Fin run.expansion.terms) (dir : Directory (F.terminal run.flat (run.enum j)) V E)
    (x : Terminal.Input Data V E w → Bool) (reads : dir.Reads (S.source.catalog S.rounds) field x)
    (selected : f.eval x (.inl (run.selected (run.enum j))) = true) :
    RouteRows.Ready enum (run.expansion.pack j) (run.expansion.routes j)
      (boundaryRows dir).flatten dir.dummy (f.eval x ∘ Sum.inr) := by
  obtain ⟨σ,_,flags,row⟩ := cert dir x reads
  have heq : run.selected (run.enum j) = σ := of_decide_eq_true ((flags _).symm.trans selected)
  subst σ
  exact (row.ready (run.output.out (run.enum j)).routes (run.output.origins (run.enum j))
    (run.output.charges (run.enum j)) (run.output.first (run.enum j))).flatten

end PackedHistoryCircuit.Normalized.SiteSchedule

end BorderVNP
end Computability
end OAI
