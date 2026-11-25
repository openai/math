import OAI.Computability.BorderVNP.PackedHistoryNormalizedEpoch
import OAI.Computability.BorderVNP.ShortenEnrichedSiteExecution

/-! # The physical site epoch on the complete assigned state

The circuit and the geometry use one enriched program on the very same
subdivided leaves. Its terminal index identifies the full saved state and
the final physical site motion on that state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SiteSchedule

open Crossing Epoch Epoch.Round Cover Shortening Packing Catalog Adaptive VPVNP.VerifierNetwork
open scoped Classical
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {A : ℕ → Type*} {view : S.GeometricView d P bits A} (F : S.EnrichedProgram d view)
    (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget)

/-- A site-to-site execution of the actual named program, from the installed
subdivisions through the chosen physical motion of each terminal histogram. -/
structure EnrichedExecution where
  /-- Complete public state on each installed subdivision. -/
  flat : Fin (S.fanIn^S.rounds) → A 0
  /-- Genuine geometric subdivision of its given site network. -/
  initialSites : ∀ i, InitialSites (view 0 (flat i)) S.budget S.radius_pos
  originalPack : ∀ i, (initialSites i).pack = input i
  originalRoutes : ∀ i, HEq (initialSites i).routes (route i)
  originalPotential : ∀ i, (initialSites i).routes.potential S.weight = (route i).potential S.weight
  /-- Actual terminal motion chosen on each stored pin vector. -/
  selected : F.Hist flat → Cube D → Fin S.motions
  minimum : ∀ q, S.Minimizes (F.terminal flat q) (selected q)
  /-- Physical return value of this same execution. -/
  output : EnrichedOutput F flat initialSites selected

namespace EnrichedExecution

variable {F input route} (run : EnrichedExecution F input route)

/-- Public number of an actual enriched terminal histogram. -/
noncomputable def enum := (Fintype.equivFin (F.Hist run.flat)).symm

/-- The returned site expansion on the supplied valued inputs. Its term
numbering enumerates the full enriched history, including all multiplicities. -/
noncomputable def expansion : SiteExpansion (outputDepth := d+1) S.positiveFanIn input route S.weight S.error where
  terms := Fintype.card (F.Hist run.flat)
  pack q := flattenPack S.rounds (F.terminal run.flat (run.enum q)).pack
  routes q := (run.output.out (run.enum q)).routes.flatten
  tensor x := by
    have h := run.output.tensor x
    rw [funext run.originalPack] at h
    exact h.trans (run.enum.sum_comp (fun i => (flattenPack S.rounds (F.terminal run.flat i).pack).tensor x)).symm
  bound q := by
    have h := run.output.bound (run.enum q)
    rwa [funext run.originalPotential] at h

/-- The exact branch count fields, with no conversion through another machine's
choice type. -/
noncomputable def word {w : ℕ → ℕ} (room : F.Fits w) (q : F.Hist run.flat) :=
  flatWord (F.codec room) run.flat q

/-- An accepted branch specifies one actual enriched histogram. -/
theorem word_injective {w : ℕ → ℕ} (room : F.Fits w) : Function.Injective (run.word room) :=
  flatWord_injective (F.codec room) run.flat

variable {w : ℕ → ℕ} (room : F.Fits w) {W : ℕ → Type} [∀ i, Fintype (W i)]
    (rep : Represents A W) (step : Steps S.fanIn S.rounds W
      (Physical.Pin (Cube D) (fun i => (S.source.pattern i).bins.Bin) (S.level d) e.count w))
    (ok : LocalCorrect (F.codec room) rep step) {X V : Type} [Fintype X] [Fintype V]
    (pre : Frame X (Fin (S.fanIn^S.rounds) × W 0)) (post : Frame (X ⊕ W S.rounds) V)
    (x : X → Bool) (start : ∀ i, rep 0 (fun j => pre.eval x (i,j)) (run.flat i))

/-- The exact enriched root, including its assigned words, before final site routing. -/
noncomputable abbrev root (q : F.Hist run.flat) := (flatChoice F.system run.flat).term q

include ok start in
/-- The validity output tests exactly the physical histograms of this execution.
On their true words the inner circuit represents the entire stored state. -/
theorem checked (g : Slot S.fanIn
    (Physical.Pin (Cube D) (fun i => (S.source.pattern i).bins.Bin) (S.level d) e.count w) S.rounds → Bool) :
    ((wrappedEpoch pre step post).eval (Sum.elim x g) (.inr ()) = true ↔ ∃ q, g = run.word room q) ∧
      ∀ q, g = run.word room q →
        rep S.rounds (fun j => (flatEpoch step).eval (Sum.elim (pre.eval x) g) (.inl j)) (run.root q) := by
  rw [wrappedEpoch_flag]
  exact flatEpoch_correct (F.codec room) rep step ok run.flat (fun i j => pre.eval x (i,j)) start g

include ok start in
/-- The actual post-frame receives this very root's stored pin assignment.
Its output therefore describes the corresponding flattened pack and site routes. -/
theorem correct
    (result : (V → Bool) → (p : Pack D (Fin (S.fanIn^S.rounds) × P) (fun z => bits z.2) K) →
      SiteRoutes p (Cube D) (d+1) S.budget → Prop)
    (finish : ∀ q z, rep S.rounds z (run.root q) →
      result (post.eval (Sum.elim x z)) (flattenPack S.rounds (F.terminal run.flat q).pack) (run.output.out q).routes.flatten)
    (g : Slot S.fanIn
      (Physical.Pin (Cube D) (fun i => (S.source.pattern i).bins.Bin) (S.level d) e.count w) S.rounds → Bool) :
    let f := wrappedEpoch pre step post
    (f.eval (Sum.elim x g) (.inr ()) = true ↔ ∃ q, g = run.word room q) ∧
    ∀ q, g = run.word room q → result (fun j => f.eval (Sum.elim x g) (.inl j))
      (flattenPack S.rounds (F.terminal run.flat q).pack) (run.output.out q).routes.flatten := by
  intro f
  obtain ⟨guard,stored⟩ := run.checked room rep step ok pre post x start g
  refine ⟨guard,fun q hq => ?_⟩
  rw [show (fun j => f.eval (Sum.elim x g) (.inl j)) = _ from wrappedEpoch_state pre step post x g]
  exact finish q _ (stored q hq)

end EnrichedExecution
end PackedHistoryCircuit.Normalized.SiteSchedule

end BorderVNP
end Computability
end OAI
