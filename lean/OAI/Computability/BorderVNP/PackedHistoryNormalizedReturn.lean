import OAI.Computability.BorderVNP.PackedHistoryNormalizedTransport
import OAI.Computability.BorderVNP.PackedTerminalEnriched

/-! # The compiled terminal frame on the attained outer successor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Catalog Adaptive PublicCapacity
open Shortening.PublicSegments Shortening.PublicRelative Shortening.PreparedBins
open VPVNP.VerifierNetwork (Frame)
open scoped Classical
attribute [local instance] portFintype

universe u v

section Frame

variable {Move X Y Z : Type} [Fintype Move] [Fintype X] [Fintype Y] [Fintype Z] {q w a b : ℕ} {outer inner : Shape}
    (hlev : a=b) (hshape : outer=inner)
    (f : Frame Y (Z ⊕ RouteRows.Pins Move q (a+1) inner.sites inner.edges w))

/-- Use the attained inner state as the terminal frame's input and return all route columns
at their prescribed outer indices. -/
noncomputable def terminalPost : Frame (X ⊕ Y) (RouteRows.Pins Move q (b+1) outer.sites outer.edges w) :=
  (f.subst (Frame.initial Sum.inr)).select (Sum.inr ∘ returnedPin hlev hshape)

/-- Reindexing the output and retaining the terminal inputs adds no gates. -/
theorem terminalPost_size : (terminalPost (X := X) hlev hshape f).size = f.size := by
  simp [terminalPost]

/-- Every computed outer wire is the corresponding wire of the selected terminal frame. -/
theorem terminalPost_eval (x : X → Bool) (y : Y → Bool) :
    (terminalPost hlev hshape f).eval (Sum.elim x y) = f.eval y ∘ Sum.inr ∘ returnedPin hlev hshape := by
  have stored : (Frame.initial (Sum.inr : Y → X ⊕ Y)).eval (Sum.elim x y) = y := funext fun j => by simp
  funext i
  simp [terminalPost,stored]

end Frame

variable {D m : ℕ} [NeZero D] {K : Type v} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {start T t V E w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {budget : ℕ → ℕ}
    (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T)
    {A : ℕ → Type u} {view : S.GeometricView (offset S start t) (Port (fan S) P t) (width bits (fan S) t) A}
    {F : S.EnrichedProgram (offset S start t) view}
    {Data : Type} [Fintype Data]
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (flat : Fin (fan S) → A 0) (words : A S.rounds → Terminal.Input Data V E w → Bool)

/-- The calibrated terminal pass, including its one-hot motion output. -/
noncomputable abbrev TerminalCircuit (S : SiteSchedule e) (Data : Type) [Fintype Data] (d V E w : ℕ) :=
  Frame (Terminal.Input Data V E w) (Terminal.Selected D S.motions ↥(allowedMoves (Cube D) S.budget)
    (Fintype.card (Cube D)) (d+2) V E w)

/-- The native execution and the exact assigned successor on each of its actual histories. -/
structure Returned
    (post : Frame ((Fin (fan S) × Pins S start shape w t) ⊕ Terminal.Input Data V E w)
      (Pins S start shape w (t+1)))
    (dir : ∀ a, Directory (view S.rounds a) V E) (hshape : shape (t+1) = ⟨V,E⟩) where
  /-- The enriched execution on the supplied child packs with their routes at the starting inner level. -/
  run : SiteSchedule.EnrichedExecution F (fun i => (c i).val.pack) (routes deep ht c)
  leaves : run.flat = flat
  /-- Site and cable row numbers of the flattened terminal pack for each attained histogram. -/
  rows : ∀ q : F.Hist run.flat, Rows (shape (t+1)) (flattenPack S.rounds (F.terminal run.flat q).pack).layout
  /-- Endpoint used for the dummy loop at each vacant cable row of the returned pack. -/
  dummy : ∀ q : F.Hist run.flat, Fin (shape (t+1)).edges → (flattenPack S.rounds (F.terminal run.flat q).pack).layout.Site
  rows_eq : ∀ q : F.Hist run.flat, rows q = returnedRows hshape
    (Terminal.boundaryRows (dir (run.root q))).flatten
  dummy_eq : ∀ q : F.Hist run.flat, dummy q = returnedDummy
    (p := flattenPack S.rounds (F.terminal run.flat q).pack) hshape (dir (run.root q)).dummy
  closed : ∀ q : F.Hist run.flat, Good budget (t+1) (State.mk
    (flattenPack S.rounds (F.terminal run.flat q).pack)
    (reindexRoutes (levels S deep ht).2.1 (run.output.out q).routes.flatten) (rows q) (dummy q)
    (post.eval (Sum.elim (childWords c) (words (run.root q)))))

private theorem returnedRows_site {D : ℕ} {K : Type*} {P : Type} {bits : P → ℕ} {p : Pack D P bits K}
    {inner outer : Shape} (hshape : outer = inner) (row : Rows inner p.layout) (v : p.layout.Site) :
    ((returnedRows (p := p) hshape row).site v).val = (row.site v).val := by
  subst outer
  rfl

section Attachment

variable {deep ht c flat words} {post} {dir} {hshape}

/-- The returned site number of each flat external port is the terminal state's stored
site number for the corresponding nested port. -/
theorem Returned.rows_attach (R : Returned (F := F) deep ht c flat words post dir hshape)
    (q : F.Hist R.run.flat) (z : Fin (fan S) × Port (fan S) P t) :
    ((R.rows q).site ((flattenPack S.rounds (F.terminal R.run.flat q).pack).layout.attach z)).val =
      ((dir (R.run.root q)).sites ((F.terminal R.run.flat q).pack.layout.attach
        ((portEquiv S.fanIn (Port (fan S) P t) S.rounds).symm z))).val := by
  rw [R.rows_eq q]
  exact returnedRows_site (p := flattenPack S.rounds (F.terminal R.run.flat q).pack) hshape
    (Terminal.boundaryRows (dir (R.run.root q))).flatten _

end Attachment

variable {field : FieldBit (↥(S.source.catalog S.rounds)) (Cube D) (S.level (offset S start t) S.rounds+1) → Data}

set_option maxHeartbeats 1500000 in
/-- Execute the calibrated terminal motion on the stored named words. Both the physical row
certificate and the expanded record budget refer to the output of this very histogram. -/
theorem returned_execution (hshape : shape (t+1) = ⟨V,E⟩)
    (f : TerminalCircuit S Data (offset S start t) V E w)
    (runs : S.RunsEnriched.{u,v} (offset S start t))
    (cert : S.TerminalFrame (factorEnum D) (offset S start t) V E w field f)
    (placed : ∀ a, PlacedAt (S.source.catalog S.rounds) S.radius (view S.rounds a))
    (measure : ∀ i a, Nonempty (Stage.Measurements (F.stage i a) S.positiveFanIn S.saving S.tolerance
      (S.source.pattern i).mean (S.source.pattern i).motion))
    (save : F.SaveNames) (records : ∀ i a, (F.stage i a).RecordFactor e (S.source.pattern i).record)
    (dir : ∀ a, Directory (view S.rounds a) V E)
    (reads : ∀ a, (dir a).Reads (S.source.catalog S.rounds) field (words a))
    (initial : ∀ i, InitialSites (view 0 (flat i)) S.budget S.radius_pos)
    (originalPack : ∀ i, (initial i).pack = (c i).val.pack)
    (originalRoutes : ∀ i, HEq (initial i).routes (routes deep ht c i))
    (originalPotential : ∀ i, (initial i).routes.potential S.weight = (routes deep ht c i).potential S.weight)
    (nextCap : S.recordFactor*(1+budget t) ≤ 1+budget (t+1)) :
    ∃ R : Returned (F := F) deep ht c flat words (terminalPost (levels S deep ht).2.1 hshape f) dir hshape,
      ∀ q τ, f.eval (words (R.run.root q)) (.inl τ) = decide (τ = R.run.selected q) := by
  let root := (flatChoice F.system flat).term
  obtain ⟨motion,out,minimum,returned⟩ := runs.withReturnedRows cert placed measure save flat initial
    (fun q => dir (root q)) (fun q => words (root q)) (fun q => reads (root q))
  let run : SiteSchedule.EnrichedExecution F (fun i => (c i).val.pack) (routes deep ht c) :=
    ⟨flat,initial,originalPack,originalRoutes,originalPotential,motion,minimum,out⟩
  let nativeRows (q : F.Hist flat) := (Terminal.boundaryRows (dir (root q))).flatten
  let nativeDummy (q : F.Hist flat) := (dir (root q)).dummy
  refine ⟨⟨run,rfl,fun q => returnedRows hshape (nativeRows q),
    fun q => returnedDummy (p := flattenPack S.rounds (F.terminal flat q).pack) hshape (nativeDummy q),
    fun _ => rfl,fun _ => rfl,?_⟩,fun q => (returned q).1⟩
  intro q
  refine ⟨?_,?_⟩
  · have ready := returnedReady (factorEnum D) (levels S deep ht).2.1 hshape (returned q).2
    rw [terminalPost_eval]
    exact ready
  · obtain ⟨fields,within⟩ := inputFields deep ht c
    let data := run.recordFields fields save q
    refine ⟨data,?_⟩
    have hcap := run.recordCertificate fields save records true (budget t) within q
    let route := (run.output.out q).routes.flatten
    change ∀ tile, @localRecords D _ (portFintype (k := fan S) (P := P) (b := t+1)) _
      (flattenPack S.rounds (F.terminal run.flat q).pack).layout true data.prior data.payload
      (fun v => reduceMove (depth S start (t+1)) ((reindexRoutes (levels S deep ht).2.1 route).origin v) = tile) ≤ budget (t+1)
    rw [show portFintype (k := fan S) (P := P) (b := t+1) = instFintypeProd (Fin (fan S)) (Port (fan S) P t)
      from Subsingleton.elim _ _]
    apply RecordData.transfer_site_cap (levels S deep ht).2.1.symm rfl
      (reindexRoutes_heq (levels S deep ht).2.1 route) data true (budget (t+1))
    intro tile
    have h := (hcap tile).trans nextCap
    exact Nat.le_of_add_le_add_left h

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
