import OAI.Computability.BorderVNP.PackedHistoryFlatPrivateSites
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms
import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedOuter
import OAI.Computability.BorderVNP.DiagonalOriginalRowExecution

/-! # Retained private work on every attained enriched outer history

A full epoch starts from the actual child edge directories, installs its
routed subdivisions, executes the chosen normalized histogram, and flattens
its returned ports. The outer recursion follows the machine's own branch
indices and provides the private site tapes on exactly its terminal state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500

universe u

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

/-- Present the same stored site programs using another enumeration of the same finite ports. -/
noncomputable def changePrivateInstance {D : ℕ} {Q : Type} {widths : Q → ℕ} (N : Network D Q widths)
    {fin fin' : Fintype Q} (old : @Site.Programs D Q fin widths N) : @Site.Programs D Q fin' widths N :=
  fun v => (old v).castWidth (incoming_instances N v)

/-- Transport the entire program family along the stored equality of its layout. -/
def samePrivatePrograms {N M : Network D P bits} (h : N = M) (old : Site.Programs N) : Site.Programs M :=
  h ▸ old

/-- The private birth at the stored original host is unchanged by this layout equality. -/
theorem samePrivatePrograms_birth {N M : Network D P bits} (h : N = M) (old : Site.Programs N) (v : N.Site) :
    (samePrivatePrograms h old ((Retains.ofEq h).site v)).birth = (old v).birth := by
  subst M
  rfl

variable {m start T : ℕ} [NeZero D] {K : Type} [Field K]
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    (c : Fin (fan S) → Admissible good t) (old : ∀ i, Site.Programs (c i).val.pack.layout)

/-- Real initial subdivision of one child, including the true old/new cable and port rows. -/
noncomputable def installedPrivatePrograms (i : Fin (fan S)) : Site.Programs (E.view 0 ((E.run c).flat i)).pack.layout := by
  let run := E.run c
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let prior := samePrivatePrograms orig (old i)
  exact samePrivatePrograms saved (Subdivision.subdividePrivatePrograms a.pack.layout (a.routes.routes S.radius)
    raw.edge new.edge (rows.ports 0) (changePrivateInstance _ prior))

/-- The subdivision of the actual child still exposes the same original birth at its retained endpoint. -/
theorem installedPrivatePrograms_birth (i : Fin (fan S)) (v : (c i).val.pack.layout.Site) :
    (E.installedPrivatePrograms rows c old i
      ((enrichedInstalledHosts (E.run c).flat (E.run c).initialSites (E.run c).originalPack i).site v)).birth =
      (old i v).birth := by
  let run := E.run c
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let prior := samePrivatePrograms orig (old i)
  let atOld := (Retains.ofEq orig).site v
  let installed := Subdivision.subdividePrivatePrograms a.pack.layout (a.routes.routes S.radius)
    raw.edge new.edge (rows.ports 0) (changePrivateInstance _ prior)
  exact (samePrivatePrograms_birth saved installed (.inl atOld)).trans
    ((Subdivision.subdivide_birth a.pack.layout (a.routes.routes S.radius) atOld raw.edge new.edge (rows.ports 0) (changePrivateInstance _ prior)).trans
      (samePrivatePrograms_birth orig (old i) v))

/-- Executable private banks at the actual saved outer state produced by this histogram. -/
noncomputable def privatePrograms (number : e.Entry → ℕ) (q : E.F.Hist (E.run c).flat) :
    Site.Programs ((E.term c q).val.pack.layout) :=
  changePrivateInstance _ (E.F.flatPrivatePrograms E.saveNames rows number (E.run c).flat (E.installedPrivatePrograms rows c old) q)

/-- The child bank's birth is preserved at its actual final host after this entire epoch. -/
theorem privatePrograms_birth (number : e.Entry → ℕ) (q : E.F.Hist (E.run c).flat)
    (i : Fin (fan S)) (v : (c i).val.pack.layout.Site) :
    (E.privatePrograms rows c old number q ((enrichedEpochHosts (E.run c) E.saveNames q).site ⟨i,v⟩)).birth =
      (old i v).birth :=
  (E.F.flatPrivatePrograms_birth E.saveNames rows number (E.run c).flat (E.installedPrivatePrograms rows c old)
    q i _).trans (E.installedPrivatePrograms_birth rows c old i v)

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)

/-- The complete physical program family emitted by one active outer step. -/
noncomputable def stepPrivatePrograms {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, Site.Programs (c j).val.pack.layout) :
    ∀ q : (M.epoch n c).Index, Site.Programs ((M.epoch n c).term q).val.pack.layout := by
  unfold Machine.epoch
  rw [dite_eq_left hn]
  exact (M n hn).privatePrograms (rows n hn) c old number

/-- Every original child birth is retained on the host traced by this true outer step. -/
theorem stepPrivatePrograms_birth {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, Site.Programs (c j).val.pack.layout) (q : (M.epoch n c).Index)
    (i : Fin (fan S)) (v : (c i).val.pack.layout.Site) :
    (M.stepPrivatePrograms rows number hn c old q ((enrichedStepHosts M hn c q).site ⟨i,v⟩)).birth =
      (old i v).birth := by
  let family (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) → Site.Programs (z.term j).val.pack.layout
  let hosts (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) →
    Retains (parallelPacks fun i => (c i).val.pack).layout (z.term j).val.pack.layout
  have carry {z y : ProfileSum (Admissible good (n+1))} (he : z = y) (f : family y) (g : hosts y)
      (h : ∀ j : y.Index, (f j ((g j).site ⟨i,v⟩)).birth = (old i v).birth) :
      ∀ j : z.Index, ((Eq.mpr (congrArg family he) f) j (((Eq.mpr (congrArg hosts he) g) j).site ⟨i,v⟩)).birth =
        (old i v).birth := by
    subst y
    exact h
  have he : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  exact carry he ((M n hn).privatePrograms (rows n hn) c old number)
    (enrichedEpochHosts ((M n hn).run c) (M n hn).saveNames)
    (fun j => (M n hn).privatePrograms_birth (rows n hn) c old number j i v) q

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- Full recursive private bank of the actual attained outer history. -/
noncomputable def historyPrivatePrograms :
    (n : ℕ) → n ≤ T → (q : (packHistory bottom M.epoch n).Index) →
    Site.Programs ((packHistory bottom M.epoch n).term q).val.pack.layout
  | 0, _, _ => base
  | n+1, hn, q =>
    M.stepPrivatePrograms rows number (Nat.lt_of_succ_le hn)
      (fun j => (packHistory bottom M.epoch n).term (q.1 j))
      (fun j => historyPrivatePrograms n (Nat.le_of_succ_le hn) (q.1 j)) q.2

/-- At the actual host of every nested original site the complete outer history
preserves the intrinsic birth program of that site's original bottom copy. -/
theorem historyPrivatePrograms_birth (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index)
    (v : (parallelLeaves (fun _ : Unit => bottom.val.pack) n (leavesEquiv (fan S) Unit n fun _ => ())).layout.Site) :
    (M.historyPrivatePrograms rows number bottom base n hn q ((enrichedNestedHosts M bottom n hn q).site v)).birth =
      (base (originalNames (fun _ : Unit => bottom.val.pack) n (fun _ => ()) v).2).birth := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let hl := Nat.lt_of_succ_le hn
    let H := packHistory bottom M.epoch n
    let c := fun j : Fin (fan S) => H.term (q.1 j)
    let old := fun j : Fin (fan S) => M.historyPrivatePrograms rows number bottom base n hl.le (q.1 j)
    let atChild := (enrichedNestedHosts M bottom n hl.le (q.1 v.1)).site v.2
    exact (M.stepPrivatePrograms_birth rows number hl c old q.2 v.1 atChild).trans (ih hl.le (q.1 v.1) v.2)

variable (q : (packHistory bottom M.epoch T).Index)

/-- Executable site programs of the genuine flattened terminal network of the chosen outer history. -/
noncomputable def terminalPrivatePrograms :
    Site.Programs (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout := fun v =>
  (M.historyPrivatePrograms rows number bottom base T le_rfl q v).castWidth
    ((incoming_instances _ _).trans (Flat.incoming_eq T ((packHistory bottom M.epoch T).term q).val.pack v).symm)

/-- The retained bank at the row-major original leaf address has exactly its original
birth tape and observation fiber, through every intervening subdivision and histogram. -/
theorem terminalPrivatePrograms_birth (i : Fin ((fan S)^T)) (v : bottom.val.pack.layout.Site) :
    (M.terminalPrivatePrograms rows number bottom base q ((enrichedOuterHosts M bottom q).site ⟨i,v⟩)).birth =
      (base v).birth := by
  let orig := originalNames (k := fan S) (fun _ : Unit => bottom.val.pack) T (fun _ => ())
  let u := orig.symm ⟨i,v⟩
  have hb := M.historyPrivatePrograms_birth rows number bottom base T le_rfl q u
  exact hb.trans (congrArg (fun x : (parallelPacks fun _ : Fin ((fan S)^T) => bottom.val.pack).layout.Site =>
    (base x.2).birth) (orig.apply_symm_apply ⟨i,v⟩))

end Machine
end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
