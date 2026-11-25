import OAI.Computability.BorderVNP.PackedRetainedWork
import OAI.Computability.BorderVNP.PackedBankInheritedDenseReplay
import OAI.Computability.BorderVNP.DiagonalExternalSewNormalized
import OAI.Computability.BorderVNP.DiagonalOriginalRowTree

/-! # Private site tapes on the selected normalized history

Parallel composition and cable sorting keep each site's private work in place.
Sewing appends the sorted physical intervals at each old site and installs the
origin, terminal and paid programs at the newly created sites. Following the
actual child indices therefore keeps a complete observation fiber from each
site's birth to its saved terminal tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

/-- A current site program, its intrinsic program at birth and its installed interval history. -/
structure Site.Lineage (inc : ℕ) where
  /-- Intrinsic bottom, origin, terminal or paid program. -/
  birth : Site
  /-- Current executable private program. -/
  program : Site
  /-- True successive interval installs from birth to this state. -/
  retention : birth.Retention program
  /-- All physical incidence words have their actual current extent. -/
  size : program.incoming = inc

/-- Start at the site's intrinsic program with its independent private choices. -/
def Site.Lineage.start (s : Site) {inc : ℕ} (h : s.incoming = inc) : Site.Lineage inc := ⟨s,s,.refl s,h⟩

/-- Reindex the incidence width while leaving the full private program and its history in place. -/
def Site.Lineage.castWidth {m n : ℕ} (s : Site.Lineage m) (h : m = n) : Site.Lineage n :=
  ⟨s.birth,s.program,s.retention,s.size.trans h⟩

open Crossing

/-- Actual installed private programs at every host of a network. -/
noncomputable abbrev Site.Programs {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits) :=
  (v : N.Site) → Site.Lineage (Inherited.incoming N v)

/-- Reindex the synthesized finite-port instance at a recursive boundary. -/
theorem incoming_instances {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits) (v : N.Site)
    {f g : Fintype P} : @Inherited.incoming D P f bits N v = @Inherited.incoming D P g bits N v :=
  congrArg (fun i => @Inherited.incoming D P i bits N v) (Subsingleton.elim f g)

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Shortening.CombiningStep
open Diagonal.ExternalSew Diagonal.CellEntries Epoch.Round
open scoped Classical

attribute [local instance] portFintype
set_option maxHeartbeats 1600000

variable {D m k d d' : ℕ} [NeZero D] {P I K B : Type} [Fintype P] [Fintype I] [Fintype B] [Field K]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (e : PaidIdentity K D m) (s : Stage m B d' child) (q : s.Index e)
    (old : ∀ j, Site.Programs (child j).pack.layout)
    {ns ne np : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (portID : (Fin k × P) ↪ Fin np)
    (seedName : ((I → Deck (d'+1)) × B) → ℕ) (position : e.Entry → ℕ)

namespace Stage

private noncomputable abbrev oldEdge := CutCircuit.denseRows (raw child).layout s.slot
private noncomputable abbrev cuts (v : s.input.layout.Site) :=
  Layer.orderedCuts s.input (oldEdge s) portID v e s.label s.perm seedName s.orient (0,false) q edgeID

/-- The complete bank installed at all actual retained and newly born sites on this histogram. -/
noncomputable def privatePrograms : Site.Programs (s.result e q).pack.layout := by
  let previous : s.input.layout.Site → Site := fun v => (old v.1 v.2).program
  let actual := roundSites e s.input s.label s.perm s.orient (0,false) q seedName position
    siteID edgeID portID previous (cuts e s q edgeID portID seedName)
  intro v
  rcases v with v | fresh
  · let prior := old v.1 v.2
    have size := prior.size.trans (s.input_incoming v.1 v.2).symm
    exact ⟨prior.birth,actual (.inl v),
      orderedRetention e s.input s.label s.perm seedName s.orient (0,false) q v (oldEdge s) edgeID portID prior.retention size,rfl⟩
  · exact Site.Lineage.start (actual (.inr fresh))
      (roundSites_incoming e s.input s.label s.perm s.orient (0,false) q seedName position
        siteID edgeID portID previous _ (.inr fresh))

/-- Old work and the original program follow the genuine retained host of the public stage. -/
theorem privatePrograms_birth (v : (raw child).layout.Site) :
    (s.privatePrograms e q old siteID edgeID portID seedName position
      ((normalizedStage e s q).site v)).birth = (old v.1 v.2).birth := rfl

end Stage

section Storage

variable {E : ℕ} {Q : Type} {widths : Q → ℕ} (p saved : PlacedPack D Q widths K I d)
    (edges : p.pack.layout.Edge ↪ Fin E) (stored : saved = p.dense edges)

/-- The actual second cable sort and the equality transporting it to the saved state. -/
noncomputable def privateStorage : Storage p.pack.layout saved.pack.layout := by
  rw [stored]
  exact Storage.dense _ edges

/-- Transport all installed programs through the second cable sort. Finiteness instances
for the same nested ports may be synthesized differently on the two sides. -/
noncomputable def carryPrivatePrograms {fin fin' : Fintype Q}
    (old : @Site.Programs D Q fin widths p.pack.layout) : @Site.Programs D Q fin' widths saved.pack.layout := by
  subst saved
  letI := fin
  exact fun v => (old v).castWidth ((dense_incoming p.pack.layout edges v).symm.trans (incoming_instances _ _))

omit [NeZero D] [Field K] in
/-- The site's birth program is carried by the very same saved host as the exterior ancestry. -/
theorem carryPrivatePrograms_birth {fin fin' : Fintype Q}
    (old : @Site.Programs D Q fin widths p.pack.layout) (v : p.pack.layout.Site) :
    (carryPrivatePrograms p saved edges stored (fin' := fin') old
      ((privateStorage p saved edges stored).site v)).birth = (old v).birth := by
  subst saved
  rfl

end Storage

namespace Program

variable {rounds : ℕ} {A : ℕ → Type*} {Bin : Fin rounds → Type} [∀ i, Fintype (Bin i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e} (F : Program (B := Bin) e view) (store : F.SaveNames)

/-- The site, port and seed rows of the actual public serializer on each selected output.
Its cable directory comes from the very same dense save as the state transition. -/
structure SiteRows where
  /-- Number of public site rows on this output. -/
  nSite : ∀ i (c : Fin k → A i.val), (F.stage i c).Index e → ℕ
  /-- Site injection emitted on that histogram. -/
  sites : ∀ i c (q : (F.stage i c).Index e), ((F.stage i c).result e q).pack.layout.Site ↪ Fin (nSite i c q)
  /-- Width of the current nested port directory. -/
  nPort : ℕ → ℕ
  /-- Rows of the actual current ports. -/
  ports : ∀ i, Port k P i ↪ Fin (nPort i)
  /-- Seed names used in this round's stable interval row order. -/
  seeds : ∀ i : Fin rounds, ((I → Deck (depth (i.val+1)+1)) × Bin i) → ℕ

variable (rows : F.SiteRows) (number : e.Entry → ℕ)

/-- Carry the entire selected sewn site program through the actual dense cable save. -/
noncomputable def savePrivatePrograms (i : Fin rounds) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout) :
    Site.Programs (view (i.val+1) (F.advance i c q)).pack.layout := by
  let st := F.stage i c
  let next := st.privatePrograms e q old (rows.sites i c q) (store.number i c q)
    (rows.ports (i.val+1)) (rows.seeds i) number
  exact carryPrivatePrograms (st.result e q) _ (store.number i c q) (store.stored i c q) next

/-- Host transport at the second dense save in the attained history. -/
noncomputable def siteStorage : DenseReplay.Saved F := fun i c q =>
  privateStorage ((F.stage i c).result e q) _ (store.number i c q) (store.stored i c q)

/-- The private birth program and exterior port lineage follow the same concrete saved host. -/
theorem savePrivatePrograms_birth (i : Fin rounds) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout) (v : (raw (fun j => view i.val (c j))).layout.Site) :
    (F.savePrivatePrograms store rows number i c q old
      ((F.siteStorage store i c q).site ((normalizedStage e (F.stage i c) q).site v))).birth =
      (old v.1 v.2).birth :=
  (carryPrivatePrograms_birth _ _ _ _ _ _).trans
    ((F.stage i c).privatePrograms_birth e q old _ _ _ _ _ v)

/-- Full private programs, including all earlier work tapes, on every attained saved histogram. -/
noncomputable def replayPrivatePrograms :
    (n : ℕ) → (hn : n ≤ rounds) → (a : Leaves k (A 0) n) →
    (initial : ∀ v : (parallelLeaves (fun x => (view 0 x).pack) n a).layout.Site, Site.Lineage
      (incoming (parallelLeaves (fun x => (view 0 x).pack) n a).layout v)) →
    (q : (F.system.histories n hn a).Index) →
    Site.Programs (view n (RowTrace.state F.system n hn a q)).pack.layout
  | 0, _, _, initial, _ => fun v => (initial v).castWidth (incoming_instances _ _)
  | n+1, hn, a, initial, q => by
    let hl := Nat.lt_of_succ_le hn
    let i : Fin rounds := ⟨n,hl⟩
    let c := fun j : Fin k => RowTrace.state F.system n hl.le (a j) (q.1 j)
    let children := fun j : Fin k => (parallelLeaves (fun x => (view 0 x).pack) n (a j)).layout
    let old (j : Fin k) := replayPrivatePrograms n hl.le (a j) (fun v =>
      (initial ⟨j,v⟩).castWidth ((incoming_instances _ _).trans (Inherited.Parallel.incoming_eq children j v))) (q.1 j)
    exact F.savePrivatePrograms store rows number i c q.2 old

/-- Every original private bank has exactly its original birth program at the actual
saved host of this full selected histogram. Newly inserted sites do not disturb its prefix. -/
theorem replayPrivatePrograms_birth (n : ℕ) (hn : n ≤ rounds) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (q : (F.system.histories n hn a).Index)
    (v : (parallelLeaves (fun x => (view 0 x).pack) n a).layout.Site) :
    (F.replayPrivatePrograms store rows number n hn a initial q
      ((normalizedAncestry F (F.siteStorage store) n hn a q).site v)).birth = (initial v).birth := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let hl := Nat.lt_of_succ_le hn
    let i : Fin rounds := ⟨n,hl⟩
    let c := fun j : Fin k => RowTrace.state F.system n hl.le (a j) (q.1 j)
    let children := fun j : Fin k => (parallelLeaves (fun x => (view 0 x).pack) n (a j)).layout
    let src (j : Fin k) (w : (children j).Site) := (initial ⟨j,w⟩).castWidth
      ((incoming_instances _ _).trans (Inherited.Parallel.incoming_eq children j w))
    let old := fun j : Fin k => F.replayPrivatePrograms store rows number n hl.le (a j) (src j) (q.1 j)
    let here := (normalizedAncestry F (F.siteStorage store) n hl.le (a v.1) (q.1 v.1)).site v.2
    exact (F.savePrivatePrograms_birth store rows number i c q.2 old ⟨v.1,here⟩).trans
      (ih hl.le (a v.1) (src v.1) (q.1 v.1) v.2)

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
