import OAI.Computability.BorderVNP.PackedCompilerRows
import OAI.Computability.BorderVNP.PackedFieldBoundSites
import OAI.Computability.BorderVNP.PackedBankPrivateReplay

/-! # Fixed compiler rows through the actual selected private history

Every attained child carries its own executable private programs. A public
crossing stage installs their retained and fresh site programs, and the dense
save reorders the cables. Induction on the actual histogram trace carries the
fixed row bounds through both operations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Shortening.CombiningStep
open Diagonal.ExternalSew Diagonal.CellEntries Epoch.Round
open scoped Classical
attribute [local instance] portFintype

variable {D m k d d' : ℕ} [NeZero D] {P I K B : Type} [Fintype P] [Fintype I] [Fintype B] [Field K]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (e : PaidIdentity K D m) (s : Stage m B d' child) (q : s.Index e)
    (old : ∀ j, Site.Programs (child j).pack.layout)
    {ns ne np : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (portID : (Fin k × P) ↪ Fin np)
    (seedName : ((I → Deck (d'+1)) × B) → ℕ) (position : e.Entry → ℕ)

namespace Stage

/-- Each private lineage exposes precisely the executable retained or born
site installed at its true host by the crossing stage. -/
theorem privatePrograms_program (v : (s.result e q).pack.layout.Site) :
    (s.privatePrograms e q old siteID edgeID portID seedName position v).program =
      roundSites e s.input s.label s.perm s.orient (0,false) q seedName position siteID edgeID portID
        (fun u => (old u.1 u.2).program)
        (fun u => Layer.orderedCuts s.input (CutCircuit.denseRows (raw child).layout s.slot) portID
          u e s.label s.perm seedName s.orient (0,false) q edgeID) v := by
  rcases v with oldV | fresh <;> rfl

set_option maxHeartbeats 1800000 in
/-- On each attained histogram, every current site is exactly the installed
site of the selected crossing, with the same fixed compiler bounds. -/
theorem privatePrograms_compilerRows (prior : ∀ j v, ((old j v).program).CompilerRows e)
    (v : (s.result e q).pack.layout.Site) :
    ((s.privatePrograms e q old siteID edgeID portID seedName position v).program).CompilerRows e := by
  rw [s.privatePrograms_program e q old siteID edgeID portID seedName position v]
  exact roundSites_compilerRows e s.input s.label s.perm s.orient (0,false) q seedName position
    siteID edgeID portID _ _ (fun u => prior u.1 u.2) v

/-- The local scalar address and global signed ID scales hold on each
selected installed one-copy table. -/
theorem privatePrograms_splitFields {V U : ℕ} (localSize : tableLimit e ≤ V)
    (globalIDs : ∀ z, position z ≤ U) (prior : ∀ j v, (old j v).program.SplitFields V U)
    (v : (s.result e q).pack.layout.Site) :
    (s.privatePrograms e q old siteID edgeID portID seedName position v).program.SplitFields V U := by
  rw [s.privatePrograms_program e q old siteID edgeID portID seedName position v]
  exact roundSites_splitFields e s.input s.label s.perm s.orient (0,false) q seedName position
    siteID edgeID portID _ _ localSize globalIDs (fun u => prior u.1 u.2) v

end Stage

namespace Program

variable {rounds : ℕ} {A : ℕ → Type*} {Bin : Fin rounds → Type} [∀ i, Fintype (Bin i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e} (F : Program (B := Bin) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

omit [NeZero D] [Field K] in
private theorem carry_forall {E : ℕ} {P : Type} {b : P → ℕ} {fin fin' : Fintype P} {d : ℕ}
    (Q : Site → Prop) (p saved : PlacedPack D P b K I d) (edges : p.pack.layout.Edge ↪ Fin E)
    (h : saved = p.dense edges) (u : @Site.Programs D P fin b p.pack.layout) (good : ∀ v, Q (u v).program) :
    ∀ v, Q ((carryPrivatePrograms p saved edges h (fin' := fin') u v).program) := by
  subst saved
  exact good

set_option maxHeartbeats 1800000 in
/-- Reindexing the selected programs through the exact saved cable order
preserves any pointwise property of the executable site program. -/
theorem savePrivatePrograms_forall (Q : Site → Prop) (i : Fin rounds) (c : Fin k → A i.val)
    (q : (F.stage i c).Index e) (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout)
    (step : ∀ v, Q (((F.stage i c).privatePrograms e q old (rows.sites i c q)
      (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number v).program)) :
    ∀ v, Q ((F.savePrivatePrograms store rows number i c q old v).program) := by
  let st := F.stage i c
  let next := st.privatePrograms e q old (rows.sites i c q) (store.number i c q)
    (rows.ports (i.val+1)) (rows.seeds i) number
  exact carry_forall Q (st.result e q) (view (i.val+1) (F.advance i c q)) (store.number i c q)
    (store.stored i c q) next step

set_option maxHeartbeats 1800000 in
/-- A depth-indexed site invariant that holds at each selected private
transition holds on every replayed program. The induction follows the same
child and histogram indices as the native history. -/
theorem replayPrivatePrograms_induction (Q : ℕ → Site → Prop)
    (step : ∀ (i : Fin rounds) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
      (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout),
      (∀ j v, Q i.val (old j v).program) → ∀ v,
      Q (i.val+1) (((F.stage i c).privatePrograms e q old (rows.sites i c q)
        (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number v).program))
    (n : ℕ) (hn : n ≤ rounds) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (bottom : ∀ v, Q 0 (initial v).program) (q : (F.system.histories n hn a).Index) :
    ∀ v, Q n ((F.replayPrivatePrograms store rows number n hn a initial q v).program) := by
  let good := fun (i : ℕ) (x : A i) (pr : Site.Programs (view i x).pack.layout) => ∀ v, Q i (pr v).program
  apply F.replayPrivatePrograms_invariant store rows number good
    (fun i c q old prior => F.savePrivatePrograms_forall store rows number (Q (i.val+1)) i c q old
      (step i c q old prior)) n hn a initial ?_ q
  clear q hn
  induction n with
  | zero => exact bottom
  | succ n ih =>
    intro j
    exact ih (a j) (subInitial (view := view) n a initial j) (fun v => bottom ⟨j,v⟩)

set_option maxHeartbeats 1800000 in
/-- At every actual attained state, the compiler receives the same fixed
per-record and per-factor bounds chosen from the paid identity, and its
selector widths remain valid. -/
theorem replayPrivatePrograms_compilerRows (n : ℕ) (hn : n ≤ rounds) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (bottom : ∀ v, (initial v).program.CompilerRows e) (q : (F.system.histories n hn a).Index) :
    ∀ v, (F.replayPrivatePrograms store rows number n hn a initial q v).program.CompilerRows e :=
  F.replayPrivatePrograms_induction store rows number (fun _ s => s.CompilerRows e)
    (fun i c q old h => (F.stage i c).privatePrograms_compilerRows e q old (rows.sites i c q)
      (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number h) n hn a initial bottom q

/-- The same true selected history carries the separate local scalar and
global ID scales. An ID's numeric value is independent of the dimension of
the factor table containing it. -/
theorem replayPrivatePrograms_splitFields {V U : ℕ} (localSize : tableLimit e ≤ V)
    (globalIDs : ∀ z, number z ≤ U) (n : ℕ) (hn : n ≤ rounds) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (bottom : ∀ v, (initial v).program.SplitFields V U) (q : (F.system.histories n hn a).Index) :
    ∀ v, (F.replayPrivatePrograms store rows number n hn a initial q v).program.SplitFields V U :=
  F.replayPrivatePrograms_induction store rows number (fun _ s => s.SplitFields V U)
    (fun i c q old h => (F.stage i c).privatePrograms_splitFields e q old (rows.sites i c q)
      (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number localSize globalIDs h) n hn a initial bottom q

end Program

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
