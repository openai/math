import OAI.Computability.BorderVNP.PackedCompilerFields
import OAI.Computability.BorderVNP.PackedFlatCompilerRows
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites
import OAI.Computability.BorderVNP.PackedSubdivisionCompilerRows

/-! # Compiler rows of every attained outer history

The selected epoch first subdivides its real child networks, then executes
the chosen normalized histories and returns their flat private banks.
Throughout the outer recursion the public row count, one-copy table size,
relative field scale and global ID scale retain their initial uniform bounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing

namespace Subdivision

open Shortening

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (route : N.WireRoutes) (oldID : N.Edge ↪ Fin m) (newID : (N.subdivide route).Edge ↪ Fin n)
    (portID : P ↪ Fin np)

/-- Subdivision leaves inherited box tables in place, and its newly born
equality relays have empty box lists. -/
theorem subdividePrivatePrograms_splitFields {V U : ℕ} (prior : Site.Programs N)
    (h : ∀ v, (prior v).program.SplitFields V U) (z : (N.subdivide route).Site) :
    (subdividePrivatePrograms N route oldID newID portID prior z).program.SplitFields V U := by
  rcases z with v | j
  · exact h v
  · intro fs hs
    exact False.elim (List.not_mem_nil hs)

end Subdivision

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxRecDepth 2500
set_option maxHeartbeats 1800000

universe u

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

/-- Transporting the actual site family to an equal stored layout preserves
every pointwise property of its executable programs. -/
theorem samePrivatePrograms_forall (Q : Site → Prop) {N M : Network D P bits} (h : N = M) (old : Site.Programs N)
    (good : ∀ v, Q (old v).program) : ∀ v, Q (samePrivatePrograms h old v).program := by
  subst M
  exact good

variable {m start T : ℕ} [NeZero D] {K : Type} [Field K]
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    (c : Fin (fan S) → Admissible good t) (old : ∀ i, Site.Programs (c i).val.pack.layout)

/-- Every physically subdivided child enters its actual inner epoch with
the same fixed row bounds and local/global scalar scales. -/
theorem installedPrivatePrograms_compilerFields {L U : ℕ}
    (h : ∀ j v, (old j v).program.CompilerFields e L U) (i : Fin (fan S)) :
    ∀ v, (E.installedPrivatePrograms rows c old i v).program.CompilerFields e L U := by
  let run := E.run c
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let prior := samePrivatePrograms orig (old i)
  let Q := fun s : Site => s.CompilerFields e L U
  have priorBound := samePrivatePrograms_forall Q orig (old i) (h i)
  let src : Site.Programs (P := Port S.fanIn (Port (fan S) P t) 0) a.pack.layout :=
    changePrivateInstance a.pack.layout prior
  let sub := Subdivision.subdividePrivatePrograms (P := Port S.fanIn (Port (fan S) P t) 0)
    a.pack.layout (a.routes.routes S.radius) raw.edge new.edge (rows.ports 0) src
  have localBound (v) : Q (src v).program := priorBound v
  have subBound (z) : Q (sub z).program :=
    ⟨Subdivision.subdividePrivatePrograms_compilerRows (P := Port S.fanIn (Port (fan S) P t) 0)
        a.pack.layout (a.routes.routes S.radius) raw.edge new.edge (rows.ports 0) e src (fun v => (localBound v).1) z,
      Subdivision.subdividePrivatePrograms_splitFields (P := Port S.fanIn (Port (fan S) P t) 0)
        a.pack.layout (a.routes.routes S.radius) raw.edge new.edge (rows.ports 0) src (fun v => (localBound v).2) z⟩
  exact samePrivatePrograms_forall (P := Port S.fanIn (Port (fan S) P t) 0) Q saved sub subBound

/-- Actual output at a selected outer histogram, after the independent child
subdivisions, the entire inner history and the final flat port transport. -/
theorem privatePrograms_compilerFields {L U : ℕ} (number : e.Entry → ℕ)
    (hL : tableLimit e ≤ L) (ids : ∀ z, number z ≤ U) (h : ∀ j v, (old j v).program.CompilerFields e L U)
    (q : E.F.Hist (E.run c).flat) : ∀ v, (E.privatePrograms rows c old number q v).program.CompilerFields e L U := by
  let src := E.installedPrivatePrograms rows c old
  let flat := (E.run c).flat
  have ini := E.installedPrivatePrograms_compilerFields rows c old h
  have shapes := E.F.flatPrivatePrograms_compilerRows E.saveNames rows number flat src q (fun i v => (ini i v).1)
  have fields := E.F.flatPrivatePrograms_splitFields E.saveNames rows number flat src q hL ids (fun i v => (ini i v).2)
  exact fun v => ⟨shapes v,fields v⟩

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)

omit [∀ t, Fintype (W t)] in
private theorem choice_forall {n : ℕ} (Q : Site → Prop) {Z Y : ProfileSum (Admissible good (n+1))}
    (h : Z = Y) (prog : ∀ q : Y.Index, Site.Programs (Y.term q).val.pack.layout)
    (ok : ∀ q v, Q (prog q v).program) :
    ∀ q v, Q ((Eq.mpr (congrArg (fun z => ∀ q : z.Index, Site.Programs (z.term q).val.pack.layout) h) prog) q v).program := by
  subst Z
  exact ok

/-- The public branch at a live outer depth is the selected epoch's
concrete histogram. Any pointwise property proved on that epoch's output
holds on the transported private program. -/
theorem stepPrivatePrograms_forall (Q : Site → Prop) {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, Site.Programs (c j).val.pack.layout)
    (step : ∀ q v, Q ((M n hn).privatePrograms (rows n hn) c old number q v).program) :
    ∀ (q : (M.epoch n c).Index) v, Q ((M.stepPrivatePrograms rows number hn c old q v).program) := by
  let E := M n hn
  have live : M.epoch n c = E.choice c := dite_eq_left hn
  exact choice_forall Q live (E.privatePrograms (rows n hn) c old number) step

/-- The selected live branch of one outer step preserves all compiler field
bounds on its actual returned site programs. -/
theorem stepPrivatePrograms_compilerFields {n L U : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, Site.Programs (c j).val.pack.layout) (hL : tableLimit e ≤ L)
    (ids : ∀ z, number z ≤ U) (prior : ∀ j v, (old j v).program.CompilerFields e L U) :
    ∀ (q : (M.epoch n c).Index) v, (M.stepPrivatePrograms rows number hn c old q v).program.CompilerFields e L U := by
  exact M.stepPrivatePrograms_forall rows number (fun s => s.CompilerFields e L U) hn c old
    ((M n hn).privatePrograms_compilerFields (rows n hn) c old number hL ids prior)

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- Induction through the actual outer epoch ordinals. Every independent
child supplies its own previous site program at its own selected history. -/
theorem historyPrivatePrograms_forall (Q : ℕ → Site → Prop)
    (step : ∀ (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
      (old : ∀ j, Site.Programs (c j).val.pack.layout), (∀ j v, Q n (old j v).program) →
      ∀ q v, Q (n+1) ((M n hn).privatePrograms (rows n hn) c old number q v).program)
    (initial : ∀ v, Q 0 (base v).program) (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) :
    ∀ v, Q n ((M.historyPrivatePrograms rows number bottom base n hn q v).program) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    exact M.stepPrivatePrograms_forall rows number (Q (n+1)) (Nat.lt_of_succ_le hn) _ _
      (step n (Nat.lt_of_succ_le hn) _ _ (fun j => ih (Nat.le_of_succ_le hn) (q.1 j))) q.2

/-- All sites in all actual attained outer histories receive the uniform
bounds of the input family. The width and table constants precede the depth,
the histogram choices, and the final site. -/
theorem historyPrivatePrograms_compilerFields {L U : ℕ} (hL : tableLimit e ≤ L) (ids : ∀ z, number z ≤ U)
    (initial : ∀ v, (base v).program.CompilerFields e L U) (n : ℕ) (hn : n ≤ T)
    (q : (packHistory bottom M.epoch n).Index) :
    ∀ v, (M.historyPrivatePrograms rows number bottom base n hn q v).program.CompilerFields e L U := by
  exact M.historyPrivatePrograms_forall rows number bottom base (fun _ s => s.CompilerFields e L U)
    (fun n hn c old prior => (M n hn).privatePrograms_compilerFields (rows n hn) c old number hL ids prior)
    initial n hn q

/-- On the owner-sorted directory of any attained outer history, the
public profile checker, record serializer, and private box serializer all
receive the bounds proved for that very history. Final incidence bindings
and arbitrary physical placement offsets are included in the statement. -/
theorem historyDirectory_compilerFields {L U : ℕ} (hL : tableLimit e ≤ L) (ids : ∀ z, number z ≤ U)
    (initial : ∀ v, (base v).program.CompilerFields e L U) (n : ℕ) (hn : n ≤ T)
    (q : (packHistory bottom M.epoch n).Index) :
    let N := ((packHistory bottom M.epoch n).term q).val.pack.layout
    let state := fun v => (M.historyPrivatePrograms rows number bottom base n hn q v).program
    ∀ {ns ne np : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
      (portID : Port (fan S) P n ↪ Fin np) (owner : Fin ns → ℕ) (cell : N.Site → ℕ)
      (c : ℕ) (reports : List (List ℕ)),
      let dir := FinalCell.directory owner N cell siteID edgeID portID state c reports
      dir.ProfileWidths ∧ (∀ r ∈ dir.records, (CellSparse.Packet.record r).length ≤ 16*(e.count+1)) ∧
        ∀ fs ∈ dir.boxes, ∀ f ∈ fs, f.TableBound (tableLimit e) ∧ f.FieldBound L ∧ f.IDBound U := by
  intro N state ns ne np siteID edgeID portID owner cell c reports dir
  have h := M.historyPrivatePrograms_compilerFields rows number bottom base hL ids initial n hn q
  have ht := sortedDirectory_tableBound N cell siteID edgeID portID owner state c reports (fun v => (h v).1.2.2)
  have hf := sortedDirectory_splitFields N cell siteID edgeID portID owner state c reports (fun v => (h v).2)
  exact ⟨FinalCell.directory_profileWidths owner N cell siteID edgeID portID state c reports
      (fun v _ => (h v).1.1),
    FinalCell.directory_rowBound owner N cell siteID edgeID portID state c reports (by omega)
      (fun v _ => (h v).1.2.1),fun fs hx f hy => ⟨ht fs hx f hy,hf fs hx f hy⟩⟩

end Machine

end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
