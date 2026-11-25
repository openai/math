import OAI.Computability.BorderVNP.DiagonalOriginalRowExecution
import OAI.Computability.BorderVNP.DiagonalDenseTerminal

/-! # Physical sparse row arrays on the sorted site factory's exact histograms -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Cover Crossing Shortening Adaptive Packing Epoch Epoch.Round CellEntries PublicCapacity
open PackedHistoryCircuit
open scoped Classical BorderVNP.Epoch.Cube

variable {D m d : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {M : Normalized.SiteMachine S d P bits}
    {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
    (run : Normalized.SiteExecution S M input route)

omit [NeZero D] in
/-- The capacity of the site-only lookup is exactly the site component of
the public recurrence that also reserves the cable bands. -/
theorem capacities_eq (fan : ℕ) (seeds : ℕ → ℕ) (base : Shape) (n : ℕ) :
    capacities e fan base.sites seeds n = (combineRows e fan seeds base n).sites := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change StaticRows.siteCapacity e (fan*capacities e fan base.sites seeds n) (seeds n) =
      StaticRows.siteCapacity e (fan*(combineRows e fan seeds base n).sites) (seeds n)
    rw [ih]

variable {s : Shape}

/-- Actual rows of an installed leaf, including the equality sites inserted
by the dense site schedule's initial routes. -/
noncomputable def denseInstalledRows (i : Fin (S.fanIn^S.rounds)) (old : Rows s (input i).layout) :
    Rows (s.subdivide ⌈S.budget/S.radius⌉₊) (run.flat i).val.pack.layout := by
  let a := run.initialSites i
  let orig := sameRows (congrArg Pack.layout (run.originalPack i).symm) old
  exact sameRows (congrArg (fun p => p.pack.layout) a.realizes.symm) (orig.siteRoutes a.routes S.radius)

/-- Initial subdivision in the actual dense execution keeps an original
attachment's integer row. -/
theorem denseInstalledRows_attach (i : Fin (S.fanIn^S.rounds)) (old : Rows s (input i).layout) (p : P) :
    ((denseInstalledRows run i old).site ((run.flat i).val.pack.layout.attach p)).val =
      (old.site ((input i).layout.attach p)).val := by
  let a := run.initialSites i
  let orig := sameRows (congrArg Pack.layout (run.originalPack i).symm) old
  let sub := orig.siteRoutes a.routes S.radius
  refine (congrArg Fin.val (sameRows_attach (congrArg (fun p => p.pack.layout) a.realizes.symm) sub p)).trans ?_
  exact congrArg Fin.val (sameRows_attach (congrArg Pack.layout (run.originalPack i).symm) old p)

variable (base : Shape) (seeds : ℕ → ℕ)
    (seed : ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level d (i.val+1)+1)) × (S.source.asPath.pattern i).Bin) ↪ Fin (seeds i.val))

/-- The stable sparse edge IDs through both physical sorts of a normalized
stage. Old-band, hook and seed edges use the actual sorted allocator. -/
noncomputable def denseEdges :
    (n : ℕ) → (hn : n ≤ S.rounds) → (flat : Fin (S.fanIn^n) → S.State d P bits 0) →
    (∀ i, (flat i).val.pack.layout.Edge ↪ Fin base.edges) →
    (q : (M.F.system.histories n hn (leavesEquiv S.fanIn _ n flat)).Index) →
    (state M.F.system n hn (leavesEquiv S.fanIn _ n flat) q).val.pack.layout.Edge ↪
      Fin (combineRows e S.fanIn seeds base n).edges
  | 0, _, _, rows, _ => rows 0
  | n+1, hn, flat, rows, q => by
    let hl := Nat.lt_of_succ_le hn
    let i : Fin S.rounds := ⟨n,hl⟩
    let f := fun j : Fin S.fanIn => fun x => flat (copyIndex S.fanIn n (j,x))
    let c := fun j : Fin S.fanIn => state M.F.system n hl.le (leavesEquiv S.fanIn _ n (f j)) (q.1 j)
    let st := M.F.stage i c
    let old := PublicParallel.parallelName
      (fun j => denseEdges n hl.le (f j) (fun x => rows (copyIndex S.fanIn n (j,x))) (q.1 j))
    let actual := (Names.denseSlot (Normalized.raw fun j => (c j).val).layout st.slot).symm.toEmbedding.trans old
    let out := StaticRows.outputRows e st.input st.label st.perm st.orient (0,false) q.2 actual (seed i)
    let after := (M.after i c st q.2).number
    change (M.F.advance i c q.2).val.pack.layout.Edge ↪ _
    rw [M.stored i c q.2]
    exact (Names.denseSlot (st.result e q.2).pack.layout after).symm.toEmbedding.trans out

/-- The public site's exact row and the true cable's stable sparse ID at
every terminal histogram of the normalized site epoch. -/
noncomputable def denseEpochDirectory (rows : ∀ i, Rows base (input i).layout) (q : Fin run.expansion.terms) :
    Rows (combineRows e S.fanIn seeds (base.subdivide ⌈S.budget/S.radius⌉₊) S.rounds)
      (run.expansion.pack q).layout := by
  let sub := base.subdivide ⌈S.budget/S.radius⌉₊
  let initial := fun i => denseInstalledRows run i (rows i)
  let step := normalized e sub.sites seeds seed M.F (DenseSiteReplay.storage M)
  exact ⟨(historyRows step S.rounds le_rfl run.flat (fun i => (initial i).site) (run.enum q)).trans
    (finCongr (capacities_eq (e := e) S.fanIn seeds sub S.rounds)).toEmbedding,
    denseEdges (M := M) sub seeds seed S.rounds le_rfl run.flat (fun i => (initial i).edge) (run.enum q)⟩

/-- Every public port in the attained sorted epoch is at the original row
plus the predetermined offsets of its row-major leaf digits. -/
theorem denseEpochDirectory_attach (rows : ∀ i, Rows base (input i).layout) (q : Fin run.expansion.terms)
    (u : Fin (S.fanIn^S.rounds)) (p : P) :
    ((denseEpochDirectory run base seeds seed rows q).site ((run.expansion.pack q).layout.attach (u,p))).val =
      flatOffset (fun level j => j.val * capacities e S.fanIn
        (base.subdivide ⌈S.budget/S.radius⌉₊).sites seeds level) S.rounds u +
        ((rows u).site ((input u).layout.attach p)).val := by
  let sub := base.subdivide ⌈S.budget/S.radius⌉₊
  let initial := fun i => denseInstalledRows run i (rows i)
  let step := normalized e sub.sites seeds seed M.F (DenseSiteReplay.storage M)
  exact (flat_attach step S.rounds le_rfl run.flat (fun i => (initial i).site) (run.enum q) u p).trans
    (congrArg (_ + ·) (denseInstalledRows_attach run u (rows u) p))

end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
