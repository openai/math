import OAI.Computability.BorderVNP.DiagonalOriginalRowStages
import OAI.Computability.BorderVNP.DiagonalExternalSewEpoch
import OAI.Computability.BorderVNP.ShortenPublicSubdivisionRows

/-! # Sparse row transport through a real site epoch

The initial equality subdivision, every selected shortening histogram and
the final flattening carry the exact rows of the padded public serializer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Cover Crossing Shortening Adaptive Packing Epoch Epoch.Round CellEntries PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube

variable {D : ℕ} {P : Type} {bits : P → ℕ} {s : Shape}

/-- Change only the recorded presentation of an identical layout. -/
def sameRows {N M : Network D P bits} (h : N = M) (old : Rows s N) : Rows s M := h ▸ old

/-- The row of every external attachment agrees across this identity. -/
theorem sameRows_attach {N M : Network D P bits} (h : N = M) (old : Rows s N) (p : P) :
    (sameRows h old).site (M.attach p) = old.site (N.attach p) := by subst M; rfl

variable {m rounds k : ℕ} [NeZero D] {E : Type} [Field E] [Fintype P] {e : PaidIdentity E D m}
    {h H ν : ℝ} {path : StagePath rounds e (Cube D) h H ν} {C : Fin rounds → ℕ}
    {last high : ℕ} {hk : 0 < k} {machine : SiteMachine path C last high hk P bits}
    {low : ℕ} {L weight error A Cout : ℝ} {cap : ℕ} {hh : 0 < h}
    {input : Fin (k^rounds) → Pack D P bits E} {route : ∀ i, SiteRoutes (input i) (Cube D) high L}
    (run : SiteExecution (low := low) machine hh input route weight error A Cout cap)

/-- Install the actual sparse rows at the machine's starting states after
reserving the full equality-subdivision stripe for each original cable. -/
noncomputable def installedRows (i : Fin (k^rounds)) (old : Rows s (input i).layout) :
    Rows (s.subdivide ⌈L/h⌉₊) (run.flat i).val.pack.layout := by
  let a := run.initialSites i
  let original := sameRows (congrArg Pack.layout (run.originalPack i).symm) old
  let subdivided := original.siteRoutes a.routes h
  exact sameRows (congrArg (fun p => p.pack.layout) a.realizes.symm) subdivided

/-- Even an original tile with many attached port bits keeps its same public
site number through the true equality subdivision. -/
theorem installedRows_attach (i : Fin (k^rounds)) (old : Rows s (input i).layout) (p : P) :
    ((installedRows run i old).site ((run.flat i).val.pack.layout.attach p)).val =
      (old.site ((input i).layout.attach p)).val := by
  let a := run.initialSites i
  let original := sameRows (congrArg Pack.layout (run.originalPack i).symm) old
  let sub := original.siteRoutes a.routes h
  refine (congrArg Fin.val (sameRows_attach (congrArg (fun p => p.pack.layout) a.realizes.symm) sub p)).trans ?_
  exact congrArg Fin.val (sameRows_attach (congrArg Pack.layout (run.originalPack i).symm) old p)

section ProgramRows

variable {b : ℕ} {I : Type} [Fintype I] {State : ℕ → Type*}
    {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {view : ∀ n, State n → PlacedPack D (Port k P n) (width bits k n) E I (depth n)}
    (F : Adaptive.Program (B := B) e view)
    (stored : ∀ i c q, (view (i.val+1) (F.advance i c q)).pack.layout = ((F.step i c).result e q).pack.layout)
    (base : Shape) (seeds : ℕ → ℕ)
    (seed : ∀ i : Fin b, ((I → Deck (depth (i.val+1)+1)) × B i) ↪ Fin (seeds i.val))

/-- Generate both row arrays by the real parallel and sewn operations at
each attained histogram. These include the old-band, hook and bank edge IDs. -/
noncomputable def executedRows :
    (n : ℕ) → (hn : n ≤ b) → (flat : Fin (k^n) → State 0) →
    (∀ i, Rows base (view 0 (flat i)).pack.layout) →
    (q : (F.system.histories n hn (leavesEquiv k (State 0) n flat)).Index) →
    Rows (combineRows e k seeds base n) (view n (state F.system n hn (leavesEquiv k (State 0) n flat) q)).pack.layout
  | 0, _, _, bottom, _ => bottom 0
  | n+1, hn, flat, bottom, q => by
    let hl := Nat.lt_of_succ_le hn
    let i : Fin b := ⟨n,hl⟩
    let f := fun j : Fin k => fun x => flat (copyIndex k n (j,x))
    let c := fun j : Fin k => state F.system n hl.le (leavesEquiv k (State 0) n (f j)) (q.1 j)
    let old := Rows.parallel (p := fun j => (view n (c j)).pack)
      (fun j => executedRows n hl.le (f j) (fun x => bottom (copyIndex k n (j,x))) (q.1 j))
    let node := F.step i c
    let out := Rows.sew e _ node.bin node.perm node.positive q.2 (0,false) old (seed i)
    exact sameRows (stored i c q.2).symm out

omit [Fintype P] in
/-- The original port's row in these specific directories is a function only
of its fixed bottom row, the flat leaf ordinal and the public capacities. -/
theorem executedRows_attach (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → State 0)
    (bottom : ∀ i, Rows base (view 0 (flat i)).pack.layout)
    (q : (F.system.histories n hn (leavesEquiv k (State 0) n flat)).Index) (p : Port k P n) :
    let z := portEquiv k P n p
    ((executedRows F stored base seeds seed n hn flat bottom q).site
      ((view n (state F.system n hn (leavesEquiv k (State 0) n flat) q)).pack.layout.attach p)).val =
      flatOffset (fun level j => j.val*(combineRows e k seeds base level).sites) n z.1 +
        ((bottom z.1).site ((view 0 (flat z.1)).pack.layout.attach z.2)).val := by
  induction n with
  | zero => exact (Nat.zero_add _).symm
  | succ n ih =>
    rcases p with ⟨j,p⟩
    let hl := Nat.lt_of_succ_le hn
    let i : Fin b := ⟨n,hl⟩
    let f := fun u : Fin k => fun x => flat (copyIndex k n (u,x))
    let c := fun u : Fin k => state F.system n hl.le (leavesEquiv k (State 0) n (f u)) (q.1 u)
    let child := fun u : Fin k => executedRows F stored base seeds seed n hl.le (f u)
      (fun x => bottom (copyIndex k n (u,x))) (q.1 u)
    let old := Rows.parallel (p := fun u => (view n (c u)).pack) child
    let node := F.step i c
    let out := Rows.sew e _ node.bin node.perm node.positive q.2 (0,false) old (seed i)
    refine (congrArg Fin.val (sameRows_attach (stored i c q.2).symm out (j,p))).trans ?_
    let rows := (combineRows e k seeds base n).sites
    change ((child j).site ((view n (c j)).pack.layout.attach p)).val + rows*j.val = _
    rw [portEquiv_succ,flatOffset_succ]
    have hc := ih hl.le (f j) (fun x => bottom (copyIndex k n (j,x))) (q.1 j) p
    change ((child j).site ((view n (c j)).pack.layout.attach p)).val = _ at hc
    rw [hc]
    ac_rfl

end ProgramRows
end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
