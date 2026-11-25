import OAI.Computability.BorderVNP.DiagonalOriginalRowDenseEpoch
import OAI.Computability.BorderVNP.DiagonalExternalSewDenseFactory

/-! # Fixed numeric host lookup through all outer sorted site epochs

The row allocated to an original public port is computed from the initial
site row and the leaf digits in each epoch's padded schedule. The complete
site and cable directories use the measured dense factory's own branch index.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Cover Crossing Shortening Adaptive Packing Packing.PhysicalEpochs Epoch Epoch.Round CellEntries PublicCapacity
open PackedHistoryCircuit
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- Actual seed rectangle size for a given outer level and inner round. -/
noncomputable def seedCount (start t n : ℕ) :=
  if hi : n < S.rounds then
    Fintype.card ((Cube D → Deck (S.level (start-S.drop*(t+1)-1) (n+1)+1)) ×
      (S.source.asPath.pattern ⟨n,hi⟩).Bin)
  else 0

/-- The seed names are fixed before the profile, in the full public rectangle. -/
noncomputable def seedNumber (start t : ℕ) (i : Fin S.rounds) :
    ((Cube D → Deck (S.level (start-S.drop*(t+1)-1) (i.val+1)+1)) ×
      (S.source.asPath.pattern i).Bin) ↪ Fin (seedCount S start t i.val) :=
  (Fintype.equivFin _).toEmbedding.trans (finCongr (by simp only [seedCount,dite_eq_left i.isLt])).toEmbedding

/-- The scheduled padded site and cable dimensions at an outer boundary. -/
noncomputable abbrev outerShape (start : ℕ) (initial : Shape) :=
  epochRows e S.fanIn S.rounds ⌈S.budget/S.radius⌉₊ (seedCount S start) initial

/-- Fixed child offset of a given outer epoch, computed from the inner child
digits and the same public row capacities used by the dense program. -/
noncomputable def outerOffset (start : ℕ) (initial : Shape) (t : ℕ) (u : Fin (S.fanIn^S.rounds)) :=
  let base := (outerShape S start initial t).subdivide ⌈S.budget/S.radius⌉₊
  flatOffset (fun j (i : Fin S.fanIn) => i.val*capacities e S.fanIn base.sites (seedCount S start t) j) S.rounds u

variable {S} (program : Factory.Dense.Programs S) {start T : ℕ}
    (deep : (Factory.ofDenseSchedule program).floor+1+(Factory.ofDenseSchedule program).drop*T ≤ start)
    (initial : Shape)

/-- The actual rows produced by one physical sorted epoch, together with its
numeric lookup for every supplied original port. -/
noncomputable def stageRows {t : ℕ} (ht : t < T)
    (c : Fin (Factory.ofDenseSchedule program).fan → (Factory.ofDenseSchedule program).State bits start t)
    (rows : ∀ j, Rows (outerShape S start initial t) (c j).pack.layout) :
    ∀ q : ((Factory.ofDenseSchedule program).epoch deep t c).Index,
      {s : Rows (outerShape S start initial (t+1))
          (((Factory.ofDenseSchedule program).epoch deep t c).term q).pack.layout //
        ∀ i p, (s.site ((((Factory.ofDenseSchedule program).epoch deep t c).term q).pack.layout.attach (i,p))).val =
          outerOffset S start initial t i + ((rows i).site ((c i).pack.layout.attach p)).val} := by
  unfold Factory.epoch
  rw [dite_eq_left ht]
  intro q
  let run := DenseTerminal.execution program deep ht c
  exact ⟨denseEpochDirectory run _ (seedCount S start t) (seedNumber S start t) rows q,
    denseEpochDirectory_attach run _ (seedCount S start t) (seedNumber S start t) rows q⟩

variable (bottom : (Factory.ofDenseSchedule program).State bits start 0)
    (rows : Rows initial bottom.pack.layout)

/-- Replay all selected sparse row embeddings along the actual outer history. -/
noncomputable def outerDirectory :
    (n : ℕ) → n ≤ T → (q : ((Factory.ofDenseSchedule program).histories deep bottom n).Index) →
    Rows (outerShape S start initial n) (((Factory.ofDenseSchedule program).histories deep bottom n).term q).pack.layout
  | 0, _, _ => rows
  | n+1, hn, q =>
    (stageRows program deep initial (Nat.lt_of_succ_le hn)
      (fun j => ((Factory.ofDenseSchedule program).histories deep bottom n).term (q.1 j))
      (fun j => outerDirectory n (Nat.le_of_succ_le hn) (q.1 j)) q.2).val

/-- Arithmetic evaluation of the original port row in the true attained
terminal directory. All quantities on the right precede the history index. -/
theorem outerDirectory_attach (n : ℕ) (hn : n ≤ T)
    (q : ((Factory.ofDenseSchedule program).histories deep bottom n).Index)
    (p : Port (Factory.ofDenseSchedule program).fan P n) :
    let F := Factory.ofDenseSchedule program
    let z := portEquiv F.fan P n p
    ((outerDirectory program deep initial bottom rows n hn q).site
      (((F.histories deep bottom n).term q).pack.layout.attach p)).val =
      flatOffset (outerOffset S start initial) n z.1 + (rows.site (bottom.pack.layout.attach z.2)).val := by
  induction n with
  | zero => exact (Nat.zero_add _).symm
  | succ n ih =>
    rcases p with ⟨i,p⟩
    let F := Factory.ofDenseSchedule program
    let H := F.histories deep bottom n
    let hl := Nat.lt_of_succ_le hn
    let c := fun j : Fin F.fan => H.term (q.1 j)
    let old := fun j : Fin F.fan => outerDirectory program deep initial bottom rows n hl.le (q.1 j)
    have he := (stageRows program deep initial hl c old q.2).property i p
    have hi := ih hl.le (q.1 i) p
    dsimp only at hi ⊢
    refine he.trans ((congrArg (outerOffset S start initial n i + ·) hi).trans ?_)
    let z := portEquiv F.fan P n p
    let f := outerOffset S start initial
    let leaf := (rows.site (bottom.pack.layout.attach z.2)).val
    change f n i + (flatOffset f n z.1 + leaf) = flatOffset f (n+1) (copyIndex F.fan n (i,z.1)) + leaf
    exact (Nat.add_assoc ..).symm.trans (congrArg (· + leaf) (flatOffset_succ f n i z.1).symm)

/-- The numeric ID of the retained original attachment can be computed
without reading a history bit. The left side follows the true compressed
host map and the real sparse row table for that history. -/
theorem retained_name (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index)
    (u : Fin ((Factory.ofDenseSchedule program).fan^T)) (p : P) :
    let host := denseOuterHosts program deep bottom q
    ((outerDirectory program deep initial bottom rows T le_rfl q).site (host.site ⟨u,bottom.pack.layout.attach p⟩)).val =
      flatOffset (outerOffset S start initial) T u + (rows.site (bottom.pack.layout.attach p)).val := by
  let F := Factory.ofDenseSchedule program
  let lookup (z : Fin (F.fan^T) × P) :=
    flatOffset (outerOffset S start initial) T z.1 + (rows.site (bottom.pack.layout.attach z.2)).val
  let host := denseOuterHosts program deep bottom q
  let dir := outerDirectory program deep initial bottom rows T le_rfl q
  exact (congrArg (fun v => (dir.site v).val) (host.attach (u,p)).symm).trans
    ((outerDirectory_attach program deep initial bottom rows T le_rfl q ((portEquiv F.fan P T).symm (u,p))).trans
      (congrArg lookup ((portEquiv F.fan P T).apply_symm_apply (u,p))))

end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
