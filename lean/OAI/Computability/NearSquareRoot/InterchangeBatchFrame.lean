import OAI.Computability.NearSquareRoot.InterchangeBatchRows
import OAI.Computability.NearSquareRoot.InterchangeFrame
import OAI.Computability.IntegerMultiplication.Loom.Fare

/-!
# Batching a central interchange in the native spectator layout

The first digit of the earlier field lives at the end of the prefix tape.
Each child has the same coordinate order, with this digit replaced by a
quotient spectator. Prefix dimensions, the gap, and the suffix may all vary.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BatchFrame

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress

variable {I J : Type} {n b : ℕ} (ord : J ≃ Fin n) (P G B : I → Tape) (f : I → ℕ)

abbrev front (k : ℕ) := fun i => P i ++ [k]
abbrev rows (k : ℕ) := layoutRows (b := b) ord (front P k) G B f
abbrev Value (k : ℕ) := (i : I) → Keys (front P k i) (G i) (B i) J (Block b (f i)) → Tree
abbrev outer := fun i => Dims.layout (P i)
abbrev tail (i : I) := (threads (line b (f i)) ord).cart
  ((Dims.layout (G i)).cart ((threads (line b (f i)) ord).cart (Dims.layout (B i))))

/-- `[P] × [k]` has exactly the native order and address representation
of the augmented prefix tape. -/
def prefixView (D : Tape) (k : ℕ) : Adopt ((Dims.layout D).cart (Series.natural k))
    (Dims.layout (D ++ [k])) :=
  let digit : Adopt (Series.natural k) (Dims.layout [k]) :=
    ((Adopt.skip (Series.natural k)).back).thenDo (Adopt.turn _ (hinge k []))
  ((Adopt.same _).split digit).thenDo (unite D [k])

def view (k : ℕ) (i : I) : Adopt
    (BatchRows.layout (outer P) (tail (b:=b) ord G B f) k i) (rows (b:=b) ord P G B f k i) :=
  (prefixView (P i) k).split (Adopt.same _)

/-- Select the original prefix and genuine leading digit for a padded row record. -/
def padded {W : ℕ} (hb : 0 < b) (v : Value (J:=J) (b:=b) P G B f b) (u : Fin W) :
    Value (J:=J) (b:=b) P G B f (BatchRows.groups b W) := fun i a =>
  let x := (prefixView (P i) (BatchRows.groups b W)).cast.symm a.1
  v i ((prefixView (P i) b).cast (x.1, BatchRows.select hb u x.2), a.2)

/-- For each native output address, fetch its unique genuine row and group. -/
def gather {W : ℕ} (hW : 0 < W)
    (v : Fin W → Value (J:=J) (b:=b) P G B f (BatchRows.groups b W)) :
    Value (J:=J) (b:=b) P G B f b := fun i a =>
  let x := (prefixView (P i) b).cast.symm a.1
  v (BatchRows.row hW x.2) i
    ((prefixView (P i) (BatchRows.groups b W)).cast (x.1, BatchRows.group hW x.2), a.2)

@[simp] theorem gather_padded {W : ℕ} (hb : 0 < b) (hW : 0 < W)
    (v : Value (J:=J) (b:=b) P G B f b) :
    gather P G B f hW (padded (W:=W) P G B f hb v) = v := by
  funext i a
  simp [gather,padded]

/-- An arbitrary change of both central wing vectors, fixing prefix, gap and suffix. -/
def change (F : (i : I) → ((J → Block b (f i)) × (J → Block b (f i))) →
    ((J → Block b (f i)) × (J → Block b (f i)))) {k : ℕ}
    (v : Value (J:=J) (b:=b) P G B f k) : Value (J:=J) (b:=b) P G B f k := fun i a =>
  let z := F i (a.2.1, a.2.2.2.1)
  v i (a.1,z.1,a.2.2.1,z.2,a.2.2.2.2)

theorem gather_change {W : ℕ} (hb : 0 < b) (hW : 0 < W)
    (F : (i : I) → ((J → Block b (f i)) × (J → Block b (f i))) →
      ((J → Block b (f i)) × (J → Block b (f i)))) (v : Value (J:=J) (b:=b) P G B f b) :
    gather P G B f hW (fun u => change P G B f F (padded P G B f hb v u)) =
      change P G B f F v := by
  funext i a
  simp [gather,change,padded]

theorem padded_manifest {W : ℕ} (hb : 0 < b) (v : Value (J:=J) (b:=b) P G B f b)
    {l : I → ℕ} (hv : Manifest _ l v) (u : Fin W) : Manifest _ l (padded P G B f hb v u) :=
  hv.shift _

variable {r : Regime I} {l : I → ℕ} {input : I → Tree}

/-- Packing into fewer rows than leading digit values preserves the permitted
range of a spectator dimension. -/
theorem groups_bounds {W b : ℕ} (hW : 0 < W) (hb : W < b) :
    2 ≤ BatchRows.groups b W ∧ BatchRows.groups b W ≤ b := by
  refine ⟨?_, (ceilDiv_le_iff_le_mul hW).mpr (Nat.le_mul_of_pos_left _ hW)⟩
  have h := BatchRows.le_groups_volume (b:=b) hW
  by_contra! h'
  have := (Nat.mul_le_mul_left W (show BatchRows.groups b W ≤ 1 by omega)).trans_eq (Nat.mul_one W)
  omega

/-- The quotient spectator is a valid P192 tape dimension including when the
radix is just one greater than the number of independent rows. -/
theorem told_front {W : ℕ} (hW : 0 < W) (hb : W < b) (hp : Told r P) :
    Told r (front P (BatchRows.groups b W)) := by
  apply hp.append
  exact ⟨fun _ => by simpa [solid] using (groups_bounds hW hb).1, Regime.fixed _⟩

private theorem station_tail (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hg : Told r G) (hs : Told r B) :
    Station r (tail (b:=b) ord G B f) := by
  have hd := (Told.carrier hb f hf).stacked n
  have base : Station r (fun i => threads (line b (f i)) ord) := by
    have e (i : I) : (threads (line b (f i)) ord).count =
        (Dims.layout (Rack (field b (f i)) n)).count :=
      (undye (line b (f i)) ord (Adopt.same _)).cost
    unfold Station
    simp_rw [e]
    exact hd.station
  exact base.product (hg.station.product (base.product hs.station))

private theorem cells_le (hb : 0 < b) (i : I) : (outer P i).count * (tail (b:=b) ord G B f i).count ≤
    (rows (b:=b) ord P G B f b i).count := by
  rw [← (view (b:=b) ord P G B f b i).cost]
  simp only [BatchRows.layout, Series.count_cart, Series.count_natural]
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hb)

/-- Splitting directly from a native center stream into native stage rows. -/
theorem split {W : ℕ} (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (v : Value (J:=J) (b:=b) P G B f b)
    (header : Rip r (fun i => (rows (b:=b) ord P G B f b i).count) l input r.header)
    (source : Rip r (fun i => (rows (b:=b) ord P G B f b i).count) l input
      (stackRun (rows (b:=b) ord P G B f b) v)) :
    Rip r (fun i => (rows (b:=b) ord P G B f b i).count) l input (fun i =>
      stripe (Series.natural W) fun u => stripe (rows (b:=b) ord P G B f (BatchRows.groups b W) i)
        (padded P G B f (by omega) v u i)) := by
  let vf i := v i ∘ (view (b:=b) ord P G B f b i).cast
  have src : (stackRun (rows (b:=b) ord P G B f b) v) = stackRun
      (BatchRows.layout (outer P) (tail (b:=b) ord G B f) b) vf :=
    funext fun i => (view (b:=b) ord P G B f b i).packet _
  rw [src] at source
  have raw := BatchRows.split_rip (W:=W) (outer P) (tail (b:=b) ord G B f)
    (by omega : 0 < b) hp.station (station_tail ord G B f hb hf hg hs)
    (cells_le ord P G B f (by omega)) header vf source
  convert raw using 1
  funext i
  apply congrArg (stripe (Series.natural W)); funext u
  rw [(view (b:=b) ord P G B f (BatchRows.groups b W) i).packet]
  apply congrArg (stripe _); funext a
  change v i ((prefixView _ b).cast (_, _),_) = v i ((prefixView _ b).cast (_,_),_)
  simp [view, Adopt.split, Equiv.prodCongr_apply]

/-- Merge arbitrary processed native stage rows, at the original node's charge. -/
theorem merge {W : ℕ} (hW : 0 < W) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (v : Fin W → Value (J:=J) (b:=b) P G B f (BatchRows.groups b W))
    (header : Rip r (fun i => (rows (b:=b) ord P G B f b i).count) l input r.header)
    (source : Rip r (fun i => (rows (b:=b) ord P G B f b i).count) l input (fun i =>
      stripe (Series.natural W) fun u => stripe (rows (b:=b) ord P G B f (BatchRows.groups b W) i)
        (v u i))) :
    Rip r (fun i => (rows (b:=b) ord P G B f b i).count) l input
      (stackRun (rows (b:=b) ord P G B f b) (gather P G B f hW v)) := by
  let q := BatchRows.groups b W
  let vf (u : Fin W) (i : I) := v u i ∘ (view (b:=b) ord P G B f q i).cast
  have src (i : I) : (fun u => stripe (rows (b:=b) ord P G B f q i) (v u i)) =
       fun u => stripe (BatchRows.layout (outer P) (tail (b:=b) ord G B f) q i) (vf u i) :=
    funext fun u => (view (b:=b) ord P G B f q i).packet (v u i)
  have nr := (funext fun i => congrArg (stripe (Series.natural W)) (src i)) ▸ source
  have raw := BatchRows.merge_rip (b:=b) (outer P) (tail (b:=b) ord G B f) hW
    hp.station (station_tail ord G B f hb hf hg hs) (cells_le ord P G B f (by omega)) header vf nr
  convert raw using 1
  funext i
  rw [stackRun, (view (b:=b) ord P G B f b i).packet]
  apply congrArg (stripe _); funext a
  rcases a with ⟨⟨p,d⟩,z⟩
  simp [Function.comp_apply, gather, view, Adopt.split, BatchRows.gather, vf, q]

/-- The same domain cardinality used by the native recursive calls satisfies
the required shrinkage, for any number of spectator prefixes. -/
theorem row_volume {W : ℕ} (hW : 0 < W) (hWb : W ≤ b) (i : I) :
    W * (rows (b:=b) ord P G B f (BatchRows.groups b W) i).count ≤
      2 * (rows (b:=b) ord P G B f b i).count := by
  rw [← (view (b:=b) ord P G B f (BatchRows.groups b W) i).cost,
    ← (view (b:=b) ord P G B f b i).cost]
  exact BatchRows.row_layout_volume _ _ hW hWb i

/-- Exact rational volume ratio for every individual native row, including
its padded final group and all spectator coordinates. -/
theorem row_volume_exact (W : ℕ) (i : I) :
    b * (rows (b:=b) ord P G B f (BatchRows.groups b W) i).count =
      BatchRows.groups b W * (rows (b:=b) ord P G B f b i).count := by
  rw [← (view (b:=b) ord P G B f (BatchRows.groups b W) i).cost,
    ← (view (b:=b) ord P G B f b i).cost]
  simp only [BatchRows.layout, Series.count_cart, Series.count_natural]
  ac_rfl

/-- Bank at the native geometry used by the stage. -/
abbrev packet {W : ℕ} (v : Fin W → Value (J:=J) (b:=b) P G B f (BatchRows.groups b W)) :=
  fun i => stripe (Series.natural W) fun u => stripe (rows (b:=b) ord P G B f (BatchRows.groups b W) i)
    (v u i)

private theorem enlarge_count {X : Type} {job : Job X} {zone : I → X → Prop} {k : ℤ}
    {src dst : I → Tree} {N N' : I → ℕ} (h : ∀ i, N i ≤ N' i)
    (v : Hopto job r N l zone k src dst) : Hopto job r N' l zone k src dst := by
  obtain ⟨uses,safe,calls,⟨c,run⟩⟩ := v.safe
  refine ⟨uses,safe,calls,c,fun e => IntegerMultiplication.Loom.Tunnel.monoT (run e) (fun i => ?_)⟩
  unfold mass
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h i) (by positivity)

/-- Enclose a native charged bank computation between the physical splitter
and merger. Its charged calls and child predicate are preserved. The parent
header remains available on return. -/
theorem with_rows {W : ℕ} (hW : 0 < W) (hb : W < b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) {X : Type}
    {job : Job X} {zone : I → X → Prop} {calls : ℤ}
    (F : (i : I) → ((J → Block b (f i)) × (J → Block b (f i))) →
      ((J → Block b (f i)) × (J → Block b (f i))))
    (v : Value (J:=J) (b:=b) P G B f b) (hv : Manifest _ l v)
    (run : Hopto job r (fun i => (rows (b:=b) ord P G B f (BatchRows.groups b W) i).count) l
      zone calls (together r.header (packet (W:=W) ord P G B f (padded P G B f (by omega) v)))
      (packet (W:=W) ord P G B f (fun u => change P G B f F (padded P G B f (by omega) v u)))) :
    Hopto job r (fun i => (rows (b:=b) ord P G B f b i).count) l zone calls
      (together r.header (stackRun (rows (b:=b) ord P G B f b) v))
      (stackRun (rows (b:=b) ord P G B f b) (change P G B f F v)) := by
  let q := BatchRows.groups b W
  let parent i := (rows (b:=b) ord P G B f b i).count
  let child i := (rows (b:=b) ord P G B f q i).count
  let pin := padded (W:=W) P G B f (show 0 < b by omega) v
  let pout (u : Fin W) := change P G B f F (pin u)
  have hb' : 2 ≤ b := by omega
  have parentP : Told r (front P b) := hp.append (Told.carrier hb' (fun _ => 1) (Regime.fixed _))
  have pst := layoutRows_station (b:=b) ord (front P b) G B f hb' hf parentP hg hs
  have cst := layoutRows_station (b:=b) ord (front P q) G B f hb' hf (told_front P hW hb hp) hg hs
  have qle : q ≤ b := (groups_bounds hW hb).2
  have child_le (i : I) : child i ≤ parent i := by
    dsimp only [child,parent]
    rw [← (view (b:=b) ord P G B f q i).cost, ← (view (b:=b) ord P G B f b i).cost]
    simp only [BatchRows.layout, Series.count_cart, Series.count_natural]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ qle)
  have parentA := hv.lives pst
  have header := Drive.fetch pst.1 parentA
  have before := split (W:=W) ord P G B f hb' hf hp hg hs v header (Drive.self pst.1 parentA)
  have external := ((enlarge_count child_le run).pack r.header).preceded ((header.twice before).twice header)
  have rowA (u : Fin W) : Alive r parent l (stackRun (rows (b:=b) ord P G B f q) (pout u)) := by
    have live : Manifest _ l (pout u) := (padded_manifest P G B f (by omega) v hv u).shift _
    exact (live.lives cst).monoSize child_le (fun _ => le_rfl)
  have bankA : Alive r parent l (packet (W:=W) ord P G B f pout) := Fatigue.entire (Series.natural W)
    (fun i u => stripe (rows (b:=b) ord P G B f q i) (pout u i)) pst.1 rowA
  have back := Rip.split (Rip.alivePair bankA (Drive.started (l:=l) pst.1))
  have merged := merge ord P G B f hW hb' hf hp hg hs pout back.2 back.1
  have ret := external.afterTask merged
  rw [show gather P G B f hW pout = change P G B f F v from gather_change P G B f _ hW F v] at ret
  exact ret

/-- Simultaneous swap of both complete families, as required by the centered
recursive call in `InterchangeFrame.axis`. -/
theorem with_rows_swap {W : ℕ} (hW : 0 < W) (hb : W < b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) {X : Type}
    {job : Job X} {zone : I → X → Prop} {calls : ℤ}
    (v : Value (J:=J) (b:=b) P G B f b) (hv : Manifest _ l v)
    (run : Hopto job r (fun i => (rows (b:=b) ord P G B f (BatchRows.groups b W) i).count) l
      zone calls (together r.header (packet (W:=W) ord P G B f (padded P G B f (by omega) v)))
      (packet (W:=W) ord P G B f (fun u i => padded P G B f (by omega) v u i ∘ swapper _ _ _))) :
    Hopto job r (fun i => (rows (b:=b) ord P G B f b i).count) l zone calls
      (together r.header (stackRun (rows (b:=b) ord P G B f b) v))
      (stackRun (rows (b:=b) ord P G B f b) (fun i => v i ∘ swapper _ _ _)) :=
  with_rows ord P G B f hW hb hf hp hg hs (fun _ => Prod.swap) v hv run

end BatchFrame

end NearSquareRoot
end Computability
end OAI
