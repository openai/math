import OAI.Computability.NearSquareRoot.InterchangeOuterReserves
import OAI.Computability.NearSquareRoot.InterchangeBQuestPack

/-! # Bounded execution of the smaller-row phase

The physical split and merge have no recursive calls. The padded bank invokes
the smaller-row program while its continuation keeps the parent descriptor.
The bank's recursive list and its child predicates survive both operations.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BatchFrame

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress
  NearSquareRoot.InterchangeSpace

variable {I J : Type} {n b : ℕ} (ord : J ≃ Fin n) (P G B : I → Tape) (f : I → ℕ)
  {r : Regime I} {l : I → ℕ}

private theorem enlarge_bounded {Y : Type} {job : Job Y} {zone : I → Y → Prop}
    {limit : ℤ} {N M : I → ℕ} {input output : I → Tree}
    (le : ∀ i, N i ≤ M i) (h : BHop job r N l zone limit input output) :
    BHop job r M l zone limit input output := by
  obtain ⟨uses, valid, cost, ⟨k,body⟩⟩ := h.safe
  exact ⟨uses, valid, cost, ⟨k, body.mono (fun i => Nat.mul_le_mul_right _ (le i))⟩⟩

/-- All local work and all parked bank cells are included in the bounded
command certificate, with the original recursive list and target range. -/
theorem bounded_with_rows {W : ℕ} (hW : 0 < W) (hb : W < b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) {X : Type}
    {job : Job X} {zone : I → X → Prop} {calls : ℤ}
    (F : (i : I) → ((J → Block b (f i)) × (J → Block b (f i))) →
      ((J → Block b (f i)) × (J → Block b (f i))))
    (v : Value (J:=J) (b:=b) P G B f b) (hv : Manifest _ l v)
    (run : BHop job r (fun i => (rows (b:=b) ord P G B f (BatchRows.groups b W) i).count) l
      zone calls (together r.header (packet (W:=W) ord P G B f (padded P G B f (by omega) v)))
      (packet (W:=W) ord P G B f (fun u => change P G B f F (padded P G B f (by omega) v u)))) :
    BHop job r (fun i => (rows (b:=b) ord P G B f b i).count) l zone calls
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
  have external := ((enlarge_bounded child_le run).pack r.header (Drive.started pst.1)).preceded ((header.twice before).twice header)
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

end BatchFrame

namespace OuterReserves

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  NearSquareRoot.InterchangeSpace

/-- Apply the physical row splitter and merger around the batched main swap.
The rank and cardinality of the reserve strips do not change the row map. -/
theorem bounded_with_rows_main {I : Type} {r : Regime I} {b W : ℕ} {l : I → ℕ}
    (a m : ℕ) (P G B : I → Dims.Tape) (f : I → ℕ) (hW : 0 < W) (hb : W < b)
    (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    {X : Type} {job : Job X} {zone : I → X → Prop} {calls : ℤ}
    (v : BatchFrame.Value (J:=Slots a m) (b:=b) P G B f b) (hv : Manifest _ l v)
    (run : BHop job r (fun i =>
      (BatchFrame.rows (b:=b) (Equiv.refl (Slots a m)) P G B f (BatchRows.groups b W) i).count) l
      zone calls (together r.header (BatchFrame.packet (W:=W) (Equiv.refl _) P G B f
        (BatchFrame.padded P G B f (by omega) v)))
      (BatchFrame.packet (W:=W) (Equiv.refl _) P G B f (fun u i =>
        BatchFrame.padded P G B f (by omega) v u i ∘ InterchangeSpectralFibre.swapMain (main a m)))) :
    BHop job r (fun i => (BatchFrame.rows (b:=b) (Equiv.refl (Slots a m)) P G B f b i).count) l
      zone calls (together r.header (stackRun (BatchFrame.rows (Equiv.refl _) P G B f b) v))
      (stackRun (BatchFrame.rows (Equiv.refl _) P G B f b)
        (fun i => v i ∘ InterchangeSpectralFibre.swapMain (main a m))) := by
  classical
  let F (i : I) (x : (Slots a m → Block b (f i)) × (Slots a m → Block b (f i))) :=
    (fun j => if j ∈ Set.range (main a m) then x.2 j else x.1 j,
     fun j => if j ∈ Set.range (main a m) then x.1 j else x.2 j)
  exact BatchFrame.bounded_with_rows (Equiv.refl _) P G B f hW hb hf hp hg hs F v hv run

end OuterReserves

end NearSquareRoot
end Computability
end OAI
