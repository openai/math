import OAI.Computability.IntegerMultiplication.Loom.Canal
import OAI.Computability.IntegerMultiplication.Strip.Narrow

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Fleet
variable {I K : Type} {A S : I→Type} (s : Series K) {t : (i:I)→Series (A i)}
variable {u : (i:I)→Series (S i)} {l : I→ℕ} {r : Regime I}
variable (k : Station r (fun _ : I => s)) (m : Station r t)
private theorem counts (u : (i:I)→Series (S i)) :
    (fun i => ((s.cart (t i)).cart (u i)).count)=(fun i => (((t i).cart s).cart (u i)).count) := by
  simp [Nat.mul_comm]
include k m
-- unmasked movement primitive in a fat stream
theorem settle (B : Station r u)
    (x : (i:I) → K × A i × S i → Tree) (d : Manifest _ l x) :
    Fleet r l (cartS (fun _ => s) (cartS t u)) (cartS t (cartS (fun _ => s) u))
      x (fun i a => x i (a.2.1,a.1,a.2.2)) := by
  let z i := s.cart (t i)
  let g i := (t i).cart s
  let src i := (z i).cart (u i)
  let dst i := (g i).cart (u i)
  apply Fleet.access (s:=src) (d:=dst) _ _ (fun i=>Adopt.rotate s (t i) (u i))
    (fun i=>Adopt.rotate (t i) s (u i))
  let N i := (src i).count
  let v (i : I) (a : (K × A i) × S i) := x i (a.1.1,a.1.2,a.2)
  let w (i : I) (a : A i × K) := stripe (u i) (fun b => v i ((a.2,a.1),b))
  let i0 := stackRun src v
  have g0 := k.product m
  have hk := g0.product B
  let v0 := (d.shift (fun i (a : (K×A i)×S i) => (a.1.1,a.1.2,a.2))).lives hk
  change Alive r N l i0 at v0
  have h' := Drive.fetch hk.1 v0
  have h := Drive.self hk.1 v0
  have gz i : (z i).count≤N i := by rw [show N i=(z i).count*(u i).count from Series.count_cart ..]; exact Nat.le_mul_of_pos_right _ (B.1 i)
  have gt i : (t i).count≤N i := (show _ ≤ (z i).count from (Series.count_cart ..).symm ▸
    Nat.le_mul_of_pos_left _ (k.1 i)).trans (gz i)
  have gu i : (u i).count≤N i := by rw [show N i=(z i).count*(u i).count from Series.count_cart ..]; exact Nat.le_mul_of_pos_left _ (g0.1 i)
  have f := Rip.carve z u v (h'.chain ((Station.supply g0 gz).twice (Station.supply B gu))) h g0.1 B.1 (fun i => by rw [← Series.count_cart])
  apply Rip.flatten g u (fun i a => v i ((a.1.2,a.1.1),a.2))
  have c := h'.chain (Station.supply m gt)
  obtain ⟨a,ok⟩ := f
  obtain ⟨b,ox⟩ := c
  exact ⟨a+b,IntegerMultiplication.Strip.sink s t _ (ok.larger (mass_le (by omega : a≤a+b))) (ox.larger (mass_le (by omega : b≤a+b)))⟩

theorem reascend (B : Station r u)
    (x : (i:I)→A i × K × S i → Tree) (d : Manifest _ l x) :
    Fleet r l (cartS t (cartS (fun _ => s) u)) (cartS (fun _ => s) (cartS t u))
      x (fun i a => x i (a.2.1,a.1,a.2.2)) := by
  let z i := (t i).cart s
  let g i := s.cart (t i)
  let src i := (z i).cart (u i)
  let dst i := (g i).cart (u i)
  apply Fleet.access (s:=src) (d:=dst) _ _ (fun i => Adopt.rotate (t i) s (u i))
    (fun i => Adopt.rotate s (t i) (u i))
  let N i := (src i).count
  let v (i : I) (a : (A i × K) × S i) := x i (a.1.1,a.1.2,a.2)
  let i0 := stackRun src v
  have g0 := m.product k
  have hk := g0.product B
  let v0 := (d.shift (fun i (a : (A i×K)×S i) => (a.1.1,a.1.2,a.2))).lives hk
  change Alive r N l i0 at v0
  have h' := Drive.fetch hk.1 v0
  have h := Drive.self hk.1 v0
  have gz i : (z i).count≤N i := by rw [show N i=(z i).count*(u i).count from Series.count_cart ..]; exact Nat.le_mul_of_pos_right _ (B.1 i)
  have gt i : (t i).count≤N i := (show _ ≤ (z i).count from (Series.count_cart ..).symm ▸
    Nat.le_mul_of_pos_right _ (k.1 i)).trans (gz i)
  have gu i : (u i).count≤N i := by rw [show N i=(z i).count*(u i).count from Series.count_cart ..]; exact Nat.le_mul_of_pos_left _ (g0.1 i)
  have f := Rip.carve z u v (h'.chain ((Station.supply g0 gz).twice (Station.supply B gu))) h g0.1 B.1 (fun i => by rw [← Series.count_cart])
  apply Rip.flatten g u (fun i a => v i ((a.1.2,a.1.1),a.2))
  have c := h'.chain (Station.supply m gt)
  obtain ⟨a,ok⟩ := f
  obtain ⟨b,ox⟩ := c
  exact ⟨a+b,bubble s t _ (ok.larger (mass_le (by omega : a≤a+b))) (ox.larger (mass_le (by omega : b≤a+b)))⟩

theorem beacon_change (B : Station r u)
    (x : (i:I)→K × A i × K × S i→Tree) (h : Manifest _ l x) :
    Fleet r l (cartS (fun _=>s) (cartS t (cartS (fun _=>s) u)))
      (cartS (fun _=>s) (cartS t (cartS (fun _=>s) u))) x
      (fun i a => x i (a.2.2.1,a.2.1,a.1,a.2.2.2)) := by
  have f := settle s k m (k.product B) x h
  let y := fun (i:I) (a : A i × K × K × S i) => x i (a.2.1,a.1,a.2.2)
  have h0 := h.shift (fun i (a : A i × K × K × S i) => (a.2.1,a.1,a.2.2))
  let T := Sigma A
  have b := settle s (k.pull (Sigma.fst:T→I)) (k.pull (Sigma.fst:T→I)) (B.pull (Sigma.fst:T→I))
    (fun (i:T) t => y i.1 (i.2,t)) (Manifest.localize (s:=fun i r z => y i (r,z)) h0)
  have b0 : Fleet r l (cartS t (cartS (fun _=>s) (cartS (fun _=>s) u)))
      (cartS t (cartS (fun _=>s) (cartS (fun _=>s) u))) y
      (fun i a => x i (a.2.2.1,a.1,a.2.1,a.2.2.2)) :=
    Fleet.wind m (k.product (k.product B)) h0 b
  have z := reascend s k m (k.product B) _
      (h.shift (fun i (a : A i × K × K × S i) => (a.2.2.1,a.1,a.2.1,a.2.2.2)))
  exact f.chain (b0.chain z (fun _ => rfl)) (by simp [Fleet.cartS]; intro i; ring)

end Strip
namespace Loom
open Strip Dims Code Adic
noncomputable section
variable {I W : Type} [Fintype W] (D p : ℕ) [NeZero p] (R : Series W)
variable (v : I → Boll D p W 0) {r : Regime I}
omit [NeZero p] in
theorem primeval (a : 2≤p) (h : r.header = fun i => (v i).site.ticket) :
    let t (i:I) : Where D p W := ⟨0,v i⟩
    Rip r (fun i => (t i).plates.count) (fun i => timeNow (t i))
      (together r.header (stackRun (fun i => (t i).plates) (fun i z => (t i).cap R z)))
      ((Where.current R).reply ∘ t) := by
  dsimp only
  let t (i:I) : Where D p W := ⟨0,v i⟩
  have y : r.Small (fun i => (t i).site.ticket) := h ▸ Regime.self
  obtain ⟨q,c,d⟩ := Where.ticket_told (D:=D) (fun _ => 0) (fun i => (v i).site) y
  let P i := Pin (t i).site.north
  let T := Sigma P
  let K := line p (D^0)
  have z : Station r (fun _=>K) := terminal a _ (Regime.fixed _)
  have m := visible (l:=fun i => timeNow (t i))
    (fun i => skein W R (t i).2.cargo (t i).1) (fun i => (t i).2.option)
      (fun i => by rw [strands]; exact le_rfl)
  have x := beacon_change K (z.pull (Sigma.fst:T→I)) (c.station.pull (Sigma.fst:T→I))
    (d.station.pull (Sigma.fst:T→I)) (fun (i:T) x => (t i.1).cap R (i.2,x))
    (Manifest.localize (s:=fun i w u => (t i).cap R (w,u)) m)
  exact Fleet.wind (q.station) (z.product (c.station.product (z.product d.station))) m x
end
end Loom

end IntegerMultiplication
end Computability
end OAI
