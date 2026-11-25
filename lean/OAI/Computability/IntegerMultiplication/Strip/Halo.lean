import OAI.Computability.IntegerMultiplication.Strip.Mask

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Loom
variable {I : Type} {S T K : I→Type} (s : (i:I)→Series (S i)) (t : (i:I)→Series (T i))
variable (C : ℕ) (e : ∀ i,Gap (s i) (t i) C)
variable {r : Regime I} {n l : I→ℕ}
noncomputable section

theorem beam (v : (i:I)→S i→Tree) {p : I→Tree}
    (h : Rip r n l p (stackRun s v)) (w : Rip r n l p (fun i => send (tally (t i).count))) :
    Rip r n l p (stackRun t (fun i => v i ∘ expand (s i) (t i) C (e i))) := by
  have hx := w.twice h
  unfold stackRun at hx ⊢
  simp_rw [stripe_eq] at *
  have y := Fatigue.act (x:=fun i => (tally (t i).count, (s i).tab (v i))) hx
    _ (easy_cloud (A:=Tree) C)
  simpa only [tally_length,material] using y
theorem skim (v : (i:I)→T i→Tree) {p : I→Tree}
    (h : Rip r n l p (stackRun t v)) (w : Rip r n l p (fun i => send (tally (s i).count))) :
    Rip r n l p (stackRun s (fun i => v i ∘ intro_ (s i) (t i) C (e i))) := by
  have hx := w.twice h
  unfold stackRun at hx ⊢
  simp_rw [stripe_eq] at *
  have y := Fatigue.act (x:=fun i => (tally (s i).count, (t i).tab (v i))) hx
    _ ((easy_cut (easy_id (X:=Tally×List Tree))).fstCompose)
  simpa only [cede,cutLists,tally_length] using y

theorem Rip.factor {v w : I→Tree} (h : Rip r n l v w) {m : I→ℕ}
    (u : ∀ i,1≤ m i) (c : ℕ) (z : ∀ i,n i ≤ c*m i) : Rip r m l v w := by
  obtain ⟨k,b⟩ := h
  refine ⟨k,b.times (unit_mass u _) c (fun i => ?_)⟩
  unfold mass; rw [← mul_assoc]
  gcongr; exact_mod_cast z i
theorem Breeze.factor {v w : I→Tree} {x : I→ℝ} (h : Breeze x r n l v w)
    {m : I→ℕ} (u : ∀ i,1≤ m i) (c : ℕ) (z : ∀ i,n i ≤ c*m i) : Breeze x r m l v w := by
  obtain ⟨a,k,b⟩ := h
  refine ⟨a,k,b.times (fun i => one_le_mul_of_one_le_of_one_le (unit_mass u _ _) (a _)) c (fun i => ?_)⟩
  unfold runrate mass; rw [← mul_assoc,← mul_assoc]
  have t := a i
  gcongr; exact_mod_cast z i

open Fleet

-- arbitrary suffix on operations
private theorem teal (u : (i:I)→Series (K i)) (v : (i:I)→S i × K i→Tree)
    (sw : (i:I)→T i→S i) (x : Station r s) (z : Station r u)
    (h : Manifest _ l v)
    (run : let v0 := stackRun s (fun i a => stripe (u i) (fun b => v i (a,b)))
      let y0 := stackRun t (fun i a => stripe (u i) (fun b => v i (sw i a,b)))
      Alive r (fun i => (s i).count*(u i).count) l v0 →
        Drive r (fun i => (s i).count*(u i).count) l v0 y0) :
    Fleet r l (cartS s u) (cartS t u) v (fun i a => v i (sw i a.1,a.2)) := by
  have B := (x.product z)
  have hx := h.lives B
  have n i : (cartS s u i).count=(s i).count*(u i).count := Series.count_cart ..
  simp_rw [n] at hx
  let N i := (s i).count*(u i).count
  have N0 (i) : 1≤N i := Nat.mul_pos (x.1 i) (z.1 i)
  have t₁ := Drive.fetch N0 hx
  have t₂ := Drive.self N0 hx
  have hs := t₁.chain ((Station.supply x (fun i => Nat.le_mul_of_pos_right _ (z.1 i))).twice
    (Station.supply z (fun i => Nat.le_mul_of_pos_left _ (x.1 i))))
  have m := Rip.carve _ _ v hs t₂ x.1 z.1 (fun _ => le_rfl)
  have f := Drive.pipe m (run m.idle)
  unfold Fleet
  simp_rw [n]
  exact Rip.flatten _ _ (fun i a => v i (sw i a.1,a.2)) f

theorem band (u : (i:I)→Series (K i))
    (a : Station r s) (b : Station r t) (x : Station r u)
    (v : (i:I)→S i × K i→Tree) (h : Manifest _ l v) :
    Fleet r l (cartS s u) (cartS t u) v (fun i a => v i (expand (s i) (t i) C (e i) a.1,a.2)) := by
  apply teal s t u v _ a x h
  dsimp only; intro hz
  let N i := (s i).count * (u i).count
  have N0 i : 1≤N i := Nat.mul_pos (a.1 i) (x.1 i)
  have hf := Drive.fetch N0 hz
  apply beam s t C e _ (Drive.self N0 hz)
  refine hf.chain (Rip.factor (m:=N) (Station.supply (l:=l) b (fun _=>le_rfl)) N0 C ?_)
  intro i
  have q : (s i).count*C≤C*N i := by
    rw [mul_comm]
    apply Nat.mul_le_mul_left _
    exact Nat.le_mul_of_pos_right _ (x.1 i)
  exact (e i).maxfold.trans q

theorem subband (u : (i:I)→Series (K i))
    (a : Station r s) (b : Station r t) (x : Station r u)
    (v : (i:I)→T i × K i→Tree) (h : Manifest _ l v) :
    Fleet r l (cartS t u) (cartS s u) v (fun i a => v i (intro_ (s i) (t i) C (e i) a.1,a.2)) := by
  apply teal t s u v _ b x h
  dsimp only; intro hz
  let N i := (t i).count * (u i).count
  have N0 i : 1≤N i := Nat.mul_pos (b.1 i) (x.1 i)
  have hf := Drive.fetch N0 hz
  apply skim s t C e _ (Drive.self N0 hz)
  exact hf.chain (Station.supply a (fun i => (e i).fit.trans (Nat.le_mul_of_pos_right _ (x.1 i))))

variable {Y : I→Type} (j : (i:I)→Series (Y i)) (u : (i:I)→Series (K i))
-- Putting in also a left axis. arbitrary layout. note shrinking with count changes handled later
theorem band_plus (a : Station r s) (b : Station r t) (y : Station r j) (x : Station r u)
    (v : (i:I)→Y i × S i × K i→Tree) (h : Manifest _ l v) :
    Fleet r l (cartS j (cartS s u)) (cartS j (cartS t u)) v
      (fun i a => v i (a.1,expand (s i) (t i) C (e i) a.2.1,a.2.2)) :=
  Fleet.wind y (a.product x) h (band (fun i:Sigma Y => s i.1) (fun i=>t i.1) C (fun i => e i.1)
    (fun i=>u i.1) (a.pull Sigma.fst) (b.pull Sigma.fst) (x.pull Sigma.fst)
      (fun i:Sigma Y => fun k => v i.1 (i.2,k)) (Manifest.localize (s:=fun i t k => v i (t,k)) h))

theorem subband_plus (a : Station r s) (b : Station r t) (y : Station r j) (x : Station r u)
    (v : (i:I)→Y i × T i × K i→Tree) (h : Manifest _ l v) :
    Fleet r l (cartS j (cartS t u)) (cartS j (cartS s u)) v
      (fun i a => v i (a.1,intro_ (s i) (t i) C (e i) a.2.1,a.2.2)) :=
  Fleet.wind y (b.product x) h (subband (fun i:Sigma Y => s i.1) (fun i=>t i.1) C (fun i => e i.1)
    (fun i=>u i.1) (a.pull Sigma.fst) (b.pull Sigma.fst) (x.pull Sigma.fst)
      (fun i:Sigma Y => fun k => v i.1 (i.2,k)) (Manifest.localize (s:=fun i t k => v i (t,k)) h))
end
end Strip

end IntegerMultiplication
end Computability
end OAI
