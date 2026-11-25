import OAI.Computability.IntegerMultiplication.Strip.Halo

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Dims Fleet Loom
variable {I : Type} {S T : I→Type}
variable (s : (i:I)→Series (S i)) (t : (i:I)→Series (T i))
variable (C : ℕ) (e : ∀ i,Gap (s i) (t i) C)
variable (P G B : I→Tape)
variable {l : I→ℕ} {r : Regime I}
variable (hs : Station r s) (ht : Station r t)
variable (x : Station r (fun i => layout (P i))) (y : Station r (fun i => layout (G i))) (z : Station r (fun i => layout (B i)))
noncomputable section

abbrev star_ := fun i => Path (P i) (s i) (G i) (s i) (B i)
def fill_ i (a : SpanKey (P i) (G i) (B i) (T i)) : SpanKey (P i) (G i) (B i) (S i) :=
  (a.1,expand (s i) (t i) C (e i) a.2.1,a.2.2.1,expand (s i) (t i) C (e i) a.2.2.2.1,a.2.2.2.2)
def thicken i (a : SpanKey (P i) (G i) (B i) (S i)) : SpanKey (P i) (G i) (B i) (T i) :=
  (a.1,intro_ (s i) (t i) C (e i) a.2.1,a.2.2.1,intro_ (s i) (t i) C (e i) a.2.2.2.1,a.2.2.2.2)
theorem paid_ i v :
    fill_ s t C e P G B i (swapper _ _ _ (thicken s t C e P G B i v)) =
      swapper _ _ _ v := by simp [fill_,thicken,swapper]

-- Combine expansions conserving charges even though intermediary larger.
theorem Fleet.go {I} {S T V : I→Type} {S0 : (i:I)→Series (S i)}
    {D0 : (i:I)→Series (T i)} {V0 : (i:I)→Series (V i)}
    {r : Regime I} {l : I→ℕ} {x y z}
    (h : Fleet r l S0 D0 x y) (g : Fleet r l D0 V0 y z)
    (k : ℕ) (v : ∀ i,(D0 i).count≤k*(S0 i).count) (p : ∀ i,1≤(S0 i).count) :
    Fleet r l S0 V0 x z := Drive.pipe h (Rip.factor g p k v)

abbrev track_ (A : (i:I)→Series (S i)) (B : (i:I)→Series (T i)) :=
  cartS A B
include e
private theorem budgets i :
    (s i).count ≤ (t i).count ∧ (t i).count ≤ C*(s i).count :=
  ⟨(e i).fit, by simpa only [Nat.mul_comm C] using (e i).maxfold⟩

theorem all_counts i :
    (star_ t P G B i).count ≤ C^2*(star_ s P G B i).count := by
  simp only [star_,Loom.Path,Loom.Board,Series.count_cart]
  obtain ⟨_,b⟩ := budgets s t C e i
  calc
   _ ≤ (layout (P i)).count*(C*(s i).count*((layout (G i)).count*((C*(s i).count)*(layout (B i)).count))) := by
    gcongr
   _ = _ := by ring

include x y z hs ht
theorem addHalo (v : (i:I) → SpanKey (P i) (G i) (B i) (S i) → Tree) (h : Manifest _ l v) :
    Fleet r l (star_ s P G B) (star_ t P G B) v (fun i => v i ∘ fill_ s t C e P G B i) := by
  -- remove P. first inflate first, then second.
  let GG i := layout (G i)
  let BB i := layout (B i)
  let W := fun i => (Pin (P i))
  let SS := cartS s (cartS GG (cartS s BB))
  let f (i:Sigma W) a := v i.1 (i.2,a)
  let g (i:Sigma W) (a : T i.1 × Pin (G i.1) × S i.1 × Pin (B i.1)) :=
    f i (expand (s i.1) (t i.1) C (e i.1) a.1,a.2)
  let H := r.pull (Sigma.fst:Sigma W→I)
  let hs0 := hs.pull (Sigma.fst:Sigma W→I)
  let ht0 := ht.pull (Sigma.fst:Sigma W→I)
  let y0 := y.pull (Sigma.fst:Sigma W→I)
  let z0 := z.pull (Sigma.fst:Sigma W→I)
  have h0 := Manifest.localize (s:=fun i q b => v i (q,b)) h
  let K := fun i:Sigma W => T i.1
  have j := band _ _ C (fun i=>e i.1) _ hs0 ht0
    (y0.product (hs0.product z0)) f h0
  have hg : Manifest _ (fun i:Sigma W => l i.1) g := h0.shift (fun (i:Sigma W) (a : T i.1 × Pin (G i.1) × S i.1 × Pin (B i.1)) => (expand (s i.1) (t i.1) C (e i.1) a.1,a.2))
  have u := Fleet.wind (c:=fun i => (layout (G i.1)).cart ((t i.1).cart (layout (B i.1)))) (u:=fun (i:Sigma W) (a : T i.1 × Pin (G i.1) × T i.1 × Pin (B i.1)) => g i (a.1,a.2.1,expand (s i.1) (t i.1) C (e i.1) a.2.2.1,a.2.2.2)) ht0 (y0.product (hs0.product z0)) hg
    (band_plus _ _ C (fun i:Sigma K => e i.1.1) _ _
      (hs0.pull Sigma.fst) (ht0.pull Sigma.fst) (y0.pull Sigma.fst) (z0.pull Sigma.fst)
      (fun i:Sigma K => fun a => g i.1 (i.2,a)) (Manifest.localize (s:=fun i w a => g i (w,a)) hg))
  exact Fleet.wind x (hs.product (y.product (hs.product z))) h
    (Fleet.go j u C (fun i:Sigma W => by
      simp only [cartS, Series.count_cart,← Nat.mul_assoc]; gcongr; exact (budgets s t C e i.1).2)
      (hs0.product (y0.product (hs0.product z0))).1)

theorem subHalo (v : (i:I) → SpanKey (P i) (G i) (B i) (T i) → Tree) (h : Manifest _ l v) :
    Fleet r l (star_ t P G B) (star_ s P G B) v (fun i => v i ∘ thicken s t C e P G B i) := by
  let GG i := layout (G i)
  let BB i := layout (B i)
  let W := fun i => Pin (P i)
  let f (i:Sigma W) a := v i.1 (i.2,a)
  let g (i:Sigma W) (a : S i.1 × Pin (G i.1) × T i.1 × Pin (B i.1)) :=
    f i (intro_ (s i.1) (t i.1) C (e i.1) a.1,a.2)
  let H := r.pull (Sigma.fst:Sigma W→I)
  let hs0 := hs.pull (Sigma.fst:Sigma W→I)
  let ht0 := ht.pull (Sigma.fst:Sigma W→I)
  let y0 := y.pull (Sigma.fst:Sigma W→I)
  let z0 := z.pull (Sigma.fst:Sigma W→I)
  have h0 := Manifest.localize (s:=fun i q b => v i (q,b)) h
  let K := fun i:Sigma W => S i.1
  have j := subband _ _ C (fun i=>e i.1) _ hs0 ht0
    (y0.product (ht0.product z0)) f h0
  have hg : Manifest _ (fun i:Sigma W => l i.1) g := h0.shift (fun (i:Sigma W) (a : S i.1 × Pin (G i.1) × T i.1 × Pin (B i.1)) => (intro_ (s i.1) (t i.1) C (e i.1) a.1,a.2))
  have u := Fleet.wind (c:=fun i => (layout (G i.1)).cart ((s i.1).cart (layout (B i.1)))) (u:=fun (i:Sigma W) (a : S i.1 × Pin (G i.1) × S i.1 × Pin (B i.1)) => g i (a.1,a.2.1,intro_ (s i.1) (t i.1) C (e i.1) a.2.2.1,a.2.2.2)) hs0 (y0.product (ht0.product z0)) hg
    (subband_plus _ _ C (fun i:Sigma K => e i.1.1) _ _
      (hs0.pull Sigma.fst) (ht0.pull Sigma.fst) (y0.pull Sigma.fst) (z0.pull Sigma.fst)
      (fun i:Sigma K => fun a => g i.1 (i.2,a)) (Manifest.localize (s:=fun i w a => g i (w,a)) hg))
  exact Fleet.wind x (ht.product (y.product (ht.product z))) h
    (Fleet.go j u 1 (fun i:Sigma W => by
      simp only [cartS,Series.count_cart,Nat.one_mul]; gcongr; exact (budgets s t C e i.1).1)
      (ht0.product (y0.product (ht0.product z0))).1)
end
end Strip

namespace Spindle
open Strip Loom Code Dims Adic
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] {p : ℕ}
variable [NeZero p] {τ : ℝ} (R : Series W) (d : Design J W L p τ)
variable {n M : I→ℕ}
noncomputable section
private theorem magnify (h : 0<τ) (hf : τ≤1)
    (hx : ∀ i,n i ≤ M i+1) :
    ∀ i,modes (τ:=τ) n i ≤ 2*modes (τ:=τ) M i := by
  intro i
  dsimp [modes]
  have z : ((n i+1:ℕ):ℝ) ≤ 2*((M i+1:ℕ):ℝ) := by exact_mod_cast (show _ ≤ 2*(M i+1) by specialize hx i; omega)
  have e : (2:ℝ)^τ ≤ 2 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) hf).trans_eq (Real.rpow_one _)
  apply (Real.rpow_le_rpow (by positivity) z h.le).trans
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  gcongr

theorem Breeze.pipe {f r n l} {s t u : I→Tree}
    (A : Breeze f r n l (together r.header s) t) (B : Breeze f r n l (together r.header t) u)
    (h : Drive r n l s r.header) : Breeze f r n l (together r.header s) u :=
  ((Strip.Breeze.launch h A.1).pair A).next B

variable {r : Regime I} {j : I → ℕ} (P G B : I→Tape)
include d R
/-- Rectangular raw bit version (Bead codec exactly one atom, orientation notify). -/
theorem starFlow (h : 0<τ) (hf : τ≤1)
    (guard : ∀ i n,n∈P i ++ G i ++ B i → 2≤n ∧ n≤p)
    (S : r.Has (shape ∘ P)) (Y : r.Has (shape ∘ G)) (Z : r.Has (shape ∘ B))
    (J0 : r.Has (tally ∘ j)) (l : I→ℕ) (a : I→ℕ) (ha : ∀ i,a i≤l i)
    (v : (i:I) → SpanKey (P i) (G i) (B i) (Block 2 (j i)) → Fin (a i)→Bead) :
    Breeze (modes j (τ:=τ)) r (fun i => (stock 2 (P i) (G i) (B i) (j i)).count) l
      (together r.header (cloth (fun i => stock 2 (P i) (G i) (B i) (j i)) (fun i => Series.natural (a i)) v))
      (cloth (fun i => stock 2 (P i) (G i) (B i) (j i)) (fun i => Series.natural (a i)) (fun i => v i ∘ swapper _ _ _)) :=
 by
  let s i := line 2 (j i)
  let k i := (altitude p d.large (tally (j i))).length
  let t i := line p (k i)
  have g i := grows p d.large (Code.tally (j i))
  simp only [tally_length] at g
  let e (i:I) : Gap (s i) (t i) p :=
    ⟨by simpa only [s,t,lineSize] using (g i).1, by
       rw [show (t i).count=p^k i from lineSize ..,lineSize] -- use comm
       exact (g i).2.1.trans (Nat.mul_comm ..).le, by have := d.large; omega⟩
  have q : r.Has (tally ∘ k) := by
    simpa only [Function.comp_def,k,recover_tally] using (J0.thenDo (altitude_poly p d.large))
  have u := terminal (p:=2) (by decide) j J0
  have va := terminal d.large k q
  let T : (i:I)→Series (Fin (a i)) := fun i => Series.natural (a i)
  let L (i:I) := star_ s P G B i
  let D (i:I) := star_ t P G B i
  have m := visible (l:=l) T v (by simpa [T] using ha)
  have z {Q : I→Tape} (u : ∀ i,Dims.solid (Q i)) (v : r.Has (shape ∘ Q)) : Station r (fun i => layout (Q i)) :=
    Station.tape u v
  have z1 := z (fun i n d => (guard i n (by simp [d])).1) S
  have z2 := z (fun i n d => (guard i n (by simp [d])).1) Y
  have z3 := z (fun i n d => (guard i n (by simp [d])).1) Z
  have ht := z1.product (u.product (z2.product (u.product z3)))
  let A := fun i:I => SpanKey (P i) (G i) (B i) (Block p (k i))
  let Q i := fill_ s t p e P G B i
  let V (i:I) (x : A i) := v i (Q i x)
  let W0 (i:I) (x : A i) := V i (swapper _ _ _ x)
  let N i := (L i).count
  let N' i := (D i).count
  let f0 := modes (τ:=τ) j
  have c := belly j h.le
  have i1 : Drive r N l (cloth L T v) (cloth D T V) :=
    addHalo s t p e P G B u va z1 z2 z3 _ m
  have zW : Manifest _ l (fun (i:I) x => strip (T i) (W0 i x)) :=
    m.shift (fun i x => Q i (swapper _ _ _ x))
  have i3 : Drive r N' l (cloth D T W0) (cloth L T (fun i => v i ∘ swapper _ _ _)) := by
    have e' := subHalo s t p e P G B u va z1 z2 z3 _ zW
    change Drive r N' l _ (stackRun _ (fun i x => strip _ (v i (Q i (swapper _ _ _ (thicken s t p e _ _ _ i x)))))) at e'
    simp only [Q,paid_] at e'; exact e'
  have nc : ∀ i,N' i ≤ p^2*N i := all_counts s t p e P G B -- check syntax
  have N0 : ∀ i,1≤N i := ht.1
  have internal := Strip.Breeze.factor
    (orbitalFin P G B k R d h guard S Y Z q l a ha V) N0 (p^2) nc
  obtain ⟨hc,K,int0⟩ := internal
  have ir : Breeze f0 r N l (together r.header (cloth D T V)) (cloth D T W0) :=
    ⟨c,K,int0.times (fun i => one_le_mul_of_one_le_of_one_le (unit_mass N0 _ _) (c i)) 2 (fun i => by
      unfold runrate
      rw [mul_left_comm] -- ?
      push_cast
      gcongr
      · unfold mass; positivity
      exact magnify h hf (n:=k) (fun i => (g i).2.2) i)⟩
  have f := Rip.split i1.again
  have Dlive : Drive r N l (cloth D T V) r.header := Drive.fetch N0 i1.idle
  exact Breeze.pipe (Strip.Breeze.launch i1 c) (Breeze.pipe ir (Strip.Breeze.launch (Rip.factor i3 N0 (p^2) nc) c) Dlive) f.1
end
end Spindle

end IntegerMultiplication
end Computability
end OAI
