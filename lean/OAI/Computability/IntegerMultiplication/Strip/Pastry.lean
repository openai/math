import OAI.Computability.IntegerMultiplication.Haze.Paradigm

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Loom Adic
variable {I X U Y : Type} [Codec X] [Codec U] [Codec Y] {r : Regime I}
variable {A B : I→ Type} (a : (i:I)→Series (A i)) (b : (i:I)→Series (B i))
variable {n w : I→ℕ} (u : I→U) (f : (i:I)→A i→B i→X)
variable (h : r.Has u) (sa : Station r a) (q : ∃ c:ℕ,∀ i,size (u i)≤c*(w i))
    (e : ∀ i,(b i).count*w i≤n i)

omit [Codec U] in
private theorem redraw (l a : List (List U)) (h : l.map ruler=a.map ruler) :
    (Piecework.segment (a.map ruler) l.flatten).1=l := by
  have e : ruler (X:=U) = fun l=> tally l.length := by funext; simp [ruler,tally]
  rw [← h, e]
  exact congrArg Prod.fst (Piecework.prescribed l)
include h sa q e
/-- deliver common parameter u to every row, use at every coefficient, then recombine
with supplied template. u may be as large as a coefficient. L(i)=0 allowed. -/
theorem equip {z : I→Tree}
    (H : Rip r (fun i=>(a i).count) n z (cloth a b f))
    (G : Rip r (fun i=>(a i).count) n z r.header)
    (p : U × X → Y) (ez : Easy p) (u0 : U) (x0 : X) :
    Rip r (fun i=>(a i).count) n z (cloth a b fun i j k=>p (u i,f i j k)) := by
  let A0 := fun i=> (a i).count
  let V i := (a i).tab (fun j=> (b i).tab (f i j))
  have t : Rip r A0 n z (send ∘ V) := by
    unfold cloth stackRun at H
    simpa only [V,stripe_eq',Function.comp_def] using H
  have ctrl := G.chain (Rip.header sa.1 h)
  let s (i:I) := (a i).cart (b i)
  let v (i:I) (x : A i × B i) := f i x.1 x.2
  have iH : Rip r A0 n z (send ∘ fun i=> (s i).tab (v i)) := by
    simp only [Function.comp_def,s,v,Series.grouped]
    exact Fatigue.act t _ Easy.flatten
  have get := (Fatigue.act iH _ (Easy.ruler easy_id)).twice ctrl
  obtain ⟨k,d⟩ := (get : Rip r A0 n z _)
  have mp (i:I) : ruler ((s i).tab (v i))=tally (s i).count := by simp [ruler,tally]
  simp only [Function.comp_def,mp] at d
  -- spread need ctl cost per coeff AND +1 independent. via header Dom for one
  obtain ⟨m,C,E⟩ := (Regime.Small.extent (k:=fun i=>send (u i)) h)
  obtain ⟨j,J⟩ := q
  let v₁ := mass r A0 n (k+m)
  have α := d.larger (d:=v₁) (mass_le (by omega : k≤k+m))
  have y : Carries v₁ z (stackRun s (fun i a=> send (u i))) := by
    apply spread s _ α
    refine ⟨j+C,fun i=>?_⟩
    change ((s i).count+1 : ℝ)*(size (u i):ℝ)≤_
    rw [add_mul,one_mul]
    have P : (size (u i):ℝ)≤ (C:ℝ)*(r.scale i+1:ℝ)^m := by exact_mod_cast E i
    have P0 : ∀ i,1≤ A0 i := by
      -- v name shadow function; parameter v Station renamed?
      exact sa.1
    have P1 : (size (u i):ℝ)≤ (C:ℝ)*v₁ i := by
      refine P.trans ?_
      have hv : (1:ℝ)≤A0 i := by exact_mod_cast P0 i
      suffices t : (r.scale i+1:ℝ)^m ≤ mass r A0 n m i by gcongr; exact t.trans (mass_le (by omega : m≤k+m) i)
      unfold mass
      have z := pow_nonneg (show 0≤(r.scale i:ℝ)+1 by positivity) m
      nlinarith [Nat.cast_nonneg (α:=ℝ) (n i)]
    rw [Nat.cast_add,add_mul]
    apply add_le_add _ P1
    have e0 : (s i).count*size (u i) ≤ j*(A0 i*n i) := by
      dsimp only [s]; rw [Series.count_cart]
      have hg := Nat.mul_le_mul_left ((a i).count*(b i).count) (J i)
      have hz := Nat.mul_le_mul_left (j*(a i).count) (e i)
      unfold A0; nlinarith
    refine (show ((s i).count:ℝ)* (size (u i):ℝ) ≤ (j:ℝ)*(A0 i * (n i:ℝ)) by exact_mod_cast e0).trans ?_
    unfold v₁ mass; gcongr; exact le_add_of_nonneg_right (by positivity)
  have c₁ : Rip r A0 n z (send ∘ fun i=> (s i).tab (fun _=>u i)) := by
    unfold stackRun at y
    simpa only [stripe_eq',Function.comp_def,Rip] using (show Rip r A0 n z (fun i=>stripe (s i) (fun _=>send (u i))) from ⟨k+m,y⟩)
  have a₁ := Fatigue.act
    (x:=fun i=> ((s i).tab (fun _=>u i),(s i).tab (v i))) (c₁.twice iH)
    (lock p u0 x0) (easy_lock _ ez ..)
  simp only [paired] at a₁
  -- cut into shape using original tally lists
  let t' := fun i=> (a i).tab (fun j=> (b i).tab (fun k=>p (u i,f i j k)))
  let sh := fun i=> List.map ruler (V i)
  have e₃ : Rip r A0 n z (send ∘ fun i=> (sh i,(t' i).flatten)) :=
    (Fatigue.act t (List.map ruler) (Easy.ruler easy_id).mapping).twice
      (show Rip r A0 n _ (send ∘ fun i=> (t' i).flatten) from by
        simpa only [t',s,v,Function.comp_def,Series.grouped] using a₁)
  let e4 := Fatigue.act e₃ (fun i : List Tally × List Y=> (Piecework.segment i.1 i.2).1) Piecework.easy.fstCompose
  have p4 i : sh i = (t' i).map (tally ∘ List.length) := by
    simp only [sh,t',V,Series.map_tab,Function.comp_def,Series.card]
    simp [ruler,tally] -- length taboo
  unfold cloth stackRun
  simp only [stripe_eq']
  convert e4 using 1
  funext i
  dsimp only [Function.comp_apply]
  rw [p4,Piecework.prescribed]
end Strip

end IntegerMultiplication
end Computability
end OAI
