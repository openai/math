import OAI.Computability.IntegerMultiplication.Hook.Compass

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk
variable {I J W A : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W A Motif.sigma) (R₁ : Series W)
variable (p t : I→Tape) (f g j y w U : I→ℕ) {T:I→Type} (z:(i:I)→Series (T i)) {r:Regime I}
variable (h : ArrayCards r p t w)
variable (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
variable (u:∀ i,(z i).count*(w i+1)≤U i)
variable (s:∀ i,Phase.safe (f i) (j i)) (q:∀ i,Phase.safe (f i) (y i)) (m:∀ i,f i≤w i+1)
variable (hn:∀ i,1≤f i)
abbrev residue (i:I) := (Pin (p i) × Pin (t i)) × Scr (Fin (f i)) (Ht (g i) (j i) (y i))
variable (x : (i:I)→ residue p t f g j y i→T i→Grain (w i))
noncomputable section
abbrev rain := orchid (zone p t f g j y) z w fun i=> x i ∘ browser
abbrev listB (i:I) := (zone p t f g j y i).count
private theorem rack_f {n k : I→ℕ} (p:Realizes r n) (q:Realizes r k) :
    Told r (fun i=> Loom.Rack (Adic.field 2 (n i)) (k i)) := by
  suffices e : ∀ n k,Loom.Rack (Adic.field 2 n) k = Adic.field 2 (k*n) by
    simp_rw [e]
    exact Told.carrier (by decide) _ (q.times p)
  intro n k
  induction k with
  | zero=> simp [Loom.Rack]; rfl
  | succ k ih=> rw [Loom.Rack,ih, ← field_add]; congr 1; ring

private theorem sizes {P T : Tape} (f : ∀ i,i∈P ++ T→i≤Net.Shuttle.base) {D E: Tape}
    (j₁ : ∀ a,a∈D→a=2) (j₂ : ∀ a,a∈E→a=2) :
    ∀ i,i∈(P++D) ++ (E++T) → i≤Net.Shuttle.base := by
  intro i h
  simp only [List.mem_append] at h f
  rcases h with (q|q)|(q|q)
  · exact f _ (Or.inl q)
  · rw [j₁ i q]; exact Net.Shuttle.base_large.le
  · rw [j₂ i q]; exact Net.Shuttle.base_large.le
  exact f _ (Or.inr q)

private theorem st_v {f n i:ℕ} :
    i∈st f n→i=2 := by
  unfold st
  generalize f*n=k
  induction k with
  | zero=> simp [Adic.field]
  | succ k ih=> simp_all [Adic.field]; tauto
private theorem rk_v {f n i k : ℕ} :
    i∈Loom.Rack (st f n) k→i=2 := by
  induction k with
  | zero=> simp [Loom.Rack]
  | succ k ih =>
    rw [Loom.Rack,List.mem_append]
    exact Or.rec st_v ih

variable (a : (i:I)→Fin (g i))
variable (b : (i:I)→Fin (j i))
variable (Ha : Realizes r (fun i=> (a i).val)) (Hb : Realizes r (fun i=>(b i).val))
include h d R₁ F G J₁ Y u s m hn Ha Hb
theorem flare :
    Breeze (expense j f) r (listB p t f g j y) U
      (together r.header (rain p t f g j y w z x))
      (rain p t f g j y w z fun i => runOn
        (logic (b:=knot (g i) (j i) (y i) (.inl (a i,b i))) Walsh.F) (x i)) := by
  let P i := colPrefix (f:=f i) (k:=j i) (a i)
  let T₀ i := colPost (f:=f i) (m:=y i) (k:=j i) (a i)
  let sf i := spanned (f:=f i) (k:=j i) (a i)
  have a' i : (sf i).after = g i - (a i).val-1 := by
    have t := Single.size (sf i)
    have d := Single.pos (sf i)
    omega
  have hp : Told r P := by
    simp only [P,colPrefix,Single.pos]
    exact rack_f (F.times J₁) Ha
  have hb : Told r T₀ :=
    (show Told r (fun i=> Loom.Rack (st (f i) (j i)) (sf i).after) from
      rack_f (F.times J₁) (by simp_rw [a']; exact (G.minused Ha).minused (Realizes.fix 1))).append
    (Told.carrier (by decide) _ (F.times Y))
  have A : ArrayCards r (fun i=> p i++P i) (fun i=> T₀ i++t i) w :=
    ⟨h.prefix_.append hp,hb.append h.trail,fun i=> sizes (h.below i) (fun _=> rk_v) (fun _ d=> (List.mem_append.mp d).elim rk_v st_v),
      h.digits⟩
  exact dawn d R₁ _ _ A J₁ F s m hn z u _ (fun i=> notch (a i)) _ _ _ Hb (fun i=> sees _ _) x

omit Ha Hb s
variable (vb : (i:I)→Fin (y i)) (hv : Realizes r (fun i=> (vb i).val))
include q hv
theorem quark :
    Breeze (expense y f) r (listB p t f g j y) U
      (together r.header (rain p t f g j y w z x))
      (rain p t f g j y w z fun i => runOn
        (logic (b:=knot (g i) (j i) (y i) (.inr (vb i))) Walsh.F) (x i)) := by
  let P i := colStart (f i) (g i) (j i)
  have hp : Told r P := (show Told r (fun i=> Adic.field 2 ((g i)*(f i*j i))) from
    Told.carrier (by decide) _ (G.times (F.times J₁))).append Told.nil
  have A : ArrayCards r (fun i=> p i++P i) t w :=
    ⟨h.prefix_.append hp,h.trail,fun i=> sizes (E:=[]) (h.below i) (fun _ v=> (List.mem_append.mp v).elim
      (st_v (f:=g i) (n:=f i * j i)) (by simp)) (by simp),h.digits⟩
  exact dawn d R₁ _ _ A Y F q m hn z u _ (fun _=> final_) _ _ _ hv
    (fun i=> wrapUp _) x
end
end Hook

end IntegerMultiplication
end Computability
end OAI
