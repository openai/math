import OAI.Computability.IntegerMultiplication.Hook.Drive

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk
variable {I J W A : Type} [Fintype J] [DecidableEq J] [Fintype W] (dl : Guild J W A Motif.sigma) (R₁ : Series W)
variable (p t : I→Tape) (f g j y w U : I→ℕ) {T:I→Type} (z:(i:I)→Series (T i)) {r:Regime I}
variable (h : ArrayCards r p t w)
variable (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
variable (u:∀ i,(z i).count*(w i+1)≤U i)
variable (s:∀ i,Phase.safe (f i) (j i)) (q:∀ i,Phase.safe (f i) (y i)) (m:∀ i,f i≤w i+1)
variable (hn:∀ i,1≤f i)
variable (x : (i:I)→ residue p t f g j y i→T i→Grain (w i))
noncomputable section
include h F G J₁ Y
theorem placeR : Station r (zone p t f g j y) := by
  let e := realizes_n F G J₁ Y
  have A := h.prefix_.station.product ((Adic.terminal (p:=2) (by decide) _ e).product h.trail.station)
  unfold Station zone at *
  simp_rw [show ∀i:I,(Phase.order (p i) (t i) (colT (f i) (g i) (j i) (y i))).count= (spec p t (norm f g j y) i).count from fun i=> (vS p t f g j y i).cost]
  exact A

omit h F G J₁ Y
variable {k v n:ℕ}
private theorem announce (i:Fin (Ht k v n)) (a : Fin k) (b:Fin v) (e:i=knot _ _ _ (.inl (a,b))) :
    i.val = a.val*v+b.val := by rw [e]; change b.val+v*a.val=_; ring
private theorem decl (i:Fin (Ht k v n)) (a : Fin n) (e:i=knot _ _ _ (.inr a)) :
    i.val=k*v+a.val := by rw [e]; rfl
private theorem exact_ (i : Fin (Ht k v n)) :
    i.val < k*v ↔ ∃ a b,i=knot k v n (.inl (a,b)) := by
  obtain ⟨x,rfl⟩ := (knot k v n).surjective i
  cases x with
  | inl x =>
    obtain ⟨q,c⟩ := x
    simp
    have := q.isLt; have := c.isLt; nlinarith
  | inr x=>
    rw [decl _ _ rfl]
    simp only [(knot k v n).apply_eq_iff_eq]; simp
private theorem rare (i: Fin (Ht k v n)) (e : ¬i.val < k*v) :
    ∃ a,i=knot k v n (.inr a) := by
  obtain ⟨x,rfl⟩ := (knot k v n).surjective i
  rcases x with ⟨x,y⟩|y
  · exact (e ((exact_ _).2 ⟨_,_,rfl⟩)).elim
  simp

variable (a:(i:I)→Fin (Ht (g i) (j i) (y i))) (b:Realizes r (fun i=> (a i).val))
abbrev stairs i := expense (fun i=> j i+y i) f i

private theorem up (a₁ b c : I → ℕ) (g : ∀ i,a₁ i ≤ b i) (i:I) :
    expense a₁ c i ≤ expense b c i := by
  unfold expense
  gcongr
  exact g i

include h dl R₁ F G J₁ Y u s q m hn b
theorem plume :
    let N := listB p t f g j y
    let r_ := rain p t f g j y w z
    Breeze (stairs f j y) r N U
      (together r.header (r_ x))
      (r_ fun i=> runOn (logic (b:=a i) Walsh.F) (x i)) := by
  let P i := (a i).val < g i*j i
  obtain ⟨V,hv,e⟩ := b.below (G.times J₁)
  let High := {i : I // V i=true}; let low := {i : I // V i=false}
  let u₀ : low→I := Subtype.val; let u₁ : High→I := Subtype.val
  let N := listB p t f g j y
  let Z := rain p t f g j y w z x
  let A i := runOn (logic (b:=a i) Walsh.F) (x i)
  let B := rain p t f g j y w z A
  have M := placeR p t f g j y w h F G J₁ Y
  have D : Alive r N U Z := shelter _ z w _ M u
  apply classify_b V (Drive.small M.1 D hv) u₁ u₀
    (fun i=>⟨fun e=>⟨⟨i,e⟩,rfl⟩,fun e=> ⟨⟨i,e⟩,rfl⟩⟩)
  · have sm {A:Type} [Codec A] (l : I→A) (h : r.Has l) : (r.pull u₀).Has (l ∘ u₀) :=
      Task.BT.map h u₀
    have sS (l:I→ℕ) (h : Realizes r l) : Realizes (r.pull u₀) (l ∘ u₀) := sm _ h
    have hL : ArrayCards (r.pull u₀) (p ∘ u₀) (t ∘ u₀) (w ∘ u₀) :=
      ⟨⟨fun i=>h.prefix_.solid _, sm _ h.prefix_.shape⟩,
       ⟨fun i=>h.trail.solid _,sm _ h.trail.shape⟩,
       fun i=>h.below _, sS _ h.digits⟩
    have ex (i:low) : ¬P i.val := fun H=> (show False from Bool.noConfusion (((e _).1 H).symm.trans i.property))
    choose T hT using fun i:low=> rare (a (u₀ i)) (ex i)
    have s₁ : Realizes (r.pull u₀) (fun i=> (T i).val) := by
      have w := (sS _ b).minused (sS _ (G.times J₁))
      have o i := decl (a _) (T i) (hT i)
      simpa only [Realizes,Function.comp_def,o,Nat.add_sub_cancel_left] using w
    let x0 i := x (u₀ i)
    have X :=
      quark dl R₁ _ _ _ _ _ _ _ (U ∘ u₀) (fun i=> z (u₀ i)) hL (sS _ F) (sS _ G) (sS _ J₁) (sS _ Y)
        (fun i=>u (u₀ i)) (fun i=>q (u₀ i)) (fun i=>m (u₀ i)) (fun i=>hn (u₀ i)) x0 T s₁
    have r := X.raise (fun i=> up y (fun i=>j i+y i) f (by simp) (u₀ i))
    simp_rw [show ∀ i:low,knot ((g ∘ u₀) i) ((j ∘ u₀) i) ((y ∘ u₀) i) (.inr (T i))=a (u₀ i) from fun i=> (hT i).symm] at r -- g comp won't match
    exact r
  · have sm {A:Type} [Codec A] (l : I→A) (h : r.Has l) : (r.pull u₁).Has (l ∘ u₁) :=
      Task.BT.map h u₁
    have sS (l:I→ℕ) (h : Realizes r l) : Realizes (r.pull u₁) (l ∘ u₁) := sm _ h
    have hL : ArrayCards (r.pull u₁) (p ∘ u₁) (t ∘ u₁) (w ∘ u₁) :=
      ⟨⟨fun i=>h.prefix_.solid _,sm _ h.prefix_.shape⟩,
       ⟨fun i=>h.trail.solid _,sm _ h.trail.shape⟩,
       fun i=> h.below _,sS _ h.digits⟩
    have ex (i:High):P i.val := (e _).2 i.property
    choose T Z hT using fun i:High=> (exact_ (a (u₁ i))).1 (ex i)
    have ξ (i) := announce _ _ _ (hT i)
    have χ (i): ((T i).val*j (u₁ i)+(Z i).val)/j (u₁ i)=(T i).val := by
      rw [Nat.add_comm _ ((Z i).val), Nat.mul_comm ((T i).val),Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero ?_),Nat.div_eq_of_lt (Z i).isLt, Nat.zero_add]
      have := (Z i).isLt; omega
    have t₀ : Realizes (r.pull u₁) (fun i=>(T i).val) := by
      have w := (sS _ b).dividing (sS _ J₁)
      simpa only [Realizes,Function.comp_def,ξ,χ] using w
    have o (i): ((T i).val*j (u₁ i)+(Z i).val)%j (u₁ i)=(Z i).val := by simp [Nat.add_comm _ ((Z i).val),Nat.mod_eq_of_lt (Z i).isLt]
    have z₀ : Realizes (r.pull u₁) (fun i=>(Z i).val) := by
      have w := (sS _ b).rem (sS _ J₁)
      simpa only [Realizes,Function.comp_def,ξ,o] using w
    let x₁ i := x (u₁ i)
    have X := flare dl R₁ _ _ _ _ _ _ _ (U ∘ u₁) (fun i=> z (u₁ i)) hL (sS _ F) (sS _ G) (sS _ J₁) (sS _ Y)
        (fun i=>u (u₁ i)) (fun i=>s (u₁ i)) (fun i=>m (u₁ i)) (fun i=>hn (u₁ i)) x₁ T Z t₀ z₀
    have w := X.raise (fun i=> up j (fun i=>j i+y i) f (by simp) (u₁ i))
    simp_rw [show ∀ i:High,knot ((g ∘ u₁) i) ((j ∘ u₁) i) ((y ∘ u₁) i) (.inl (T i,Z i))=a (u₁ i) from fun i=> (hT i).symm] at w
    exact w
end
end Hook

end IntegerMultiplication
end Computability
end OAI
