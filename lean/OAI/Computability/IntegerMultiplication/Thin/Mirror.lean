import OAI.Computability.IntegerMultiplication.Thin.Flight

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Thin
open Code Strip Dims Adic Packed Net Net.Walsh Earth Loom
noncomputable section
variable {I : Type} {r : Regime I}
variable (k w n : I→ℕ)
variable (p : (i:I)→Plane k n i)
variable (Hp : r.Has fun i=> screen (p i))
variable (Hk : r.Has (tally ∘ k)) (Hn : r.Has (tally ∘ n))
variable (gain : ∀ i x,(p i x).1 < (p i x).2)
variable (K:ℕ)
abbrev voyage (i:I) : Equiv.Perm (Fin (k i)) := low (p i) (n i) le_rfl
include Hp Hk Hn gain
theorem glide (x : (i:I)→Byte (k i)→Tree) (e : ∀ i a,(x i a).count≤ K*(w i+1)) :
    let F i := line 2 (k i)
    let T := stackRun F
    Breeze (fun i=> (n i:ℝ)+1) r single (rolls k w) (together r.header (T x))
      (T fun i=> x i ∘ lever (voyage k n p i)) := by
  let Z (i:I) : Dial.States (Wrapped k w K) := ⟨i,x i,e i⟩
  have f := (rotation k w n p Hp Hk Hn gain K).along_cast Z
  unfold ship at f
  simp_rw [lantern k w n p K] at f
  exact ⟨fun i=>by simp,f.2⟩
omit Hp Hk Hn gain

-- exchange nth fields via disjoint layout
section
variable {n k : ℕ} (u v:Fin n→Fin k) (g:Function.Injective u) (f:Function.Injective v) (q:∀ a b,u a≠ v b)
abbrev twin (x : Fin n) := ((u x,v x):Sig k)
include g f q
omit g f q in
private theorem dump {x : ℕ} (h : x≤ n) (s : Fin k)
    (z : ∀ i:Fin n,i.val< x→ u i≠ s ∧ v i≠ s) :
    low (twin u v) x h s=s := by
  induction x with
  | zero=>rfl
  | succ i ih =>
    change low _ _ _ (Equiv.swap (u ⟨i,h⟩) (v ⟨i,h⟩) s)=_
    have t := z ⟨i,h⟩ (Nat.lt_succ_self _)
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm t.1) (Ne.symm t.2)]
    exact ih _ fun i h=>z _ (h.trans (Nat.lt_succ_self _))

theorem coupled {x:ℕ} (h:x≤ n) :
    ∀ i:Fin n, i.val< x →
    let π := low (twin u v) x h
    π (u i)=v i ∧ π (v i)=u i := by
  induction x with
  | zero => simp
  | succ s ih =>
    intro i j
    let r : Fin n := ⟨s,h⟩
    change low _ _ _ (Equiv.swap (u r) (v r) _) = _ ∧ low _ _ _ (Equiv.swap (u r) (v r) _) = _
    by_cases z : i=r
    · subst i; rw [Equiv.swap_apply_left,Equiv.swap_apply_right]
      refine ⟨dump u v _ _ ?_,dump u v _ _ ?_⟩
      · intro i hi
        refine ⟨q _ _,fun e=>?_⟩
        have := f e
        subst i; exact lt_irrefl s hi
      intro i hi
      refine ⟨fun e=>?_,Ne.symm (q _ _)⟩
      have := g e; subst i; exact lt_irrefl s hi
    have ke : i.val< s := lt_of_le_of_ne (Nat.le_of_lt_succ j) fun h₁=> z (Fin.ext h₁)
    rw [Equiv.swap_apply_of_ne_of_ne (fun h=> z (g h)) (q _ _)]
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (q _ _)) (fun h=>z (f h))]
    exact ih _ i ke

open Iter
section
-- notation block swap high/low with gap. contact with Packed.tile
variable (c L d b : ℕ)
abbrev tn := c + L + d + L + b
abbrev hub := (c+L+d)
abbrev nearby (i : Fin L) : Fin (tn c L d b) :=
  ⟨c+i.val,by have := i.isLt; dsimp [tn]; omega⟩
abbrev afar (i:Fin L) : Fin (tn c L d b) :=
  ⟨hub c L d+i.val,by have := i.isLt; dsimp [tn,hub]; omega⟩

omit u v g f q
theorem unit0 : Function.Injective (nearby c L d b) := by
  intro i j e
  apply Fin.ext
  have t := congrArg Fin.val e
  dsimp only [nearby] at t; omega
theorem unit1 : Function.Injective (afar c L d b) := by
  intro i j e
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))
theorem sep (i j : Fin L) : nearby c L d b i < afar c L d b j := by
  change c+i.val< c+L+d+j.val
  have := i.isLt; omega
abbrev tour := twin (nearby c L d b) (afar c L d b)
private theorem formed (i:Fin L) :
    let a := nearby c L d b i
    let y := afar c L d b i
    let p := low (tour c L d b) L le_rfl
    p a=y ∧ p y=a :=
  coupled _ _ (unit0 ..) (unit1 ..) (fun _i _j=> (sep ..).ne) le_rfl i i.isLt
abbrev Land := Byte c × Byte L × Byte d × Byte L × Byte b
abbrev lands := (line 2 c).cart ((line 2 L).cart ((line 2 d).cart ((line 2 L).cart (line 2 b))))
def bolt_ : Adopt (lands c L d b) (line 2 (tn c L d b)) :=
  let T := tile 2 L b
  let G := ((Adopt.same (line 2 d)).split T).thenDo (tile 2 _ _)
  let H := ((Adopt.same _).split G).thenDo (tile 2 L _)
  (((Adopt.same _).split H).thenDo (tile 2 c _)).thenDo (castN 2 _ _ (by unfold tn; omega))
variable {c L d b}
private theorem most0 (x : Land c L d b) :
    most ((bolt_ _ _ _ _).cast x)=
    most x.1 ++ (most x.2.1 ++ (most x.2.2.1 ++ (most x.2.2.2.1 ++ most x.2.2.2.2))) := by
  change most ((castN 2 _ _ _).cast ((tile 2 _ _).cast (_, (tile 2 _ _).cast (_, (tile 2 _ _).cast (_, (tile 2 _ _).cast _)))))= _
  rcases x with ⟨t,u,v,w,c⟩
  simp only [castN_most,tile_most]; rfl
abbrev setD (x:Land c L d b) := layBit _ ((bolt_ c L d b).cast x)
private theorem set0 (x:Land c L d b) (i:Fin L) :
    setD x (nearby c L d b i)=layBit _ x.2.1 i := by
  change (most ((bolt_ _ _ _ _).cast x))[c+i.val]'_=(most x.2.1)[i.val]'_
  simp only [most0]
  rw [List.getElem_append_right (by simp)]
  simp only [Adic.length,Nat.add_sub_cancel_left,List.getElem_append_left (show i.val < (most x.2.1).length by simp)]
private theorem set1 (x:Land c L d b) (i:Fin L) :
    setD x (afar c L d b i)=layBit _ x.2.2.2.1 i := by
  change (most ((bolt_ _ _ _ _).cast x))[c+L+d+i.val]'_=(most _)[i.val]'_
  simp only [most0,Nat.add_assoc]
  rw [List.getElem_append_right (by simp)]
  simp only [Adic.length,Nat.add_sub_cancel_left]
  rw [List.getElem_append_right (by simp)]
  simp only [Adic.length,Nat.add_sub_cancel_left]
  rw [List.getElem_append_right (by simp)]
  simp only [Adic.length,Nat.add_sub_cancel_left,List.getElem_append_left (show i.val < (most x.2.2.2.1).length by simp)]

abbrev switch_ (x: Land c L d b) : Land c L d b := (x.1,x.2.2.2.1,x.2.2.1,x.2.1,x.2.2.2.2)
private theorem set2 (x:Land c L d b)
    (i:Fin (tn c L d b)) (e : i.val< c ∨
      (i.val≥ c+L ∧ i.val< c+L+d) ∨ i.val≥ c+L+d+L) :
    setD x i = setD (switch_ x) i := by
  change (most _)[i.val]'_=(most _)[i.val]'_
  simp only [most0 x,most0 (switch_ x)]
  rcases e with e|⟨h,e⟩|e <;>
    simp (disch := (simp only [Adic.length]; omega)) only [Adic.length,List.getElem_append_left,List.getElem_append_right]
theorem sight (x:Land c L d b) :
    (lever (low (tour c L d b) L le_rfl)) ((bolt_ ..).cast x)=
      (bolt_ ..).cast (switch_ x) := by
  apply (layBit _).injective; unfold lever; rw [Equiv.apply_symm_apply]
  funext i
  let q := low (tour c L d b) L le_rfl
  let a := nearby c L d b
  let v := afar c L d b
  change setD x (q i)= setD (switch_ x) i
  by_cases e : ∃ j,a j=i
  · obtain ⟨j,rfl⟩ := e
    rw [(formed ..).1,set1 x]; exact (set0 (switch_ x) j).symm
  by_cases h : ∃ j,v j=i
  · obtain ⟨j,rfl⟩ := h
    rw [(formed ..).2,set0 x]; exact (set1 (switch_ x) j).symm
  rw [dump a v le_rfl i (fun t _=> ⟨fun h=>e ⟨t,h⟩,fun u=>h ⟨t,u⟩⟩)]
  apply set2
  have P (x:Fin L) : ¬(c+x.val=i.val) := fun h=>e ⟨x,Fin.ext h⟩
  by_cases l₁ : i.val< c+L
  · left; by_contra! u
    exact P ⟨i.val-c,by omega⟩ (by dsimp; omega)
  have M (x:Fin L) : ¬(c+L+d+x.val=i.val) := fun u=>h ⟨x,Fin.ext u⟩
  by_cases l₂ : i.val< c+L+d
  · omega
  right; right
  by_contra! u
  exact M ⟨i.val-(c+L+d),by omega⟩ (by dsimp; omega)
end
end
end
end Thin

end IntegerMultiplication
end Computability
end OAI
