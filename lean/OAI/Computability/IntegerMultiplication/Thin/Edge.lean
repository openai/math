import OAI.Computability.IntegerMultiplication.Thin.Wisp
import OAI.Computability.IntegerMultiplication.Earth.Charge

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Thin
open Code Strip Dims Adic Packed Net Net.Walsh Earth Loom
noncomputable section
abbrev Byte (k : ℕ) := Block 2 k
variable {k : ℕ}
abbrev stride (i : Fin k) (j : Fin k) := j.val-i.val-1
abbrev shell (i j : Fin k) := Byte i.val × Fin 2 × Byte (stride i j) × Fin 2 × Byte (k-j.val-1)
abbrev two := Series.natural 2
abbrev flush (i j : Fin k) := (line 2 i.val).cart (two.cart ((line 2 (stride i j)).cart (two.cart (line 2 (k-j.val-1)))))
variable (i j m:Fin k)
def innerS (h:i<j) :
    Adopt (flush i j) (line 2 k) :=
  let D0 := ((chip 2).split (Adopt.same _)).thenDo (tile 2 1 (k-j.val-1))
  let D1 := ((Adopt.same (line 2 (stride i j))).split D0).thenDo (tile 2 _ _)
  let D2 := ((chip 2).split D1).thenDo (tile 2 _ _)
  let D3 := ((Adopt.same (line 2 i.val)).split D2).thenDo (tile 2 _ _)
  D3.thenDo (Packed.castN 2 _ _ (by unfold stride; have : i.val<j.val:=h; have := j.isLt; omega))
def close_ (x : shell i j) : shell i j:=
  (x.1,x.2.2.2.1,x.2.2.1,x.2.1,x.2.2.2.2)
theorem innerS_r (h:i<j) (x : shell i j) :
    most ((innerS i j h).cast x)= most x.1 ++ x.2.1::(most x.2.2.1 ++ x.2.2.2.1::most x.2.2.2.2) := by
  change most ((castN 2 _ _ _).cast ((tile 2 _ _).cast (_, (tile 2 _ _).cast (_, (tile 2 _ _).cast (_, (tile 2 _ _).cast (_, _))))))=_
  rw [castN_most,tile_most,tile_most,tile_most,tile_most,chip_word,chip_word]; rfl
private theorem lowB (h:i<j) (x : shell i j) :
    layBit _ ((innerS i j h).cast x) i = x.2.1 := by
  change (most _)[i.val]'_=_
  simp only [innerS_r i j h x]
  rw [List.getElem_append_right (by simp)]
  simp
private theorem upB (h:i<j) (x : shell i j) :
    layBit _ ((innerS i j h).cast x) j = x.2.2.2.1 := by
  change (most _)[j.val]'_=_
  simp only [innerS_r i j h x]
  rw [List.getElem_append_right (by simp; exact h.le)]
  have e : i.val<j.val:=h
  have E : j.val-i.val=stride i j+1 := by unfold stride; omega
  simp only [Adic.length,E,List.getElem_cons_succ]
  rw [List.getElem_append_right (by simp)]
  simp
theorem border (h:i<j) (x : shell i j) :
    layBit _ ((innerS i j h).cast (close_ i j x)) m =
      layBit _ ((innerS i j h).cast x) (Equiv.swap i j m) := by
  by_cases hi : i=m
  · subst m; rw [Equiv.swap_apply_left, lowB, upB]; rfl
  by_cases hj : j=m
  · subst m; rw [Equiv.swap_apply_right, upB, lowB]; rfl
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)]
  change (most ((innerS i j h).cast (close_ i j x)))[m.val]'_=(most ((innerS i j h).cast x))[m.val]'_
  simp only [innerS_r]
  have q : i.val≠m.val := by intro e; apply hi; exact Fin.ext e
  by_cases h0 : m.val< i.val
  · rw [List.getElem_append_left (by simp only [Adic.length]; exact h0),List.getElem_append_left (by simp only [Adic.length]; exact h0)]; rfl
  rw [List.getElem_append_right (by simp only [Adic.length]; omega),
    List.getElem_append_right (by simp only [Adic.length]; omega)]
  have e : i.val<j.val := h
  have E : m.val-i.val=stride i m+1 := by unfold stride; omega
  simp only [Adic.length,E,List.getElem_cons_succ]
  have w0 : j.val≠m.val := by intro e; apply hj; exact Fin.ext e
  by_cases h1 : m.val< j.val
  · have q0 : stride i m< stride i j := by unfold stride; omega
    rw [List.getElem_append_left (by simp [q0]),List.getElem_append_left (by simp [q0])]; rfl
  have q0 : stride i j+1≤ stride i m := by unfold stride; omega
  rw [List.getElem_append_right (by simp only [Adic.length]; omega),List.getElem_append_right (by simp only [Adic.length]; omega)]
  have j : stride i m-stride i j=(stride i m-stride i j-1)+1 := by omega
  simp only [Adic.length]
  conv_lhs => arg 2; rw [j] -- getelem binder? not under
  conv_rhs => arg 2; rw [j]
  rfl
def choke (x:Byte k) := (layBit k).symm ((layBit k x) ∘ (Equiv.swap i j))
theorem designed (h:i<j) (x : shell i j) :
    choke i j ((innerS i j h).cast x)=(innerS i j h).cast (close_ i j x) := by
  apply (layBit k).injective
  unfold choke
  rw [Equiv.apply_symm_apply]
  funext a; exact (border i j a h x).symm

variable {I : Type} {r : Regime I} {N: I→ℕ} {z : I→Tree}
variable (L:I→ℕ) (u v : (i:I)→Fin (L i)) (guard : ∀i,u i<v i)
variable (n : ∀ i,2^L i ≤ N i)
variable (h : Deck r N z r.header)
variable (h₀ : r.Has (fun i=> tally (u i).val)) (h₁ : r.Has (fun i=> tally (v i).val))
variable (h₂ : r.Has (tally ∘ L))
-- count and bags
def minus (p : Tally × Tally) :=
  (cutLists p.swap).2
@[fun_prop] theorem minus_easy : Easy minus :=
  Easy.exchange.compose (easy_cut Easy.identity).sndCompose
theorem less (i j) :
    minus (tally i,tally j)=tally (i-j) := by simp [minus,cutLists,tally]

include guard n h h₀ h₁ h₂
-- single bit arbitrary
theorem motion (x : (i:I)→Byte (L i)→Tree)
    (e : Deck r N z (stackRun (fun i=>line 2 (L i)) x)) :
    Deck r N z (stackRun (fun i=>line 2 (L i)) fun i=> x i ∘ choke (u i) (v i)) := by
  have b (g:I→ℕ) (p : ∀ i,g i≤L i) (d : r.Has (tally ∘ g)) :=
    bags (s:=fun i=>Adic.field 2 (g i)) (Told.carrier (by decide) _ d) h
      (fun i=> (show room (Adic.field 2 (g i))= 2^(g i) by
        rw [← Dims.population, ← Adic.count (p:=2) (l:=g i)]) |>.le.trans
        ((Nat.pow_le_pow_right (by decide) (p i)).trans (n i)))
  have j (g y:I→ℕ) (q:r.Has (tally ∘ g)) (d:r.Has (tally ∘ y)) : r.Has (fun i=> tally (g i-y i)) := by
    simpa only [Function.comp_def,less] using (q.pair d).ez minus_easy
  let u₁ (i:I) := (u i).val; let u₂ (i:I) := stride (u i) (v i); let u₃ i := L i-(v i).val-1
  let p i := line 2 (u₁ i); let g i := line 2 (u₂ i); let t i := line 2 (u₃ i)
  have pp := b u₁ (fun i=> (u i).isLt.le) h₀
  have tt := b u₃ (fun i=> by unfold u₃; omega)
    (j _ _ (j L (fun i=>(v i).val) h₂ h₁) (Regime.fixed (tally 1)))
  have gg := b u₂ (fun i=> by unfold u₂ stride; have := (v i).isLt; omega)
    (j _ _ (j (fun i=>(v i).val) u₁ h₁ h₀) (Regime.fixed (tally 1)))
  have E (i:I) : ((p @@ sr two @@ g @@ sr two @@ t) i).count= 2^L i :=
    (innerS (u i) (v i) (guard i)).cost.trans (by rw [Series.total]; exact Adic.count)
  have d' (g:I→ℕ) (i) : 1 ≤ (line 2 (g i)).count := by
    simp only [Series.total, Adic.count]
    exact Nat.one_le_pow _ _ (by decide)
  have e₃ : ∀ i,((p @@ g @@ t) i).count ≤ N i := by
    intro i
    apply le_trans _ (n i)
    rw [← E]
    simp only [fusion,sr,Series.count_cart,two,Series.count_natural]
    nlinarith [Nat.zero_le ((p i).count*((g i).count*(t i).count))]
  let f (i:I) := innerS (u i) (v i) (guard i)
  unfold stackRun at e
  simp_rw [(f _).packet] at e -- f _ doesn't elaborate
  have h' := twist (p:=p) (g:=g) (b:=t) two pp gg tt e₃ (show 1≤two.count by simp [two])
    (d' u₁) (d' u₃) (d' u₂) (fun i => x i ∘ (f i).cast) e
  unfold stackRun
  simp_rw [(f _).packet]
  have K (i:I) (a : shell (u i) (v i)) := designed (u i) (v i) (guard i) a
  change Deck _ _ _ (fun i=>stripe _ (fun s: shell (u i) (v i)=> x i (choke _ _ ((f i).cast s))))
  unfold f
  simp_rw [K]
  exact h'
end
end Thin

end IntegerMultiplication
end Computability
end OAI
