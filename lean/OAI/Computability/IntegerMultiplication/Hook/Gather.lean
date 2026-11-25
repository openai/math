import OAI.Computability.IntegerMultiplication.Hook.Place

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Code Strip Dims Adic Packed Net Net.Walsh Earth IntegerMultiplication.Fourier Staff Loom Axon
open Matrix Finset
variable (f g k m : ℕ)
noncomputable section

abbrev row := Fin f→Block 2 (Ht g k m)
abbrev rowT := Track (line 2 (Ht g k m)) f
abbrev rowS : Adopt (rowT f g k m) (line 2 (Len f g k m)) :=
  atoms f _
abbrev Eye (x : row f g k m) : Axon.Scr (Fin f) (Ht g k m) := layBit _ ∘ x
def eye : row f g k m≃Axon.Scr (Fin f) (Ht g k m) where
  toFun := Eye f g k m
  invFun x := (layBit _).symm ∘ x
  left_inv _ := by simp [Eye,Function.comp_def]
  right_inv _ := by simp [Eye,Function.comp_def]
abbrev Deck (f k : ℕ) := Fin f → Block 2 k
abbrev useD (f k : ℕ) := Track (line 2 k) f
abbrev col := (Fin g→Deck f k)× Deck f m
abbrev colT := (Track (useD f k) g).cart (useD f m)

abbrev cup : Adopt (Track (useD f k) g) (line 2 (g*(f*k))) :=
  ((equate (atoms f k) g).thenDo (atoms ..)) -- args?
def valve : Adopt (colT f g k m) (line 2 (Len f g k m)) :=
  (((cup f g k).split (atoms f m)).thenDo (splint ..)).thenDo (castN 2 _ _ (len_alt ..))
variable {f g k m}

private theorem cast_bit {t y : ℕ} (h : t=y) (x : Block 2 t) (i : Fin t) :
    layBit y ((castN _ _ _ h).cast x) ((finCongr h) i)=layBit _ x i := by
  subst y; rfl
private theorem cup_bit (x : Fin g→Deck f k) (i : Fin g) (j : Fin f) (v : Fin k) :
    layBit _ ((cup f g k).cast x) (tok f g k (j,i,v))=layBit _ (x i j) v := by
  change layBit _ ((atoms ..).cast ((equate _ _).cast x)) (finProdFinEquiv (i,finProdFinEquiv (j,v)))=_
  rw [after,installs]; exact after ..

abbrev Enact (x : col f g k m) (a : Grind f g k m) : B :=
  a.2.elim (fun s=> layBit _ (x.1 s.1 a.1) s.2) (fun t=> layBit _ (x.2 a.1) t)
theorem renders (x : col f g k m) (i : Grind f g k m) :
    layBit (Len ..) ((valve f g k m).cast x) (packC f g k m i)=Enact x i := by
  rcases i with ⟨i,⟨a,b⟩|b⟩
  · change layBit _ ((castN _ _ _ _).cast ((splint ..).cast _)) ((finCongr (len_alt f g k m)) (rod _ (f*m) (.inl (tok f g k (i,a,b)))))=_
    rw [cast_bit]
    have t := congrFun (lightning_b ((cup f g k).cast x.1) ((atoms f m).cast x.2)) (.inl (tok f g k (i,a,b)))
    exact t.trans (cup_bit ..)
  change layBit _ ((castN _ _ _ _).cast ((splint ..).cast _)) ((finCongr (len_alt f g k m)) (rod (g*(f*k)) _ (.inr (finProdFinEquiv (i,b)))))=_
  rw [cast_bit]
  have t := congrFun (lightning_b ((cup f g k).cast x.1) ((atoms f m).cast x.2)) (.inr (finProdFinEquiv (i,b)))
  exact t.trans (after ..)
theorem rowS_bit (x : row f g k m) (i : Grind f g k m) :
    layBit _ ((rowS f g k m).cast x) (packR f g k m i) = eye _ _ _ _ x i.1 (knot _ _ _ i.2) := after x i.1 (knot _ _ _ i.2)
-- physical col semantics corpus
def legend : col f g k m ≃ Scr (Fin f) (Ht g k m) where
  toFun x i j := Enact x (i,(knot g k m).symm j)
  invFun x := (fun j i=> (layBit k).symm (fun v=> x i (knot _ _ _ (.inl (j,v)))),
               fun i=> (layBit m).symm (fun v=> x i (knot _ _ _ (.inr v))))
  left_inv x := by
    refine Prod.ext (funext fun j=> funext fun i=> ?_) (funext fun i=>?_)
    all_goals simp [Enact]
  right_inv x := by
    funext i j
    obtain ⟨j,rfl⟩ := (knot g k m).surjective j
    rcases j with ⟨q,j⟩|j <;> simp [Enact]
theorem wears (x : col f g k m) (i : Grind f g k m):
    legend x i.1 (knot g k m i.2)=Enact x i := by simp [legend,Enact] -- typo
theorem rearrange (x : col f g k m) :
    let t := gather f g k m
    let y := (rowS f g k m).cast.symm ((layBit _).symm (layBit _ ((valve ..).cast x) ∘ t))
    legend x = eye f g k m y := by
  dsimp only
  funext i j
  obtain ⟨n,rfl⟩ := (knot g k m).surjective j
  rw [show legend x i (knot _ _ _ n) = Enact x (i,n) from wears x (i,n), ← rowS_bit (f:=f) (i:=(i,n))]
  simp only [Equiv.apply_symm_apply,Function.comp_apply,gather,Equiv.trans_apply,Equiv.symm_apply_apply,renders]
end
end Hook

end IntegerMultiplication
end Computability
end OAI
