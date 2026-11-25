import OAI.Computability.IntegerMultiplication.Atoll.Rafter
import OAI.Computability.IntegerMultiplication.Curtain.Freedom

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Cap Echo Strip Loom Earth Halo Adic Packed Net Net.Walsh
variable (f k r:ℕ)
abbrev Mbit := r + f*k
abbrev UX (f k:ℕ):= Fin f→Fin (2^k)
abbrev Mid (f k r:ℕ):= Fin (2^r) × UX f k
abbrev braid : Series (Mid f k r) :=
  (Series.natural (2^r)).cart (Retreat f (2^k))
abbrev winds : Series (Mid f k r):=
  ((House f (2^k)).cart (Series.natural (2^r))).via (Equiv.prodComm ..)
noncomputable section
abbrev Roll (f k:ℕ): Adopt (House f (2^k)) (line 2 (f*k)):=
  (Earth.equate (noir k).back f).thenDo (atoms ..)
abbrev Reel (f k:ℕ): Adopt (Retreat f (2^k)) (line 2 (f*k)):=
  ((Adopt.turn _ (retro f (2^k))).back).thenDo (Roll f k)
abbrev Aseal : Adopt (braid f k r) (line 2 (Mbit f k r)):=
  (((noir r).back).split (Reel f k)).thenDo (splint ..)
abbrev Bseal : Adopt (winds f k r) (line 2 (Mbit f k r)):=
  ((((Adopt.turn _ (Equiv.prodComm ..)).back).thenDo ((Roll f k).split ((noir r).back))).thenDo (splint ..)).thenDo
    (castN 2 _ _ (Nat.add_comm ..))

abbrev Fiber := Fin r ⊕ (Fin f × Fin k)
def Aspot: Fiber f k r ≃ Fin (Mbit f k r):=
  (((Equiv.refl _).sumCongr ((Fin.revPerm.prodCongr (Equiv.refl _)).trans finProdFinEquiv)).trans finSumFinEquiv)
def Bspot: Fiber f k r ≃ Fin (Mbit f k r):=
  (((Equiv.sumComm ..).trans (finProdFinEquiv.sumCongr (Equiv.refl _))).trans finSumFinEquiv).trans
    (finCongr (Nat.add_comm ..))
def orderMW: Equiv.Perm (Fin (Mbit f k r)):=
  (Aspot ..).symm.trans (Bspot ..)

variable {f k r}
abbrev rowBit {k} (x : Fin (2^k)):Fin k→ B:= layBit k (((noir k).back).cast x)
abbrev tip (x:Mid f k r)(p:Fiber f k r):B:=
  p.elim (rowBit x.1) (fun i=>rowBit (x.2 i.1) i.2)
private theorem roller (x:UX f k)(i:Fin f)(j:Fin k):
    layBit _ ((Roll ..).cast x) (finProdFinEquiv (i,j))=rowBit (x i) j:=by
  change layBit _ ((atoms ..).cast ((equate ..).cast x)) _=_
  rw [Earth.after,installs];rfl
private theorem reeler (x:UX f k)(i:Fin f)(j:Fin k):
    layBit _ ((Reel ..).cast x) (finProdFinEquiv (i.rev,j))=rowBit (x i) j:=by
  change layBit _ ((Roll f k).cast ((retro f (2^k)).symm x)) _=_
  rw [roller]
  simp [retro]
private theorem cast_ {t y : ℕ} (h : t=y) (x : Block 2 t) (i : Fin t) :
    layBit y ((castN _ _ _ h).cast x) ((finCongr h) i)=layBit _ x i := by
  subst y; rfl
theorem straight (x:Mid f k r)(p:Fiber f k r):
    layBit _ ((Aseal ..).cast x) (Aspot f k r p)=tip x p:=by
  let l := (noir r).back.cast x.1
  let m := (Reel f k).cast x.2
  let u := lightning_b l m
  rcases p with p|⟨i,j⟩
  · change layBit _ ((splint ..).cast (l,m)) (rod _ _ (.inl p))=_
    exact congrFun u (.inl p)
  change layBit _ ((splint ..).cast (l,m)) (rod _ _ (.inr (finProdFinEquiv (i.rev,j))))=_
  exact (congrFun u (.inr (finProdFinEquiv (i.rev,j)))).trans (reeler _ _ _)
theorem curved (x:Mid f k r)(p:Fiber f k r):
    layBit _ ((Bseal ..).cast x) (Bspot f k r p)=tip x p := by
  let h:=Nat.add_comm (f*k) r
  let l := (noir r).back.cast x.1
  let m := (Roll f k).cast x.2
  have u := lightning_b m l
  rcases p with p|⟨i,j⟩
  · change layBit _ ((castN 2 _ _ h).cast ((splint ..).cast (m,l))) ((finCongr h) (rod _ _ (.inr p)))=_
    rw [cast_]
    exact congrFun u (.inr p)
  change layBit _ ((castN 2 _ _ h).cast ((splint ..).cast (m,l))) ((finCongr h) (rod _ _ (.inl (finProdFinEquiv (i,j)))))=_
  rw [cast_]
  exact (congrFun u (.inl (finProdFinEquiv (i,j)))).trans (roller _ _ _)
-- evidence curtain sends A(old) to B(output)
theorem moved (x:Mid f k r):
    (layBit _).symm (layBit _ ((Bseal ..).cast x) ∘ orderMW f k r)=(Aseal ..).cast x:=by
  apply (layBit _).injective
  rw [Equiv.apply_symm_apply]
  funext i
  obtain ⟨i,rfl⟩:=(Aspot f k r).surjective i
  simp only [Function.comp_apply,orderMW,Equiv.trans_apply,Equiv.symm_apply_apply,curved,straight]
theorem moved' (x:Mid f k r):
    (layBit _).symm (layBit _ ((Aseal ..).cast x) ∘ (orderMW f k r).symm)=(Bseal ..).cast x:=by
  apply (layBit _).injective
  rw [Equiv.apply_symm_apply]
  funext i
  obtain ⟨i,rfl⟩:=(Bspot f k r).surjective i
  simp only [Function.comp_apply,orderMW,Equiv.symm_trans_apply,Equiv.symm_apply_apply,Equiv.symm_symm,curved,straight]
end
end Atoll

end IntegerMultiplication
end Computability
end OAI
