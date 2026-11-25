import OAI.Computability.IntegerMultiplication.Earth.Bolt

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Loom Strip Strip.Optic Strip.Dims Adic Net Net.Tensor Net.Walsh Phase Packed Haze
open Finset Matrix
noncomputable section
variable {p t : Tape} {m n : ℕ}
def splint (n m) :
    Adopt ((line 2 n).cart (line 2 m)) (line 2 (n+m)) :=
  (((bolt _).back.split (bolt _).back).thenDo (Loom.spire _ m n)).thenDo (bolt _)
abbrev pills (m n : ℕ) := Fin m ⊕ Fin n
abbrev rod (m n : ℕ) : pills m n ≃ Fin (m+n) := finSumFinEquiv
theorem lightning_b (x : Block 2 m) (y : Block 2 n) :
    let f := layBit _ ((splint m n).cast (x,y)) ∘ rod m n
    f = Sum.elim (layBit _ x) (layBit _ y) := by
  obtain ⟨a,rfl⟩ := (bolt m).cast.surjective x
  obtain ⟨b,rfl⟩ := (bolt n).cast.surjective y
  dsimp only
  change layBit _ ((bolt _).cast ((Loom.spire (Series.natural 2) n m).cast
    ((bolt m).cast.symm ((bolt m).cast a),(bolt n).cast.symm ((bolt n).cast b)))) ∘ _ = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  funext i
  rcases i with i|i
  · have h1 : (layBit (m+n) ((bolt (m+n)).cast
        ((Loom.spire (Series.natural 2) n m).cast (a,b)))) (Fin.castAdd n i) =
        ((Loom.spire (Series.natural 2) n m).cast (a,b)) (Fin.castAdd n i) :=
      congrFun (lightning _) _
    have h2 : ((Loom.spire (Series.natural 2) n m).cast (a,b)) (Fin.castAdd n i) = a i :=
      (spire_n (Series.natural 2) a b).1 i
    have h3 : a i = (layBit m ((bolt m).cast a)) i := (congrFun (lightning a) i).symm
    exact h1.trans (h2.trans h3)
  · have h1 : (layBit (m+n) ((bolt (m+n)).cast
        ((Loom.spire (Series.natural 2) n m).cast (a,b)))) (Fin.natAdd m i) =
        ((Loom.spire (Series.natural 2) n m).cast (a,b)) (Fin.natAdd m i) :=
      congrFun (lightning _) _
    have h2 : ((Loom.spire (Series.natural 2) n m).cast (a,b)) (Fin.natAdd m i) = b i :=
      (spire_n (Series.natural 2) a b).2 i
    have h3 : b i = (layBit n ((bolt n).cast b)) i := (congrFun (lightning b) i).symm
    exact h1.trans (h2.trans h3)

abbrev medicine p t n m := Base p t (Block 2 n × Block 2 m)
abbrev forms p t n m := Phase.order p t ((line 2 n).cart (line 2 m))
def heal (p t n m) : Adopt (forms p t n m) (comfort p t (n+m)) :=
  ((Adopt.same _).split ((splint _ _).split (Adopt.same _)))
def fixA (p t n m) :
    Adopt (forms p t n m) (comfort p (Adic.field 2 m++t) n) :=
  (Adopt.same _).split ((Adopt.rotate (line 2 n) (line 2 m) (layout t)).thenDo
    ((Adopt.same _).split (Loom.unite _ _)))
def fixB (p t n m) :
    Adopt (forms p t n m) (comfort (p++Adic.field 2 n) t m) :=
  let s := line 2 m; let v := layout t
  (((Adopt.same _).split (Adopt.rotate (line 2 n) s v)).thenDo (Adopt.rotate (layout p) _ (s.cart v)).back).thenDo ((Loom.unite _ _).split (Adopt.same _))

private def pairing (x : Addr (Fin n) × Addr (Fin m)) : Addr (Fin (n+m)) :=
  Sum.elim x.1 x.2 ∘ (rod n m).symm
private theorem pair_l (x : Addr (Fin n)×Addr (Fin m)) (i : Fin n) :
    pairing x (rod n m (.inl i)) = x.1 i := by simp [pairing]
private theorem pair_r (x : Addr (Fin n)×Addr (Fin m)) (i : Fin m) :
    pairing x (rod n m (.inr i)) = x.2 i := by simp [pairing]
private def dualKey : Addr (Fin n) × Addr (Fin m) ≃ Addr (Fin (n+m)) where
  toFun := pairing
  invFun x := (fun i=> x (rod n m (.inl i)),fun i=>x (rod n m (.inr i)))
  left_inv x := by exact Prod.ext (funext (pair_l x)) (funext (pair_r x))
  right_inv x := by
    funext i; obtain ⟨i,rfl⟩ := (rod n m).surjective i
    rcases i with i|i
    · exact pair_l ..
    exact pair_r ..
private theorem choice1 (a : Addr (Fin n)) (b : Addr (Fin m)) :
    (layBit _).symm (pairing (a,b)) = (splint _ _).cast ((layBit _).symm a,(layBit _).symm b) := by
  apply (layBit _).injective
  rw [Equiv.apply_symm_apply]
  let x := (layBit _).symm a; let y := (layBit _).symm b
  have z := lightning_b x y
  change _ ∘ _ = Sum.elim ((layBit _) ((layBit _).symm a)) ((layBit _) ((layBit _).symm b)) at z
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at z
  funext i
  obtain ⟨j,rfl⟩ := (rod n m).surjective i
  cases j with
  | inl i => rw [pair_l]; exact (congrFun z (.inl i)).symm
  | inr i => rw [pair_r]; exact (congrFun z (.inr i)).symm

variable {R:Type} [CommRing R] (M : Tensor.Mat B R)
private theorem pairMat (x y : Addr (Fin n) × Addr (Fin m)) :
    mat (fun _ => M) (pairing x) (pairing y) =
    mat (fun _=> M) x.1 y.1 * mat (fun _=> M) x.2 y.2 := by
  simp only [Tensor.app]
  rw [← (rod n m).prod_comp (fun i=> M (pairing x i) (pairing y i)),
    Fintype.prod_sum_type]
  simp only [pair_l,pair_r]

abbrev allMat (n:ℕ) := mat (fun (_:Fin n)=> M)
def doseA (x : medicine p t n m → R) : medicine p t n m → R :=
  fun i=> (Strip.Optic.operate (locker p (Adic.field 2 m++t) n) (allMat M n)
    (x ∘ (fixA ..).cast.symm)) ((fixA ..).cast i)
def doseB (x : medicine p t n m → R) : medicine p t n m → R :=
  fun i=> (Strip.Optic.operate (locker (p++Adic.field 2 n) t m) (allMat M m)
    (x ∘ (fixB ..).cast.symm)) ((fixB ..).cast i)
abbrev tablet {p t n m} (x : medicine p t n m) : Addr (Fin n) × Addr (Fin m) :=
  (layBit _ x.2.1.1,layBit _ x.2.1.2)

theorem medication (x : Base p t (Block 2 (n+m)) → R) (i : medicine p t n m) :
    operate (locker p t _) (allMat M _) x ((heal ..).cast i) =
      doseB M (doseA M (x ∘ (heal ..).cast)) i := by
  let u : Addr (Fin n) × Addr (Fin m) := tablet i
  let a : Fin (n+m)→ B := pairing u
  have eq₀ : let v := locker p t (n+m) ((heal ..).cast i)
             v.1=a := by
    change layBit _ ((splint ..).cast _) = _
    apply (layBit _).symm.injective
    rw [Equiv.symm_apply_apply]
    erw [choice1 (u.1) (u.2)]
    unfold u tablet; rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  let h := heal p t n m
  let f j := allMat M _ a j * x ((locker p t _).symm (j,(i.1,i.2.2)))
  let T (j : Addr (Fin n)) (k : Addr (Fin m)) := x (h.cast (i.1,((layBit _).symm j,(layBit _).symm k),i.2.2))
  have s (x : medicine p t n m → R) (i) : doseA M x i =
      ∑ j,allMat M n (tablet i).1 j * x (i.1,((layBit _).symm j,i.2.1.2),i.2.2) := by
    change ∑ j, allMat M _ _ j*x ((fixA ..).cast.symm ((fixA ..).cast (i.1,((layBit _).symm j,i.2.1.2),i.2.2)))=_
    simp only [Equiv.symm_apply_apply]
    rfl
  have r (x : medicine p t n m → R) (i) : doseB M x i =
      ∑ j,allMat M m (tablet i).2 j * x (i.1,(i.2.1.1,(layBit _).symm j),i.2.2) := by
    change ∑ j, allMat M _ _ j*x ((fixB ..).cast.symm ((fixB ..).cast (i.1,(i.2.1.1,(layBit _).symm j),i.2.2)))=_
    simp only [Equiv.symm_apply_apply]; rfl
  rw [r]; simp_rw [s]
  let v := (locker p t _) ((heal p t n m).cast i)
  change ∑ j,allMat M _ v.1 j * x ((locker p t _).symm (j,(i.1,i.2.2))) =
    ∑ j, allMat M _ u.2 j * (∑ k, allMat M _ u.1 k*T k j)
  erw [eq₀]
  rw [← (dualKey (m:=m) (n:=n)).sum_comp f,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change allMat M _ (pairing u) (pairing (k,j)) *
    x (i.1,(layBit _).symm (pairing (k,j)),i.2.2) = _
  rw [show allMat M _ _ (pairing (k,j)) = _ from pairMat M u (k,j), choice1,
    show T k j = x (i.1,(splint _ _).cast ((layBit _).symm k,(layBit _).symm j),i.2.2) from rfl]
  simp; ring

end
end Earth

end IntegerMultiplication
end Computability
end OAI
