import OAI.Computability.IntegerMultiplication.Earth.Sea

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Loom Strip Strip.Dims Strip.Optic Adic Net Net.Tensor Net.Walsh Phase Packed Haze
open Matrix Finset
noncomputable section
-- binary mirror using canonical most bit order
abbrev canon (K) := Track (Series.natural 2) K
def bolt : (K : ℕ) → Adopt (canon K) (line 2 K)
| 0 => sealZero _
| K+1 =>
  ((Loom.step (Series.natural 2) K).thenDo ((Adopt.same _).split (bolt K))).thenDo
    (Adopt.turn _ (Dims.hinge ..))

variable {K n m : ℕ} {P T : Tape}
@[simp] theorem lightning (x : Net.Walsh.Addr (Fin K)) :
    layBit K ((bolt K).cast x)=x := by
  induction K with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun i=> ?_) i
    · rfl
    change (most (@Adic.head 2 k (x 0) ((bolt k).cast (fun i : Fin k=>x i.succ))))[i.val+1]'(by rw [Adic.length]; have := i.isLt; omega) = _
    have hlen : (most ((bolt k).cast (fun i : Fin k => x i.succ))).length = k := Adic.length _
    have hl : (x 0 :: most ((bolt k).cast (fun i : Fin k => x i.succ))).length = k+1 := by
      exact congrArg Nat.succ hlen
    change (x 0 :: most ((bolt k).cast (fun i:Fin k=>x i.succ)))[i.val+1]'(by rw [hl]; omega) = _
    have e := congrFun (ih (fun i : Fin k=>x i.succ)) i
    exact e
theorem caught (x : Block 2 K) :
    (bolt K).cast (layBit K x)=x :=
  (layBit K).injective (lightning _)
def equate {A B:Type} {a : Series A} {b : Series B} (e:Adopt a b) :
    (n:ℕ)→Adopt (Track a n) (Track b n)
| 0 => (sealZero _).thenDo (sealZero _).back
| m+1=> ((Loom.step _ _).thenDo (e.split (equate e m))).thenDo (Loom.step _ _).back
theorem installs {A B:Type} {a : Series A} {b : Series B} (e:Adopt a b) (x:Fin n→A) :
    (equate e n).cast x=e.cast ∘ x := by
  induction n with
  | zero=> ext i; exact i.elim0
  | succ n ih =>
    change Loom.join (_, (equate e n).cast _)=_
    rw [ih]
    funext i; refine Fin.cases ?_ (fun i=>?_) i
    · rfl
    exact tail_j ..
def atoms (m k : ℕ) :
    Adopt (Track (line 2 k) m) (line 2 (m*k)) :=
  (equate (bolt k).back m).thenDo ((sheet (Series.natural 2) k m).thenDo (bolt _))
theorem after (x : Fin n → Block 2 K) (i : Fin n) (j : Fin K) :
    (layBit _ ((atoms n K).cast x)) (finProdFinEquiv (i,j))=(layBit _ (x i)) j := by
  change layBit _ ((bolt (n*K)).cast ((sheet (Series.natural 2) K n).cast ((equate _ _).cast _))) _ = _
  have h1 : (layBit (n*K) ((bolt (n*K)).cast ((sheet (Series.natural 2) K n).cast
      ((equate (bolt K).back n).cast x)))) (finProdFinEquiv (i,j)) =
      ((sheet (Series.natural 2) K n).cast ((equate (bolt K).back n).cast x)) (finProdFinEquiv (i,j)) :=
    congrFun (lightning _) _
  have h2 : ((sheet (Series.natural 2) K n).cast ((equate (bolt K).back n).cast x))
      (finProdFinEquiv (i,j)) = ((equate (bolt K).back n).cast x) i j :=
    sheet_no (Series.natural 2) _ i j
  have h3 : ((equate (bolt K).back n).cast x) i j = (layBit K (x i)) j := by
    rw [installs]
    obtain ⟨t,g⟩ := (bolt K).cast.surjective (x i)
    change ((bolt K).cast.symm (x i) j : Fin 2) = _
    rw [← g, Equiv.symm_apply_apply]
    exact (congrFun (lightning t) j).symm
  exact h1.trans (h2.trans h3)

-- correspondence of Mat opera
variable {O J C R Z : Type} [CommRing R] [Fintype O] [Fintype C]
variable [DecidableEq O] [DecidableEq C]
variable (M : Tensor.Mat B R)

def bulb (p t : Tape) (N : ℕ) := Base p t (Block 2 N)
abbrev comfort (P T:Tape) (N : ℕ) := Phase.order P T (line 2 N)
def locker (P T:Tape) (N : ℕ) : Lens (Base P T (Block 2 N)) (Addr (Fin N)) (Pin P × Pin T) where
  toFun x := (layBit _ x.2.1,x.1,x.2.2)
  invFun x := (x.2.1,(layBit _).symm x.1,x.2.2)
  left_inv x := by simp
  right_inv x := by simp
def bulk (P T:Tape) (K n : ℕ) :
    Adopt (rangeK P T K n) (comfort P T (n*K)) :=
  (Adopt.same _).split ((atoms n K).split (Adopt.same _))
theorem handover (x : Base P T (Block 2 (n*K)) → R) :
    let q := bulk P T K n
    operate (locker P T _) (mat (fun _=>M)) x ∘ q.cast =
      operate (file P T K n) (mat (fun _=>M)) (x ∘ q.cast) := by
  dsimp only
  let b := bulk P T K n
  let f := file P T K n
  let l := locker P T (n*K)
  let z : Duo n K≃Fin (n*K) := finProdFinEquiv
  let e : Addr (Fin (n*K)) ≃ Addr (Duo n K) := fromOrder z B
  have g i j : (l (b.cast i)).1 (z j) = (f i).1 j := after i.2.1 j.1 j.2
  have u i : l (b.cast i)=(e.symm (f i).1,(f i).2) := by
    refine Prod.ext (funext fun j=>?_) rfl
    obtain ⟨j,rfl⟩ := z.surjective j
    rw [g]
    change _=(f i).1 (z.symm (z _))
    rw [Equiv.symm_apply_apply]
  have d (i w : Addr (Duo n K)) : mat (fun (_:Fin (n*K))=>M) (e.symm i) (e.symm w)= mat (fun (_:Duo n K)=>M) i w := by
    simp only [Tensor.app]
    let h t := M (e.symm i t) (e.symm w t)
    change ∏ i,h i=_
    rw [← z.prod_comp h]
    unfold h e
    change (∏ t,M (i (z.symm (z t))) (w (z.symm (z t))))=_
    simp
  funext y
  let p := fun i: Addr (Fin (n*K)) => mat (fun _=>M) (l (b.cast y)).1 i*x (l.symm (i,(l (b.cast y)).2))
  change ∑ i,p i=∑ i, (mat (fun _=>M) (f y).1 i)*x (b.cast (f.symm (i,(f y).2)))
  rw [← e.symm.sum_comp p]
  apply Finset.sum_congr rfl
  intro a _
  unfold p
  rw [u]; dsimp only; rw [d] -- rw d
  congr 2
  apply l.injective
  rw [Equiv.apply_symm_apply,u,Equiv.apply_symm_apply]

end
end Earth

end IntegerMultiplication
end Computability
end OAI
