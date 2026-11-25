import OAI.ThreeFlat.Diagonal.RefreshDemandRows
import OAI.ThreeFlat.Diagonal.RefreshStageLayout

namespace OAI
/-! # Exact domains of all contiguous refresh scans -/

namespace ThreeFlat.Diagonal.RefreshStageLayout

open Computability.VPVNP.Compression CompressorPacking.Native RefreshDemandRows

variable {v a t m h pad : ℕ}

/-- The same mixed-radix order used by the RAM's row quotient and remainder. -/
def pair {I J : Type} {i j : ℕ} (u : I ≃ Fin i) (v : J ≃ Fin j) : I × J ≃ Fin (i*j) :=
  (u.prodCongr v).trans finProdFinEquiv

theorem pair_index {I J : Type} {i j : ℕ} (u : I ≃ Fin i) (v : J ≃ Fin j) (x : I × J) :
    (pair u v x).val = (u x.1).val*j+(v x.2).val := by
  change _ + _ * _ = _ * _ + _
  ac_rfl

def blocks : Block v t ≃ Fin (v*2^t) := pair (Equiv.refl _) (tagOrdinal t)

@[simp] theorem block_index (u : Block v t) : (blocks u).val = blockId u :=
  pair_index _ _ u

def oldGraphRows : Fin v × Fin m ≃ Fin (v*m) := pair (Equiv.refl _) (Equiv.refl _)

def newGraphRows : (Fin v × Fin m) × Fin (1+h+pad) ≃ Fin (v*m*(1+h+pad)) :=
  pair oldGraphRows (Equiv.refl _)

def oldWords : Address' v a t ≃ Fin ((counts v (mPort a) (2^t) h pad).oldWidthSpan) :=
  let reorder : Address' v a t ≃ (Fin v × Fin (mPort a)) × (BitWord t × Fin (mPort a)) :=
    { toFun := fun ⟨⟨v,l⟩,i,s⟩ => ((v,s),(l,i))
      invFun := fun ⟨⟨v,s⟩,l,i⟩ => ((v,l),i,s)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  (reorder.trans (pair oldGraphRows (pair (tagOrdinal t) (Equiv.refl _)))).trans
    (finCongr (by dsimp [counts]; ac_rfl))

@[simp] theorem old_index (x : Address' v a t) : (oldWords (h:=h) (pad:=pad) x).val = index x := by
  obtain ⟨⟨v,l⟩,i,s⟩ := x
  change (pair oldGraphRows (pair (tagOrdinal t) (Equiv.refl _)) ((v,s),(l,i))).val = _
  simp only [pair_index,oldGraphRows,Equiv.refl_apply,index,ordinal]
  ac_rfl

def newWords : ((Fin v × Fin m) × Fin (1+h+pad)) × BitWord t ≃
    Fin ((counts v m (2^t) h pad).newWidthSpan) := pair newGraphRows (tagOrdinal t)

@[simp] theorem new_index (x : ((Fin v × Fin m) × Fin (1+h+pad)) × BitWord t) :
    (newWords x).val = ((x.1.1.1.val*m+x.1.1.2.val)*(1+h+pad)+x.1.2.val)*2^t+(tagOrdinal t x.2).val := by
  calc
    _ = (newGraphRows x.1).val*2^t+(tagOrdinal t x.2).val :=
      pair_index newGraphRows (tagOrdinal t) x
    _ = ((oldGraphRows x.1.1).val*(1+h+pad)+x.1.2.val)*2^t+(tagOrdinal t x.2).val :=
      congrArg (fun i : ℕ => i*2^t+(tagOrdinal t x.2).val)
        (pair_index oldGraphRows (Equiv.refl _) x.1)
    _ = _ := congrArg (fun i : ℕ => (i*(1+h+pad)+x.1.2.val)*2^t+(tagOrdinal t x.2).val)
      (pair_index (Equiv.refl _) (Equiv.refl _) x.1.1)

def splitEntries : Fin 3 × (Fin v × Fin m) ≃ Fin ((counts v m (2^t) h pad).splitSpan) :=
  pair (Equiv.refl _) oldGraphRows

def descriptorEntries : Block v t × Fin 3 ≃ Fin ((counts v m (2^t) h pad).choiceSpan) :=
  (pair blocks (Equiv.refl _)).trans (finCongr (Nat.mul_comm _ _))

def adjacencyEntries : Fin 6 × ((Fin v × Fin m) × Fin (1+h+pad)) ≃
    Fin ((counts v m (2^t) h pad).graphSpan) := pair (Equiv.refl _) newGraphRows

def sparseEntries : (Block v t × Fin m) × Fin h ≃ Fin ((counts v m (2^t) h pad).sparseSpan) :=
  pair (pair blocks (Equiv.refl _)) (Equiv.refl _)

@[simp] theorem descriptor_index (u : Block v t) (j : Fin 3) :
    (descriptorEntries (m:=m) (h:=h) (pad:=pad) (u,j)).val=blockId u*3+j.val := by
  change (pair blocks (Equiv.refl _) (u,j)).val=_
  rw [pair_index,block_index]; rfl

@[simp] theorem sparse_index (u : Block v t) (p : Fin m) (s : Fin h) :
    (sparseEntries (pad:=pad) ((u,p),s)).val=(blockId u*m+p.val)*h+s.val := by
  calc
    _ = (pair blocks (Equiv.refl _) (u,p)).val*h+s.val :=
      pair_index (pair blocks (Equiv.refl _)) (Equiv.refl _) ((u,p),s)
    _ = ((blocks u).val*m+p.val)*h+s.val :=
      congrArg (fun i : ℕ => i*h+s.val) (pair_index blocks (Equiv.refl _) (u,p))
    _ = _ := congrArg (fun i : ℕ => (i*m+p.val)*h+s.val) (block_index u)

end ThreeFlat.Diagonal.RefreshStageLayout

end OAI
