import OAI.ThreeFlat.BitNetwork.CopyTables
import OAI.ThreeFlat.FoldInput
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Explicit linear-size names for every trivalent copy site and wire -/

namespace ThreeFlat.RawTick

open BitNetwork
noncomputable section
variable {F : Type*} {p h : ℕ} (N : BitNetwork F p)

abbrev sources (hidden pins : ℕ) := 2+(pins+hidden)
abbrev sockets (cells : ℕ) := cells*3
abbrev sites (cells hidden pins : ℕ) :=
  cells+(sources hidden pins+(sockets cells+sources hidden pins))
abbrev edges (cells hidden pins : ℕ) := sources hidden pins+(sockets cells+sockets cells)

private def sourceParts : BitSource h p ≃ Bool ⊕ (Fin p ⊕ Fin h) where
  toFun
    | .constant b => .inl b
    | .pin i => .inr (.inl i)
    | .hidden i => .inr (.inr i)
  invFun
    | .inl b => .constant b
    | .inr (.inl i) => .pin i
    | .inr (.inr i) => .hidden i
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | (_|_) <;> rfl

def sourceIndex : BitSource h p ≃ Fin (sources h p) :=
  sourceParts.trans ((Equiv.sumCongr FoldInput.flagIndex finSumFinEquiv).trans finSumFinEquiv)

theorem sourceIndex_val (s : BitSource h p) : (sourceIndex s).val = RAM.BitLayout.sourceAddress s := by
  cases s with
  | hidden i => change 2+(p+i.val)=(2+p)+i.val; omega
  | pin i => rfl
  | constant b => cases b <;> rfl

abbrev Key := Σ s : N.Source, Fin (N.arity s)

def socketKey : N.Socket ≃ (Key N) :=
  (Equiv.sigmaFiberEquiv N.address).symm.trans (Equiv.sigmaCongrRight N.socketOrder)

@[simp] theorem socketKey_socketAt (s : N.Source) (j : Fin (N.arity s)) :
    socketKey N (N.socketAt s j)=⟨s,j⟩ := (socketKey N).apply_symm_apply ⟨s,j⟩

private def midIndex : (Key N) ≃ Fin (sockets N.cells) := (socketKey N).symm.trans finProdFinEquiv

abbrev Parts := N.Source ⊕ ((Key N) ⊕ N.Source)
abbrev Trunk := N.Source ⊕ (Key N)

private def parts : (Σ s : N.Source, Fin (N.arity s+2)) ≃ Parts N where
  toFun := fun ⟨s,i⟩ => Fin.cases (.inl s)
    (Fin.lastCases (.inr (.inr s)) (fun j => .inr (.inl ⟨s,j⟩))) i
  invFun
    | .inl s => ⟨s,0⟩
    | .inr (.inl ⟨s,j⟩) => ⟨s,j.castSucc.succ⟩
    | .inr (.inr s) => ⟨s,(Fin.last (N.arity s)).succ⟩
  left_inv := by
    rintro ⟨s,i⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ j => induction j using Fin.lastCases <;> simp only [Fin.cases_succ,Fin.lastCases_last,Fin.lastCases_castSucc]
  right_inv := by rintro (s | (⟨s,j⟩ | s)) <;> simp only [Fin.cases_zero,Fin.cases_succ,Fin.lastCases_castSucc,Fin.lastCases_last]

private def trunkParts : (Σ s : N.Source, Fin (N.arity s+1)) ≃ Trunk N where
  toFun := fun ⟨s,i⟩ => Fin.cases (.inl s) (fun j => .inr ⟨s,j⟩) i
  invFun
    | .inl s => ⟨s,0⟩
    | .inr ⟨s,j⟩ => ⟨s,j.succ⟩
  left_inv := by rintro ⟨s,i⟩; induction i using Fin.cases <;> simp
  right_inv := by rintro (s | ⟨s,j⟩) <;> simp

/-- Cells, roots, socket equality sites, and terminals occupy consecutive intervals. -/
def siteIndex : N.CopySite ≃ Fin (sites N.cells N.internal p) :=
  let tail := ((midIndex N).sumCongr sourceIndex).trans finSumFinEquiv
  let chain := (parts N).trans ((sourceIndex.sumCongr tail).trans finSumFinEquiv)
  ((Equiv.refl _).sumCongr chain).trans finSumFinEquiv

/-- Every root and socket has an outgoing trunk. The last interval consists of spokes. -/
def edgeIndex : N.CopyEdge ≃ Fin (edges N.cells N.internal p) :=
  let pair := ((midIndex N).sumCongr finProdFinEquiv).trans finSumFinEquiv
  ((trunkParts N).sumCongr (Equiv.refl _)).trans <|
    (Equiv.sumAssoc _ _ _).trans ((sourceIndex.sumCongr pair).trans finSumFinEquiv)


def ordinal (u : N.Socket) := (finProdFinEquiv u).val

theorem ordinal_val (u : N.Socket) : ordinal N u = 3*u.1.val+u.2.val := by
  change u.2.val+3*u.1.val=_
  omega

@[simp] theorem site_cell (i : Fin N.cells) : (siteIndex N (.inl i)).val=i.val := rfl

@[simp] theorem site_root (s : N.Source) :
    (siteIndex N (.inr ⟨s,0⟩)).val=N.cells+(sourceIndex s).val := rfl

@[simp] theorem site_middle (s : N.Source) (j : Fin (N.arity s)) :
    (siteIndex N (.inr ⟨s,j.castSucc.succ⟩)).val =
      N.cells+(sources N.internal p+ordinal N (N.socketAt s j)) := by
  simp [siteIndex,parts,midIndex,ordinal,socketKey,BitNetwork.socketAt]; rfl

@[simp] theorem site_tail (s : N.Source) :
    (siteIndex N (.inr ⟨s,(Fin.last (N.arity s)).succ⟩)).val =
      N.cells+(sources N.internal p+(sockets N.cells+(sourceIndex s).val)) := by
  simp [siteIndex,parts,-Fin.succ_last]

@[simp] theorem edge_root (s : N.Source) :
    (edgeIndex N (.inl ⟨s,0⟩)).val=(sourceIndex s).val := rfl

@[simp] theorem edge_middle (s : N.Source) (j : Fin (N.arity s)) :
    (edgeIndex N (.inl ⟨s,j.succ⟩)).val =
      sources N.internal p+ordinal N (N.socketAt s j) := by
  simp [edgeIndex,trunkParts,midIndex,ordinal,socketKey,BitNetwork.socketAt]; rfl

@[simp] theorem edge_spoke (u : N.Socket) :
    (edgeIndex N (.inr u)).val=sources N.internal p+(sockets N.cells+ordinal N u) := rfl

end
end ThreeFlat.RawTick

end OAI
