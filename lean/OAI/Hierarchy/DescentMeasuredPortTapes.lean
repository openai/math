import OAI.Hierarchy.DescentMeasuredNeighborRows
import OAI.Hierarchy.DescentPackedExchange

namespace OAI
/-! # Concrete sparse row headers sharing the actual native adjacency tape -/
namespace Hierarchy.DescentMeasuredWeights
open DescentColonies DescentPackedExchange DescentGL
open scoped Classical BigOperators
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {H Δ k : ℕ}
variable (idx : V≃Fin H) (near : V→Finset V) (cap : ∀v,(near v).card≤Δ)

def atPort : Contacts near ↪ Port H Δ where
  toFun c:=(idx c.1,⟨((neighborOrder idx (near c.1)) c.2).val,
    ((neighborOrder idx (near c.1)) c.2).isLt.trans_le (by simpa using cap c.1)⟩)
  inj':=by
    rintro ⟨a,s⟩ ⟨b,t⟩ he
    obtain rfl : a=b:=idx.injective (congrArg Prod.fst he)
    obtain rfl : s=t := (neighborOrder idx (near a)).injective
      (Fin.ext (congrArg (fun p : Port H Δ=>p.2.val) he))
    rfl

omit [DecidableEq V] in
theorem atPort_read (c : Contacts near) :
    neighborSlot idx near (atPort idx near cap c)=some (idx c.2.val) := by
  rcases c with ⟨v,u⟩
  let rank := neighborOrder idx (near v) u
  change (if hi : rank.val < Fintype.card (near (idx.symm (idx v))) then
    some (idx (((neighborOrder idx (near (idx.symm (idx v)))).symm ⟨rank.val,hi⟩).val))
    else none) = some (idx u.val)
  rw [Equiv.symm_apply_apply,dite_eq_left rank.isLt]
  exact congrArg (fun z : ↥(near v) => some (idx z.val))
    ((neighborOrder idx (near v)).symm_apply_apply u)

omit [DecidableEq V] in
theorem unlisted (p : Port H Δ) (idle : ¬∃c,atPort idx near cap c=p) :
    neighborSlot idx near p=none := by
  rcases p with ⟨v,j⟩
  change (if hi : j.val < Fintype.card (near (idx.symm v)) then
    some (idx (((neighborOrder idx (near (idx.symm v))).symm ⟨j.val,hi⟩).val))
    else none) = none
  split
  · rename_i small
    let c : Contacts near := ⟨idx.symm v,(neighborOrder idx (near (idx.symm v))).symm ⟨j.val,small⟩⟩
    apply False.elim
    apply idle
    refine ⟨c,Prod.ext (idx.apply_symm_apply v) (Fin.ext ?_)⟩
    exact congrArg (fun rank : Fin (Fintype.card (near (idx.symm v))) => rank.val)
      ((neighborOrder idx (near (idx.symm v))).apply_symm_apply ⟨j.val,small⟩)
  · rfl

def portRow (b : V→ℕ) :=
  rectangle (k:=k) idx (inputLevels (k:=k) b)
    (fun v=>Nat.add_le_add_right (Nat.sub_le k (b v)) 1) (atPort idx near cap)

abbrev Rows (H k Δ : ℕ) := Fin H×Fin (k+1) ⊕ Port H Δ
def rowOrd (H k Δ : ℕ) : Rows H k Δ≃Fin (H*(k+1)+H*Δ) :=
  (finProdFinEquiv.sumCongr (slot H Δ)).trans finSumFinEquiv

omit [Fintype V] [DecidableEq V] in
theorem site_row (b : V→ℕ) (v : V) (s : Fin (inputLevels (k:=k) b v)) :
    portRow idx near cap b (.inl ⟨v,s⟩)=rowOrd H k Δ (.inl (idx v,⟨s.val,by have:=s.isLt;dsimp [inputLevels] at *;omega⟩)) := rfl

omit [Fintype V] [DecidableEq V] in
theorem port_row (b : V→ℕ) (c : Contacts near) :
    portRow (k:=k) idx near cap b (.inr c)=rowOrd H k Δ (.inr (atPort idx near cap c)) := rfl

def realDepth (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H)) : Rows H k Δ→ℕ
  | .inl (v,z)=>if b v+z.val≤k then b v+z.val else 0
  | .inr p=>(next p).elim 0 (fun u=>max (b p.1) (b u))

def realGain (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H)) (f B K : ℕ) : Rows H k Δ→ℕ
  | .inl (v,z)=>if b v+z.val≤k then 2^f*B*(4*2^((z.val+7)/8)) else 0
  | .inr p=>(next p).elim 0 (fun _=>2^f*B*K^2)

def realLoad (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H))
    (sites : Fin H→Bits k→ℕ) (traffic : Port H Δ→Bits k→ℕ) : Rows H k Δ→Bits k→ℕ
  | .inl (v,z)=>if b v+z.val≤k then sites v else fun _=>0
  | .inr p=>(next p).elim (fun _=>0) (fun _=>traffic p)

end
end Hierarchy.DescentMeasuredWeights

end OAI
