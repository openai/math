import OAI.Hierarchy.DescentTerminalGraphPositions

namespace OAI
/-! # The two ends of a real terminal cable issue identical port-row queries -/
namespace Hierarchy.DescentTerminalGraphPositions.Order
open Computability.BorderVNP.Crossing DescentKernelHistory DescentTerminalGraphRows
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} {N : Network D P bits}
    (L : Order N S p)

omit [Fintype P] in
theorem used_edge (i : Fin S) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p)) :
    Used L i (.inl ⟨e,k⟩) ↔ L.home (N.src e)=i ∨ L.home (N.dst e)=i := by
  constructor
  · rintro ⟨⟨v,hv⟩,⟨l,t⟩,he⟩
    cases l with
    | inl l=>
      have id : l.val=e := congrArg Sigma.fst (Sum.inl.inj he)
      subst e
      exact l.property.imp (fun h=>(congrArg L.home h).trans hv) (fun h=>(congrArg L.home h).trans hv)
    | inr l=>contradiction
  · rintro (h|h)
    · exact ⟨⟨N.src e,h⟩,⟨.inl ⟨e,.inl rfl⟩,k⟩,rfl⟩
    · exact ⟨⟨N.dst e,h⟩,⟨.inl ⟨e,.inr rfl⟩,k⟩,rfl⟩

omit [Fintype P] in
theorem used_port (i : Fin S) (z : P) (k : Fin (poolBatchCount (bits z) p)) :
    Used L i (.inr ⟨z,k⟩) ↔ L.home (N.attach z)=i := by
  constructor
  · rintro ⟨⟨v,hv⟩,⟨l,t⟩,he⟩
    cases l with
    | inl l=>contradiction
    | inr l=>
      have id : l.val=z := congrArg Sigma.fst (Sum.inr.inj he)
      subst z
      exact (congrArg L.home l.property).trans hv
  · exact fun h=>⟨⟨N.attach z,h⟩,⟨.inr ⟨z,rfl⟩,k⟩,rfl⟩

def between (i j : Fin S) (nm : Names N p) := Used L i nm ∧ neighbor L i nm=some j

omit [Fintype P] in
theorem between_edge (i j : Fin S) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p)) :
    between L i j (.inl ⟨e,k⟩) ↔
      (L.home (N.src e)=i ∧ L.home (N.dst e)=j) ∨ (L.home (N.dst e)=i ∧ L.home (N.src e)=j) := by
  simp only [between,used_edge,neighbor,Option.some.injEq]
  by_cases a : L.home (N.src e)=i <;> simp [a]; aesop

omit [Fintype P] in
theorem between_swap (i j : Fin S) (nm : Names N p) : between L i j nm ↔ between L j i nm := by
  rcases nm with ⟨e,k⟩|⟨z,k⟩
  · rw [between_edge,between_edge]; tauto
  · simp [between,neighbor]

/-- The neighboring position always has the reverse group with exactly the same names. -/
def partner {i j : Fin S} (gi : Group L i) (at_j : gi.val=some j) : Group L j := ⟨some i,by
  obtain ⟨nm,use,near⟩:=gi.property
  have rev := (between_swap L i j nm).mp ⟨use,near.trans at_j⟩
  exact ⟨nm,rev⟩⟩

omit [Fintype P] in
theorem partner_val {i j : Fin S} (gi : Group L i) (at_j : gi.val=some j) :
    (partner L gi at_j).val=some i := rfl

def transfer {i j : Fin S} (gi : Group L i) (at_j : gi.val=some j) :
    At L i gi ≃ At L j (partner L gi at_j) where
  toFun nm:=⟨nm.val,(between_swap L i j nm.val).mp ⟨nm.property.1,nm.property.2.trans at_j⟩⟩
  invFun nm:=⟨nm.val,by
    have b:=(between_swap L i j nm.val).mpr nm.property
    exact ⟨b.1,b.2.trans at_j.symm⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

/-- The same increasing global name key gives the same local ordinal at
either endpoint. This includes loops and multiple cables between a site pair. -/
theorem transfer_rank {i j : Fin S} (gi : Group L i) (at_j : gi.val=some j) (nm : At L i gi) :
    (inGroup L j (partner L gi at_j) (transfer L gi at_j nm)).val=(inGroup L i gi nm).val := by
  let g:=partner L gi at_j
  let src:=((Function.Embedding.subtype _).trans L.wireRank : At L i gi ↪ ℕ)
  let dst:=((Function.Embedding.subtype _).trans L.wireRank : At L j g ↪ ℕ)
  have eq : Finset.univ.image dst=Finset.univ.image src := by
    ext k
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨(transfer L gi at_j).symm u,rfl⟩
    · rintro ⟨u,rfl⟩
      exact ⟨transfer L gi at_j u,rfl⟩
  change (Finset.univ.image dst).sort.idxOf (L.wireRank nm.val)=
      (Finset.univ.image src).sort.idxOf (L.wireRank nm.val)
  rw [eq]

theorem partner_slot {i j : Fin S} (gi : Group L i) (at_j : gi.val=some j) (nm : At L i gi)
    (capacity : ℕ) :
    (inGroup L j (partner L gi at_j) (transfer L gi at_j nm)).val / capacity =
      (inGroup L i gi nm).val / capacity ∧
    (inGroup L j (partner L gi at_j) (transfer L gi at_j nm)).val % capacity =
      (inGroup L i gi nm).val % capacity := by
  rw [transfer_rank];exact ⟨rfl,rfl⟩

end
end Hierarchy.DescentTerminalGraphPositions.Order

end OAI
