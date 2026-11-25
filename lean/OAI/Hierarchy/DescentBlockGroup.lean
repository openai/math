import OAI.Hierarchy.DescentPhysicalSubround

namespace OAI
/-! # Independent copies with different prior histories placed in one physical group -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {I : Type} [Fintype I] {F : Type*} [Field F] {D : ℕ} {P : I → Type*}
variable {bits : ∀i,P i → ℕ} (A : ∀i,World F D (P i) (bits i))

def blockGraph : Network D (Σi,P i) (fun p => bits p.1 p.2) where
  Site := Σi,(A i).graph.Site
  Edge := Σi,(A i).graph.Edge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := ⟨e.1,(A e.1).graph.src e.2⟩
  dst e := ⟨e.1,(A e.1).graph.dst e.2⟩
  width e := (A e.1).graph.width e.2
  attach p := ⟨p.1,(A p.1).graph.attach p.2⟩
  position u := (A u.1).graph.position u.2
  in_ball u := (A u.1).graph.in_ball u.2

def blockAssign : (∀i,(A i).graph.Assignment) ≃ (blockGraph A).Assignment where
  toFun z e := z e.1 e.2
  invFun z i e := z ⟨i,e⟩
  left_inv _ := rfl
  right_inv _ := rfl

def blockTables : (blockGraph A).Tables F := fun ⟨i,v⟩ e p =>
  (A i).tables v
    (fun ⟨j,h⟩ => e ⟨⟨i,j⟩,h.imp (congrArg (Sigma.mk i)) (congrArg (Sigma.mk i))⟩)
    (fun ⟨j,h⟩ => p ⟨⟨i,j⟩,congrArg (Sigma.mk i) h⟩)

def blockGroup : World F D (Σi,P i) (fun p => bits p.1 p.2) := ⟨blockGraph A,blockTables A⟩

omit [Field F] in
theorem same_block (e : (blockGraph A).Edge) :
    ((blockGraph A).src e).1=((blockGraph A).dst e).1 := rfl

theorem block_value (x : Ports (fun p : Σi,P i => bits p.1 p.2)) :
    (blockGroup A).value x=∏i,(A i).value (fun p => x ⟨i,p⟩) := by
  classical
  unfold World.value Network.value
  rw [Fintype.prod_sum]
  let term (a : (blockGraph A).Assignment) : F :=
    ∏ v, (blockGraph A).read (blockTables A) a x v
  refine ((blockAssign A).sum_comp term).symm.trans ?_
  apply Finset.sum_congr rfl
  intro a _
  let factor (v : Σ i, (A i).graph.Site) :=
    (blockGraph A).read (blockTables A) (blockAssign A a) x v
  exact (Fintype.prod_sigma factor).trans (by rfl)

omit [Field F] in
theorem block_sites : Fintype.card (blockGraph A).Site=∑i,Fintype.card (A i).graph.Site :=
  Fintype.card_sigma

omit [Field F] in
theorem block_width : (blockGroup A).coreWidth=∑i,(A i).coreWidth := Fintype.sum_sigma _

/-- Set aside all noncore tethers before the next common-group replacement. -/
def blockCore (core : ∀i,Finset (A i).graph.Edge) : Finset (blockGraph A).Edge :=
  Finset.univ.sigma core

omit [Field F] in
@[simp] theorem mem_blockCore (core : ∀i,Finset (A i).graph.Edge) (i : I) (e : (A i).graph.Edge) :
    (⟨i,e⟩ : (blockGraph A).Edge)∈blockCore A core ↔ e∈core i := by
  change (⟨i,e⟩ : Σ j,(A j).graph.Edge) ∈ Finset.univ.sigma core ↔ e∈core i
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]

omit [Field F] in
theorem block_core_width (core : ∀i,Finset (A i).graph.Edge) :
    (∑e∈blockCore A core,(blockGraph A).width e)=∑i,∑e∈core i,(A i).graph.width e := by
  exact Finset.sum_sigma ..

end
end Hierarchy.DescentSixParty

end OAI
