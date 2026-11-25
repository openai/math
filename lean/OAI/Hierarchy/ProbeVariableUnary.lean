import OAI.ThreeFlat.Diagonal.MotifCountCheck
import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Tactic.FinCases

namespace OAI
/-! # A trivalent binary count check at the unique boundary of a unary stream -/

noncomputable section
namespace Hierarchy.Probe.VariableUnary
open ThreeFlat Routing Diagonal.MotifOuterTerms
open scoped BigOperators Classical

abbrev Pins (r b : ℕ) := Fin r ⊕ Fin b
abbrev Check (r b : ℕ) := Fin (r+1) × Fin b

def before {r : ℕ} (u : Fin r→Bool) (i : Fin (r+1)) : Bool :=
  if l : 0 < i.val then u ⟨i.val-1,by have:=i.isLt;omega⟩ else true

def following {r : ℕ} (u : Fin r→Bool) (i : Fin (r+1)) : Bool :=
  if l : i.val < r then u ⟨i.val,l⟩ else false

def source (r b : ℕ) (test : Check r b) : Fin 3→BitSource 0 (Fintype.card (Pins r b)) :=
  ![if lo : 0 < test.1.val then .pin (Fintype.equivFin _ (Sum.inl (⟨test.1.val-1,by have:=test.1.isLt;omega⟩ : Fin r))) else .constant true,
    if hi : test.1.val < r then .pin (Fintype.equivFin _ (Sum.inl (⟨test.1.val,hi⟩ : Fin r))) else .constant false,
    .pin (Fintype.equivFin _ (Sum.inr test.2))]

def network (F : Type*) [Zero F] [One F] (r b : ℕ) : BitNetwork F (Fintype.card (Pins r b)) where
  cells:=Fintype.card (Check r b)
  internal:=0
  source t:=source r b ((Fintype.equivFin _).symm t)
  table t z:=let x:=(Fintype.equivFin (Check r b)).symm t
             if z 0=true ∧ z 1=false → z 2=x.1.val.testBit x.2.val then 1 else 0

theorem size (F : Type*) [Zero F] [One F] (r b : ℕ) :
    (network F r b).cells+(network F r b).internal=(r+1)*b := by simp [network,Check]

private theorem sources {r b : ℕ} (t : Check r b) (u : Fin r→Bool) (c : Fin b→Bool)
    (bits : Fin 0→Bool) :
    (fun i=>(source r b t i).read bits ((Sum.elim u c) ∘ (Fintype.equivFin _).symm)) =
      ![before u t.1,following u t.1,c t.2] := by
  funext j
  fin_cases j <;> simp [source,before,following,BitSource.read] <;>
    split_ifs <;> simp

theorem eval (F : Type*) [CommSemiring F] {r b : ℕ} (u : Fin r→Bool) (c : Fin b→Bool) :
    TypedWiring.value (network F r b) (Sum.elim u c)=
      if ∀(i : Fin (r+1)) (j : Fin b),before u i=true ∧ following u i=false →
        c j=i.val.testBit j.val then 1 else 0 := by
  classical
  let accept (t : Check r b) := before u t.1 = true ∧ following u t.1 = false →
    c t.2 = t.1.val.testBit t.2.val
  let numbered (i : Fin (Fintype.card (Check r b))) := accept ((Fintype.equivFin _).symm i)
  have cell (h : Fin 0 → Bool) (i : Fin (Fintype.card (Check r b))) :
      (network F r b).factor ((Sum.elim u c) ∘ (Fintype.equivFin _).symm) h i =
        if numbered i then 1 else 0 := by
    let t := (Fintype.equivFin (Check r b)).symm i
    change (network F r b).table i (fun j => (source r b t j).read h _) = _
    rw [sources]
    rfl
  unfold TypedWiring.value BitNetwork.eval BitNetwork.weight
  change (∑ h : Fin 0 → Bool, ∏ i : Fin (Fintype.card (Check r b)),
    (network F r b).factor ((Sum.elim u c) ∘ (Fintype.equivFin _).symm) h i) = _
  simp only [cell, Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    pow_zero,one_nsmul]
  have same : (∀ i, numbered i) ↔ ∀ (i : Fin (r+1)) (j : Fin b), accept (i,j) := by
    constructor
    · intro h i j
      simpa only [numbered, Equiv.symm_apply_apply] using h (Fintype.equivFin _ (i,j))
    · intro h i
      exact h _ _
  change (∏ i, if numbered i then (1:F) else 0) = (if ∀ i j, accept (i,j) then 1 else 0)
  by_cases all : ∀ i, numbered i
  · rw [ite_eq_left (same.mp all)]
    exact Finset.prod_eq_one (fun i _ => ite_eq_left (all i))
  · rw [ite_eq_right (fun h => all (same.mpr h))]
    obtain ⟨i, no⟩ := not_forall.mp all
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right no)

private theorem edge {r : ℕ} (n i : Fin (r+1)) :
    before (unary n.val) i=true ∧ following (unary n.val) i=false ↔ i=n := by
  have ib := i.isLt
  have nb := n.isLt
  simp only [before,following,unary]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

/-- A real stable compactor publishes exactly one boundary. The same three-pin
network reads any target counter, regardless of the actual target value. -/
theorem eval_count (F : Type*) [CommSemiring F] {r b : ℕ} (n : Fin (r+1)) (c : Fin b→Bool) :
    TypedWiring.value (network F r b) (Sum.elim (unary n.val) c)=
      if c=(fun j=>n.val.testBit j.val) then 1 else 0 := by
  rw [eval]
  congr 1
  apply propext
  simp only [edge]
  exact ⟨fun all=>funext (fun j=>all n j rfl),fun eq i j hi=>by simp [eq,hi]⟩

end Hierarchy.Probe.VariableUnary
end

end OAI
