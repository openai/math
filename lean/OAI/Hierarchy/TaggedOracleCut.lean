import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Tactic

namespace OAI
/-! # Cutting a tag occurrence out of a wired contraction

The exposed bits are pinned to their original wire sources by equality gates.
They are therefore uniquely determined by the other hidden data. Contraction
with an arbitrary tensor on the cut is precisely its original occurrence in
the multilinear product.
-/

namespace Hierarchy.Tagged.OracleCut

open ThreeFlat Routing
open scoped BigOperators Classical
noncomputable section

variable {F P I : Type*} [Fintype P] [Fintype I] {r : I → ℕ} {q z : ℕ}

private def lift (s : BitSource z (Fintype.card P)) : BitSource z (Fintype.card (P ⊕ Fin q)) :=
  match s with
  | .hidden i => .hidden i
  | .constant b => .constant b
  | .pin i => .pin (Fintype.equivFin _ (.inl ((Fintype.equivFin _).symm i)))

private theorem read_lift (x : P → Bool) (cut : Fin q → Bool) (h : Fin z → Bool)
    (s : BitSource z (Fintype.card P)) :
    (lift s).read h (Sum.elim x cut ∘ (Fintype.equivFin _).symm) =
      s.read h (x ∘ (Fintype.equivFin _).symm) := by
  cases s <;> simp [lift, BitSource.read]

abbrev arity (r : I → ℕ) (g : I ⊕ Fin q) := g.elim r (fun _ => 2)

private def parts [Zero F] [One F] (N : (i : I) → BitNetwork F (r i)) :
    (g : I ⊕ Fin q) → BitNetwork F (arity r g)
  | .inl i => N i
  | .inr _ => TableCompiler.localTableNetwork (fun (v : Fin 2 → Bool) => if v 0 = v 1 then (1:F) else 0)

private def wires (wire : (i : I) → Fin (r i) → BitSource z (Fintype.card P))
    (feed : Fin q → BitSource z (Fintype.card P)) :
    (g : I ⊕ Fin q) → Fin (arity r g) → BitSource z (Fintype.card (P ⊕ Fin q))
  | .inl i, j => lift (wire i j)
  | .inr i, j => if j.val = 0 then lift (feed i) else .pin (Fintype.equivFin _ (.inr i))

def network [Zero F] [One F] (N : (i : I) → BitNetwork F (r i))
    (wire : (i : I) → Fin (r i) → BitSource z (Fintype.card P))
    (feed : Fin q → BitSource z (Fintype.card P)) : BitNetwork F (Fintype.card (P ⊕ Fin q)) :=
  BitNetwork.glue (parts N) (wires wire feed)

theorem value [CommSemiring F] (N : (i : I) → BitNetwork F (r i))
    (wire : (i : I) → Fin (r i) → BitSource z (Fintype.card P))
    (feed : Fin q → BitSource z (Fintype.card P)) (x : P → Bool) (cut : Fin q → Bool) :
    TypedWiring.value (network N wire feed) (Sum.elim x cut) =
      ∑ h : Fin z → Bool, (∏ i, (N i).eval (fun j => (wire i j).read h (x ∘ (Fintype.equivFin _).symm))) *
        if (fun j => (feed j).read h (x ∘ (Fintype.equivFin _).symm)) = cut then 1 else 0 := by
  let outer := Sum.elim x cut ∘ (Fintype.equivFin (P ⊕ Fin q)).symm
  have bit (h : Fin z → Bool) (i : Fin q) :
      (parts N (.inr i)).eval (fun j => (wires wire feed (.inr i) j).read h outer) =
        if (feed i).read h (x ∘ (Fintype.equivFin _).symm) = cut i then 1 else 0 := by
    let pin : Fin 2 → Bool := fun j => (wires wire feed (.inr i) j).read h outer
    let test := fun v : Fin 2 → Bool => if v 0=v 1 then (1:F) else 0
    have left : pin 0 = (feed i).read h (x ∘ (Fintype.equivFin _).symm) := read_lift x cut h (feed i)
    have right : pin 1 = cut i := by
      simp [pin,wires,BitSource.read,outer,Function.comp_def]
    change (TableCompiler.localTableNetwork test).eval pin = _
    calc
      _ = test pin := TableCompiler.localTableNetwork_eval test pin
      _ = _ := by simp only [test,left,right]
  change (network N wire feed).eval outer = _
  rw [network,BitNetwork.glue_eval]
  simp only [Fintype.prod_sum_type]
  simp only [bit]
  simp [parts,wires,outer,read_lift,Fintype.prod_boole,funext_iff]

/-- Plugging any coefficient tensor into the cut inserts exactly one factor. -/
theorem contract [CommSemiring F] (N : (i : I) → BitNetwork F (r i))
    (wire : (i : I) → Fin (r i) → BitSource z (Fintype.card P))
    (feed : Fin q → BitSource z (Fintype.card P)) (x : P → Bool) (f : (Fin q → Bool) → F) :
    (∑ cut : Fin q → Bool, TypedWiring.value (network N wire feed) (Sum.elim x cut) * f cut) =
      ∑ h : Fin z → Bool, (∏ i, (N i).eval (fun j => (wire i j).read h (x ∘ (Fintype.equivFin _).symm))) *
        f (fun j => (feed j).read h (x ∘ (Fintype.equivFin _).symm)) := by
  simp only [value, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp [mul_ite]

theorem size [Zero F] [One F] (N : (i : I) → BitNetwork F (r i))
    (wire : (i : I) → Fin (r i) → BitSource z (Fintype.card P))
    (feed : Fin q → BitSource z (Fintype.card P)) :
    (network N wire feed).cells + (network N wire feed).internal =
      (∑ i, (N i).cells) + (∑ i, (N i).internal) + z + 28*q := by
  simp [network, parts, TableCompiler.localTableNetwork_cells,
    TableCompiler.localTableNetwork_internal, Fintype.sum_sum_type]
 ; omega

end
end Hierarchy.Tagged.OracleCut

end OAI
