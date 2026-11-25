import OAI.Hierarchy.CorrectionFrame
import OAI.ThreeFlat.BitNetwork.CopyTables
import OAI.ThreeFlat.BitNetwork.CopyDegree
import OAI.ThreeFlat.BitNetwork.PinMap
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Exposed catalyst ports for independent rows

Rows use the same direction coordinates. Numbering their individual through
bits inside each direction gives exactly the physical batch format.
-/

noncomputable section
namespace Hierarchy.CorrectionBatch

open ThreeFlat Routing Catalyst CorrectionFrame
open scoped BigOperators Classical

variable {s k p : ℕ} {F : Type*} [Field F]

private def wireEquiv (s : ℕ) (b : Fin k → ℕ) : (Fin s × Wire b) ≃ Wire (copiesWidth s b) where
  toFun | (i,⟨j,w⟩) => ⟨j,finProdFinEquiv (i,w)⟩
  invFun | ⟨j,w⟩ => ((finProdFinEquiv.symm w).1,⟨j,(finProdFinEquiv.symm w).2⟩)
  left_inv := by rintro ⟨i,j,w⟩; simp
  right_inv := by
    rintro ⟨j,w⟩
    exact congrArg (Sigma.mk j) ((finProdFinEquiv (m:=s) (n:=b j)).apply_symm_apply w)

private theorem port_data (b : Fin k → ℕ) (i : Fin s) (j : Fin p) :
    copiesPortEquiv (p:=p) s b (i,.inl j) = .inl (finProdFinEquiv (i,j)) := rfl

private theorem port_wire (b : Fin k → ℕ) (i : Fin s) (w : Wire b) (u : Bool) :
    copiesPortEquiv (p:=p) s b (i,.inr (w,u)) = .inr (wireEquiv s b (i,w),u) := by
  rcases w with ⟨j,w⟩
  rfl

theorem ideal_power (b : Fin k → ℕ) (f : (Fin p → Bool) → F)
    (x : Port (s*p) (copiesWidth s b) → Bool) :
    ideal (copiesWidth s b) (dataProduct s f) x =
      ∏ i : Fin s, ideal b f (fun j => x (copiesPortEquiv (p:=p) s b (i,j))) := by
  let eqn (v : Wire (copiesWidth s b)) := x (.inr (v,false)) = x (.inr (v,true))
  change (if ∀ v, eqn v then _ else _) = _
  by_cases all : ∀ v, eqn v
  · rw [ite_eq_left all]
    apply Finset.prod_congr rfl
    intro i _
    have ok : ∀ w : Wire b,
        x (copiesPortEquiv (p:=p) s b (i,.inr (w,false))) =
        x (copiesPortEquiv (p:=p) s b (i,.inr (w,true))) := by
      intro w
      simpa only [port_wire,eqn] using all (wireEquiv s b (i,w))
    rw [ideal,ite_eq_left ok]; rfl
  · obtain ⟨bad,hbad⟩ := Classical.not_forall.mp all
    obtain ⟨⟨i,w⟩,rfl⟩ := (wireEquiv s b).surjective bad
    rw [ite_eq_right all]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply ite_eq_right
    intro h
    exact hbad (by simpa only [port_wire,eqn] using h w)

private def numbering (b : Fin k → ℕ) (i : Fin (Fintype.card (Fin s × Port p b))) :
    Option (Fin (Fintype.card (Port (s*p) (copiesWidth s b)))) :=
  some (Fintype.equivFin _ (copiesPortEquiv (p:=p) s b ((Fintype.equivFin _).symm i)))

/-- Readdress the external pins of a row-indexed circuit in the catalyst
format, preserving every cell and summed internal bit. -/
def package (b : Fin k → ℕ) (A : BitNetwork F (Fintype.card (Fin s × Port p b))) :
    Approximation F k (s*p) := ⟨copiesWidth s b,A.restrictPins (numbering b)⟩

theorem coeff_package (b : Fin k → ℕ) (A : BitNetwork F (Fintype.card (Fin s × Port p b)))
    (x : Port (s*p) (copiesWidth s b) → Bool) :
    (package b A).coeff x = TypedWiring.value A (x ∘ copiesPortEquiv (p:=p) s b) := by
  unfold Approximation.coeff package TypedWiring.value
  rw [BitNetwork.restrictPins_eval]
  simp only [numbering,Option.map_some,Equiv.symm_apply_apply,Option.getD_some,Function.comp_def]

omit [Field F] in
theorem size_package (b : Fin k → ℕ) (A : BitNetwork F (Fintype.card (Fin s × Port p b))) :
    (package b A).size = A.cells+A.internal+s*Fintype.card (Port p b) := by
  have ports := Fintype.card_congr (copiesPortEquiv (p:=p) s b)
  simp only [Fintype.card_prod,Fintype.card_fin] at ports
  exact congrArg (A.cells+A.internal+·) ports.symm

/-- Physical equality-copy trees make every incidence trivalent, including an
external bit read by many modules. Their volume counts every open bit. -/
theorem physical_output (Y : Approximation F k p) :
    Y.network.copyGraph.Trivalent ∧ Y.network.copyGraph.bitVolume ≤ 10*(Y.size+1) ∧
    ∀ x : Port p Y.width → Bool,
      Y.network.copyGraph.value Y.network.copyTable
        (fun q _ => x ((Fintype.equivFin _).symm q)) = Y.coeff x :=
  ⟨Y.network.copyGraph_trivalent,Y.network.copyGraph_volume_le,fun _ => Y.network.copyGraph_value _⟩

end Hierarchy.CorrectionBatch

end
end OAI
