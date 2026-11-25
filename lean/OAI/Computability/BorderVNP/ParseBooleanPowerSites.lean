import OAI.Computability.BorderVNP.ParseBooleanPhysical
import OAI.Computability.BorderVNP.DiagonalPowerSites
import OAI.Computability.BorderVNP.ParseBatchScalarExtension

/-! # Tagged physical unary sites after Boolean input rewiring -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.BooleanLayout

open VPVNP.BooleanTranscript Diagonal.CellEntries MvPolynomial
open scoped Classical

variable {X W Param Gadget : Type} {s b : ℕ} [Fintype X] [Fintype W] [Fintype Param]
    (c : Circuit (X ⊕ W) s) (weighted : Param × Fin b → W)

/-- Integral formal-polynomial entry of each selected binary exponent position. -/
noncomputable def powerWeight (j : Param × Fin b) (z : Bool) : MvPolynomial Param ℤ :=
  if z then MvPolynomial.X j.1 ^ (2^j.2.val) else 1

/-- Named unary factors read the supplying wire. All other physical entries are Boolean checks. -/
noncomputable def powerTags : (layout c weighted).network.Tables (Entry Param Gadget) :=
  fun v a x => if hj : ∃ j, weightSite c weighted j = v then
    let j := hj.choose
    unary j.1 j.2.val (a ⟨weightEdge c weighted j,Or.inr ((weightEdge_dst ..).trans hj.choose_spec)⟩ 0)
  else if (layout c weighted).tables (factor c powerWeight) v a x = 1 then 1 else 0

/-- The tagged entry of the indicated site reads exactly its original count bit. -/
theorem powerTags_at (j : Param × Fin b) (a x) :
    powerTags (Gadget := Gadget) c weighted (weightSite c weighted j) a x =
      unary j.1 j.2.val (a ⟨weightEdge c weighted j, Or.inr (weightEdge_dst ..)⟩ 0) := by
  have h : ∃ t, weightSite c weighted t = weightSite c weighted j := ⟨j,rfl⟩
  have he := (weightSite c weighted).injective h.choose_spec
  simp only [powerTags, dite_eq_left h, he]
  congr 1
  apply congrArg (fun e => a e 0)
  exact Subtype.ext (congrArg (weightEdge c weighted) he)

/-- All fine weight occurrences remain distinct after replacing the visible inputs
with public slots, private interior edges and Boolean constants. -/
noncomputable def powerSites : PowerSites Unit Param Gadget b (layout c weighted).network (powerTags c weighted) where
  site := { toFun := fun w => weightSite c weighted w.2
            inj' := fun _ _ h => Prod.ext (Subsingleton.elim ..) ((weightSite c weighted).injective h) }
  named := by
    rintro ⟨_,p,j⟩ a x
    change (counters (powerTags (Gadget := Gadget) c weighted (weightSite c weighted (p,j)) a x)).1 = 0 ∨
      (counters (powerTags (Gadget := Gadget) c weighted (weightSite c weighted (p,j)) a x)).1 =
        Finsupp.single p (2^j.val)
    rw [powerTags_at]
    cases a ⟨weightEdge c weighted (p,j),Or.inr (weightEdge_dst ..)⟩ 0
    · exact Or.inl rfl
    · exact Or.inr rfl
  other := by
    intro v hv a x
    have h : ¬ ∃ j, weightSite c weighted j = v := fun ⟨j,hj⟩ => hv ⟨((),j),hj⟩
    simp only [powerTags,dite_eq_right h]
    split <;> rfl

/-- The tagged table interpreted over any coefficient ring is exactly the
scalar extension of the corresponding Boolean verifier with integral weights. -/
theorem powerTags_interpret {E : Type*} [CommRing E] (values : Gadget → E) (v a x) :
    interpret values (powerTags c weighted v a x) =
      map (Int.castRingHom E) ((layout c weighted).tables (factor c powerWeight) v a x) := by
  by_cases h : ∃ j, weightSite c weighted j = v
  · obtain ⟨j,rfl⟩ := h
    rw [powerTags_at,interpret_unary,weight_table]
    cases a ⟨weightEdge c weighted j,Or.inr (weightEdge_dst ..)⟩ 0 <;> simp [powerWeight]
  · rcases other_tables_zero_one c weighted powerWeight v (fun j he => h ⟨j,he.symm⟩) a x with hv | hv <;>
      simp [powerTags,h,hv]

/-- Interpretation specializes the entire physical network, summing every private bit. -/
theorem powerTags_value {E : Type*} [CommRing E] (values : Gadget → E) (x : X → Bool) :
    (layout c weighted).network.value (fun v z y => interpret values (powerTags c weighted v z y)) (fun i _ => x i) =
      map (Int.castRingHom E) ((layout c weighted).network.value
        ((layout c weighted).tables (factor c powerWeight)) (fun i _ => x i)) := by
  simp_rw [powerTags_interpret]
  exact Crossing.Network.value_mapTables _ _ _ _

end ParseBatch.BooleanLayout

end BorderVNP
end Computability
end OAI
