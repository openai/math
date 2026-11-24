import OAI.Computability.VPVNP.MotifPayload

/-!
# Contraction of a single grouped payload

For a fixed global selector sequence, a matching payload width allows all
wire values to be split into independent fields for the repeated copies.
Summing over those fields factors into the product of the base contractions.
A mismatched width makes the local entry vanish at every party.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifSelector

open WireTensor

variable {J E S R : Type*} {C : J → Type*}

/-- Regroup the edgewise fields into one complete wire assignment per copy. -/
private def assignmentEquiv (w : S → E → ℕ) {u : ℕ} (θ : Fin u → S) :
    (∀ e, Word (totalWidth w θ e)) ≃ (∀ i, (e : E) → Word (w (θ i) e)) where
  toFun x i e := unpackFields (fun j ↦ w (θ j) e) (x e) i
  invFun y e := (unpackFields (fun j ↦ w (θ j) e)).symm (fun i ↦ y i e)
  left_inv x := funext fun e ↦ (unpackFields (fun j ↦ w (θ j) e)).symm_apply_apply (x e)
  right_inv y := funext fun i ↦ funext fun e ↦
    congrFun ((unpackFields (fun j ↦ w (θ j) e)).apply_symm_apply (fun j ↦ y j e)) i

open scoped Classical in
/-- A fixed global sequence contributes precisely the product of its local
base contractions to the one outer term indexed by its accumulated widths. -/
theorem sum_payload_indices [Fintype J] [Nonempty J] [Fintype E] [CommSemiring R]
    (G : Supply J E) (w : S → E → ℕ)
    (L : ∀ s j, C j → Half G (fun e ↦ Word (w s e)) j → R) {u : ℕ}
    (v : E → ℕ) (θ : Fin u → S) (c : ∀ j, Fin u → C j) :
    (∑ x : ∀ e, Word (v e), ∏ j, evalIndices L j
      (payloadIndices G w v θ j (c j) (edgeAssignment G.src G.dst x j))) =
      if v = totalWidth w θ then
        ∏ i, ∑ y : ∀ e, Word (w (θ i) e),
          ∏ j, L (θ i) j (c j i) (edgeAssignment G.src G.dst y j)
      else 0 := by
  classical
  by_cases hv : v = totalWidth w θ
  · subst v
    let f (i : Fin u) (y : ∀ e, Word (w (θ i) e)) (j : J) :=
      L (θ i) j (c j i) (edgeAssignment G.src G.dst y j)
    let e := assignmentEquiv w θ
    have entry (x : ∀ d, Word (totalWidth w θ d)) (j : J) :
        evalIndices L j (payloadIndices G w (totalWidth w θ) θ j (c j)
          (edgeAssignment G.src G.dst x j)) = ∏ i, f i (e x i) j := by
      simp [payloadIndices, evalIndices, f, e, assignmentEquiv, mapHalf_edgeAssignment]
      rfl
    simp only [ite_true, eq_self]
    simp_rw [entry]
    change (∑ x, ∏ j, ∏ i, f i (e x i) j) = ∏ i, ∑ y, ∏ j, f i y j
    rw [Fintype.prod_sum]
    calc
      _ = ∑ x, ∏ i, ∏ j, f i (e x i) j := Finset.sum_congr rfl fun x _ ↦ Finset.prod_comm
      _ = _ := e.sum_comp (fun y ↦ ∏ i, ∏ j, f i (y i) j)
  · simp [payloadIndices, hv, evalIndices]

end MotifSelector

end VPVNP
end Computability
end OAI
