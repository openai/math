import OAI.Computability.NearSquareRoot.InterchangeStageLayouts
import OAI.Computability.NearSquareRoot.InterchangeStageRoute
import OAI.Computability.NearSquareRoot.InterchangeLabelRectangles

/-! # One family of rational address maps for the complete Hamming partition -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix

/-- The endpoints of one directed rectangle, with their original orientation. -/
abbrev RectanglePoint {L : Type} (r : Rectangle L) :=
  {x : Bool × L // x.2 ∈ if x.1 then r.destinations else r.sources}

/-- Per-rectangle choices of dimensions, shared frame, and endpoint instructions.
The labels use the same global coordinate map in every rectangle they meet. -/
structure RectangleAtlas {L B : Type} (r : B → Rectangle L) (a : ℕ) where
  label : Bool → L → (Fin (a+2) → ℚ) ≃ₗ[ℚ] (Fin (a+2) → ℚ)
  diagonal : ∀ v x, (label true v).symm (label false v x) = x ∘ flipQuery a
  c : B → ℕ
  e : B → ℕ
  size : ∀ t, c t + e t = a
  common : (t : B) → (Fin (c t + (2 + e t)) → ℚ) ≃ₗ[ℚ] (Fin (a+2) → ℚ)
  prepare : (t : B) → RectanglePoint (r t) → (Fin a → ℚ) ≃ₗ[ℚ] (Fin (c t + e t) → ℚ)
  early : (t : B) → RectanglePoint (r t) → Matrix (Fin 2) (Fin (c t)) ℚ
  late : (t : B) → RectanglePoint (r t) → Matrix (Fin (e t)) (Fin 2) ℚ
  triangle : ∀ t i, (preparedQuery (prepare t i)).trans
    ((endpointAddress (early t i) (late t i)).trans (common t)) = label i.val.1 i.val.2

/-- The numerical Hamming rectangles admit compatible coordinate diagrams.
An empty key imposes no endpoint conditions and can use the identity frame. -/
theorem hamming_atlas (p k : ℕ) (hp : 0 < p) :
    Nonempty (RectangleAtlas (hammingRectangle (p:=p) (k:=k) (hp:=hp))
      ((2*p-1) * Fintype.card (Word p (2^k)))) := by
  classical
  let a := (2*p-1) * Fintype.card (Word p (2^k))
  let far := fun u v : Word p (2^k) => hammingDist u v = p
  have hir (u) : ¬far u u := by simp [far,Nat.ne_of_lt hp]
  let H (s : Bool) (v : Label p (2^k)) := labelAddress far p hp hir v s
  let r := hammingRectangle (p:=p) (k:=k) (hp:=hp)
  have layout (t : HammingRectangleKey p k hp) :
      ∃ c e : ℕ, c+e=a ∧
      ∃ common : (Fin (c+(2+e)) → ℚ) ≃ₗ[ℚ] (Fin (a+2) → ℚ),
      ∃ prepare : RectanglePoint (r t) → (Fin a → ℚ) ≃ₗ[ℚ] (Fin (c+e) → ℚ),
      ∃ G : RectanglePoint (r t) → Matrix (Fin 2) (Fin c) ℚ,
      ∃ D : RectanglePoint (r t) → Matrix (Fin e) (Fin 2) ℚ,
        ∀ i, (preparedQuery (prepare i)).trans ((endpointAddress (G i) (D i)).trans common) =
          H i.val.1 i.val.2 := by
    by_cases hi : Nonempty (RectanglePoint (r t))
    · let ref := Classical.choice hi
      apply rectangle_address_diagram far p hp hir _ _ ref
      apply gram_rectangle_layout far hp
      rintro ⟨⟨s,u⟩,hu⟩ ⟨⟨v,w⟩,hw⟩
      cases s <;> cases v
      · exact count_hammingRectangle_same (side := false) hu hw
      · exact count_hammingRectangle_cross hu hw
      · simpa only [far,hammingDist_comm,Bool.true_eq_false,ite_false] using
          count_hammingRectangle_cross hw hu
      · exact count_hammingRectangle_same (side := true) hu hw
    · exact ⟨a,0,rfl,LinearEquiv.refl ℚ _,fun i => (hi ⟨i⟩).elim, fun i => (hi ⟨i⟩).elim,
        fun i => (hi ⟨i⟩).elim, fun i => (hi ⟨i⟩).elim⟩
  choose c e size common prepare early late triangle using layout
  exact ⟨⟨H,fun v => labelAddress_diagonal far p hp hir v,c,e,size,common,prepare,
    early,late,triangle⟩⟩

end Interchange

end NearSquareRoot
end Computability
end OAI
