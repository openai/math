import OAI.Hierarchy.Catalyst

namespace OAI
/-! # The unit catalyst frame and simultaneous copies of all open ports -/

noncomputable section
namespace Hierarchy.CorrectionFrame

open LinearAlgebra.SpectralBooks SiteTensor
open Catalyst
open scoped BigOperators Classical

abbrev Location (k : ℕ) := Option (Fin k × Bool)

def point {k : ℕ} : Location k → EuclideanSpace ℝ (Fin k)
  | none => 0
  | some (j,s) => EuclideanSpace.single j (if s then 1 else -1)

def location {k p : ℕ} {b : Fin k → ℕ} : Port p b → Location k
  | .inl _ => none
  | .inr (⟨j,_⟩,s) => some (j,s)

theorem point_injective (k : ℕ) : Function.Injective (point (k := k)) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some v =>
      obtain ⟨j,s⟩ := v
      have := congrArg (fun z : EuclideanSpace ℝ (Fin k) => z j) h
      cases s <;> norm_num [point, PiLp.single_apply] at this
  | some u =>
    obtain ⟨i,s⟩ := u
    cases y with
    | none =>
      have := congrArg (fun z : EuclideanSpace ℝ (Fin k) => z i) h
      cases s <;> norm_num [point, PiLp.single_apply] at this
    | some v =>
      obtain ⟨j,t⟩ := v
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin k) => z i) h
      have ij : i=j := by
        by_contra ne
        cases s <;> cases t <;> norm_num [point, PiLp.single_apply,ne] at hi
      subst j
      have self (v : Bool) : (point (some (i,v))) i = (if v then (1:ℝ) else -1) := by
        change (EuclideanSpace.single i (if v then (1:ℝ) else -1) : EuclideanSpace ℝ (Fin k)) i = _
        rw [PiLp.single_apply,ite_eq_left rfl]
      have signs : (if s then (1:ℝ) else -1) = (if t then (1:ℝ) else -1) :=
        (self s).symm.trans (hi.trans (self t))
      have st : s=t := by
        cases s <;> cases t
        · rfl
        · norm_num at signs
        · norm_num at signs
        · rfl
      rw [st]

def frame (k : ℕ) : Location k ↪ EuclideanSpace ℝ (Fin k) := ⟨point, point_injective k⟩

theorem sites_eq {k p : ℕ} (b : Fin k → ℕ) :
    sites (p := p) b = frame k ∘ location := by
  funext i
  rcases i with t | ⟨⟨j,q⟩,s⟩ <;> rfl

theorem scale_le {F : Type*} [Field F] {k : ℕ}
    (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k))) :
    P.price (Raw.diagonal (Location k) F (Fin 2)) (frame k) ≤ 2*k := by
  let T := Raw.diagonal (Location k) F (Fin 2)
  have h := P.transport T (frame k) (fun _ => 0)
  rw [P.collapsed, Real.dist_eq, sub_zero] at h
  apply (le_abs_self _).trans (h.trans ?_)
  change ∑ i : Location k, dist (point i) 0 * Real.logb 2 (Fintype.card (Fin 2)) ≤ _
  simp only [Fintype.card_fin, Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
    mul_one, Fintype.sum_option, point, zero_add, dist_zero_right,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    PiLp.norm_single, norm_one, norm_zero, norm_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring_nf; exact le_rfl

def copiesWidth {k : ℕ} (s : ℕ) (b : Fin k → ℕ) : Fin k → ℕ := fun j => s*b j

/-- The data bits of each copy are a consecutive block, as are its wires within
each catalyst direction. No bit is identified with a bit of another copy. -/
def copiesPortEquiv {k p : ℕ} (s : ℕ) (b : Fin k → ℕ) :
    Fin s × Port p b ≃ Port (s*p) (copiesWidth s b) where
  toFun
    | (i,.inl j) => .inl (finProdFinEquiv (i,j))
    | (i,.inr (⟨j,l⟩,v)) => .inr (⟨j,finProdFinEquiv (i,l)⟩,v)
  invFun
    | .inl l => let il := finProdFinEquiv.symm l; (il.1,.inl il.2)
    | .inr (⟨j,l⟩,v) =>
      let il : Fin s × Fin (b j) := finProdFinEquiv.symm l
      (il.1,.inr (⟨j,il.2⟩,v))
  left_inv := by
    rintro ⟨i, l | ⟨⟨j,l⟩,v⟩⟩ <;> simp
  right_inv := by
    rintro (l | ⟨⟨j,l⟩,v⟩)
    · exact congrArg Sum.inl ((finProdFinEquiv (m:=s) (n:=p)).apply_symm_apply l)
    · exact congrArg (fun t : Fin (s*b j) => (Sum.inr (⟨j,t⟩,v) : Port (s*p) (copiesWidth s b)))
        ((finProdFinEquiv (m:=s) (n:=b j)).apply_symm_apply l)

theorem copies_location {k p s : ℕ} (b : Fin k → ℕ) (i : Fin s × Port p b) :
    location (copiesPortEquiv s b i) = location i.2 := by
  rcases i with ⟨i, l | ⟨⟨j,l⟩,v⟩⟩ <;> rfl

def dataProduct {F : Type*} [CommMonoid F] {p : ℕ} (s : ℕ) (f : (Fin p → Bool) → F)
    (x : Fin (s*p) → Bool) : F := ∏ i : Fin s, f (fun j => x (finProdFinEquiv (i,j)))

end Hierarchy.CorrectionFrame

end
end OAI
