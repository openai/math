import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place

/-!
# Ordinary linear combinations and bipartite decompositions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S J U : Type} [Field K] [Fintype S] [Nonempty S] [Fintype J]
  (X : S → Type) [∀ s, Fintype (X s)] (T : (∀ s, X s) → K)

theorem span_le (V : J → (∀ s, X s) → K) (a : J → K) (h : ∀ x, T x = ∑ j, a j * V j x) :
    ofRaw (Raw.ofTable X T) ≤ ∑ j, ofRaw (Raw.ofTable X (V j)) := by
  classical
  let A j := Raw.ofTable X (V j)
  let w j s := if s = Classical.arbitrary S then a j else 1
  let M j (s : S) (x y : X s) := if y = x then w j s else 0
  refine (Raw.restriction_sum_iff A (Raw.ofTable X T) Finset.univ).mpr ⟨M, fun x => ?_⟩
  change (∀ s, X s) at x
  rw [Raw.coeff_ofTable, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Raw.coeff_ofTable X (V j) x]
  change a j * (∑ i : (A j).term, ∏ s, (A j).factor i s (x s)) =
    ∑ i : (A j).term, ∏ s, ∑ y : X s, M j s (x s) y * (A j).factor i s y
  simp only [M, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.prod_mul_distrib, Finset.mul_sum]
  simp [w]

variable [DecidableEq S] [Fintype U] [DecidableEq U]

/-- Transport two groups of sites to two endpoints. A separated-variable
expansion costs no more than one wire indexed by the summands. -/
theorem separated_le (B : S → Prop) [DecidablePred B] (L R : J → (∀ s, X s) → K)
    (h : ∀ x, T x = ∑ j, L j x * R j x)
    (hL : ∀ j x y, (∀ s, B s → x s = y s) → L j x = L j y)
    (hR : ∀ j x y, (∀ s, ¬ B s → x s = y s) → R j x = R j y) (m o : U) :
    place (fun s => if B s then m else o) (ofRaw (Raw.ofTable X T)) ≤
      wire K m o (Fintype.card J) := by
  classical
  let f s := decide (B s)
  let g (b : Bool) := if b then m else o
  let A := Raw.ofTable X T
  by_cases hx : Nonempty (∀ s, X s)
  swap
  · have hz : ofRaw A = 0 := (ofRaw_eq_zero A).mpr (fun x => False.elim (hx ⟨x⟩))
    let _ : Nonempty U := ⟨m⟩
    rw [show ofRaw (Raw.ofTable X T) = 0 from hz, place_zero]
    exact zero_le _
  let fill (b : Bool) (x : (A.group f).leg b) (s : S) : X s :=
    if hs : f s = b then x ⟨s, hs⟩ else hx.some s
  let D : Raw K Bool :=
    ⟨(A.group f).leg, J, fun j b x => if b then L j (fill b x) else R j (fill b x)⟩
  have he : A.group f ≈ D := by
    refine Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
    let v (s : S) : X s := x (f s) ⟨s, rfl⟩
    have hv (b : Bool) (s : S) (hs : f s = b) : v s = fill b (x b) s := by
      subst b
      unfold fill
      erw [dite_eq_left (show f s = f s from rfl)]
    rw [Raw.coeff_group]
    change A.coeff v = D.coeff x
    rw [show A.coeff v = T v from Raw.coeff_ofTable _ _ _, h]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = ∏ b : Bool, if b then L j (fill b (x b)) else R j (fill b (x b))
    rw [Fintype.prod_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact congrArg₂ (· * ·) (hL _ _ _ (fun s hs => hv _ _ (by simp [f, hs])))
      (hR _ _ _ (fun s hs => hv _ _ (by simp [f, hs])))
  have hd : place f (ofRaw A) ≤ wire K true false (Fintype.card J) := by
    rw [place_ofRaw, ofRaw_eq he, wire, show ({true, false} : Finset Bool) = Finset.univ by decide,
      shared_all]
    exact le_term_count D
  have hg := place_mono g hd
  rw [← place_comp, place_wire] at hg
  have e : g ∘ f = fun s => if B s then m else o := by ext s; simp [g, f]
  rw [e] at hg
  exact hg

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
