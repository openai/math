import OAI.Computability.VPVNP.GrassmannTypes
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

namespace OAI
/-! # Coordinate cubes and their squares in the binary Grassmannian -/

namespace Hierarchy.GrassmannCube

open Computability.VPVNP.Grassmann Submodule
open scoped BigOperators

noncomputable section

private def index (m : ℕ) : Fin m × Bool ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp [Nat.mul_comm])

private def coord {m : ℕ} (i : Fin m × Bool) : Space m := Pi.basisFun (ZMod 2) _ (index m i)

private def sub {m : ℕ} (s : Finset (Fin m × Bool)) : Submodule (ZMod 2) (Space m) :=
  span _ (coord '' (s : Set (Fin m × Bool)))

private theorem sub_rank {m : ℕ} (s : Finset (Fin m × Bool)) : Module.finrank (ZMod 2) (sub s) = s.card := by
  have h := (Pi.basisFun (ZMod 2) (Fin (2*m))).linearIndependent.comp (index m) (index m).injective
  have independent : LinearIndependent (ZMod 2) (fun i : s => coord i.val) := by
    simpa only [coord, Function.comp_def] using h.comp (fun i : s => i.val) Subtype.val_injective
  have hr : Set.range (fun i : s => coord i.val) = coord '' (s : Set (Fin m × Bool)) := by ext; simp
  rw [sub, ← hr]
  simpa only [Fintype.card_coe] using finrank_span_eq_card independent

private def selected {m : ℕ} (v : Fin m → Bool) : Finset (Fin m × Bool) :=
  Finset.univ.image fun i => (i,v i)

private theorem card_selected {m : ℕ} (v : Fin m → Bool) : (selected v).card = m := by
  rw [selected, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

/-- One of two independent columns is selected for each coordinate. -/
def plane {m : ℕ} (v : Fin m → Bool) : Plane m := ⟨sub (selected v), (sub_rank _).trans (card_selected _)⟩

def hamming {m : ℕ} (v w : Fin m → Bool) : ℕ := (Finset.univ.filter fun i => v i ≠ w i).card

theorem plane_pair {m : ℕ} (v w : Fin m → Bool) : HasType (hamming v w) (plane v) (plane w) := by
  classical
  have hi : selected v ∩ selected w = (Finset.univ.filter fun i => v i = w i).image (fun i => (i,v i)) := by
    ext ⟨i,b⟩
    simp [selected]
    aesop
  have hci := congrArg Finset.card hi
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)] at hci
  have hc := Finset.card_union_add_card_inter (selected v) (selected w)
  rw [card_selected, card_selected,hci] at hc
  have he := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun i => v i = w i)
  simp only [Finset.card_univ, Fintype.card_fin] at he
  change Module.finrank _ (sub (selected v) ⊔ sub (selected w) : Submodule _ _) = m + _
  have hu : sub (selected v) ⊔ sub (selected w) = sub (selected v ∪ selected w) := by
    simp only [sub, Finset.coe_union, Set.image_union, span_union]
  have rankEq := congrArg (fun U : Submodule (ZMod 2) (Space m) => Module.finrank (ZMod 2) U) hu
  refine rankEq.trans ((sub_rank _).trans ?_)
  have different : hamming v w = (Finset.univ.filter fun i => ¬v i = w i).card := by
    unfold hamming
    apply congrArg Finset.card
    ext i
    simp [ne_eq]
  rw [different]
  omega

private def flag {m : ℕ} (s : Finset (Fin m)) : Fin m → Bool := fun i => decide (i ∈ s)

/-- Two sets of independent coordinate flips give every admissible quadrilateral type. -/
theorem squares {m : ℕ} (r s : ℕ) (h : r+s ≤ m) : ∃ a b c d : Plane m, IsSquare r s a b c d := by
  classical
  obtain ⟨R,_,hR⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin m))) (n := r) (by simpa using (show r ≤ m by omega))
  have hS : s ≤ ((Finset.univ : Finset (Fin m)) \ R).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hR]; omega
  obtain ⟨S,hSR,hs⟩ := Finset.exists_subset_card_eq hS
  have hd : Disjoint R S := Finset.disjoint_left.mpr fun _ ha hb => (Finset.mem_sdiff.mp (hSR hb)).2 ha
  let a := flag (∅ : Finset (Fin m))
  let b := flag R
  let c := flag (R ∪ S)
  let d := flag S
  have hab : hamming a b = r := by simpa [hamming,a,b,flag] using hR
  have hda : hamming d a = s := by simpa [hamming,d,a,flag] using hs
  have hc (i : Fin m) : ¬(i ∈ R ∧ i ∈ S) := fun h => Finset.disjoint_left.mp hd h.1 h.2
  have hbc' : (Finset.univ.filter fun i => b i ≠ c i) = S := by
    ext i; simp [b,c,flag]; specialize hc i; aesop
  have hcd' : (Finset.univ.filter fun i => c i ≠ d i) = R := by
    ext i; simp [c,d,flag]; specialize hc i; aesop
  have hac' : (Finset.univ.filter fun i => a i ≠ c i) = R ∪ S := by
    ext i
    by_cases ir : i ∈ R <;> by_cases is : i ∈ S <;> simp [a,c,flag,ir,is]
  have hbd' : (Finset.univ.filter fun i => b i ≠ d i) = R ∪ S := by
    ext i
    by_cases ir : i ∈ R
    · have outside : i ∉ S := Finset.disjoint_left.mp hd ir
      simp [b,d,flag,ir,outside]
    · by_cases is : i ∈ S <;> simp [b,d,flag,ir,is]
  have hbc : hamming b c = s := (congrArg Finset.card hbc').trans hs
  have hcd : hamming c d = r := (congrArg Finset.card hcd').trans hR
  have hac : hamming a c = r+s := by rw [hamming,hac', Finset.card_union_of_disjoint hd, hR, hs]
  have hbd : hamming b d = r+s := by rw [hamming,hbd', Finset.card_union_of_disjoint hd, hR, hs]
  exact ⟨plane a,plane b,plane c,plane d,⟨hab ▸ plane_pair a b,hbc ▸ plane_pair b c,
    hcd ▸ plane_pair c d,hda ▸ plane_pair d a,hac ▸ plane_pair a c,hbd ▸ plane_pair b d⟩⟩

/-- Coordinates past `d` use the same column at every cube vertex. -/
def extend {d m : ℕ} (v : Fin d → Bool) : Fin m → Bool := fun i => if h : i.val < d then v ⟨i.val,h⟩ else false

theorem hamming_extend {d m : ℕ} (h : d ≤ m) (v w : Fin d → Bool) :
    hamming (extend (m := m) v) (extend w) = hamming v w := by
  classical
  let e : Fin d ↪ Fin m := Fin.castLEEmb h
  have hs : (Finset.univ.filter fun i : Fin m => extend v i ≠ extend w i) =
      (Finset.univ.filter fun i => v i ≠ w i).map e := by
    ext i
    constructor
    · intro hi
      have neq := (Finset.mem_filter.mp hi).2
      by_cases inside : i.val < d
      · refine Finset.mem_map.mpr ⟨⟨i.val,inside⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,Fin.ext rfl⟩
        simpa only [extend,dite_eq_left inside] using neq
      · simp [extend,inside] at neq
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      have small : (e j).val < d := j.isLt
      have same : (⟨(e j).val,small⟩ : Fin d) = j := Fin.ext rfl
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simpa only [extend,dite_eq_left small,same] using (Finset.mem_filter.mp hj).2⟩
  rw [hamming,hs,Finset.card_map]; rfl

end
end Hierarchy.GrassmannCube

end OAI
