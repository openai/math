import OAI.Geometry.Hirsch.Emissions
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section

namespace OAI.Geometry.Hirsch.Layer

variable {X A : Type} [Fintype X] [Fintype A] {L b r : ℕ}

def numbering (X : Type) [Fintype X] (x : X) := (Fintype.equivFin X x).val

theorem numbering_injective : Function.Injective (numbering X) :=
  fun _ _ he => (Fintype.equivFin X).injective (Fin.ext he)

def factor (X : Type) [Fintype X] (r : ℕ) := (r+1)*(Fintype.card X+1)^r+1

abbrev Digits (r b : ℕ) := Fin (r+1) → Fin b

def digits (hh : L ≤ b^(r+1)) : Fin L ↪ Digits r b :=
  (Fin.castLEEmb (show L ≤ Fintype.card (Digits r b) by simpa [Digits] using hh)).trans
    (Fintype.equivFin _).symm.toEmbedding

def evaluation (y : Digits r b) (x : X) := ∑ j, (numbering X x)^j.val * (y j).val

theorem evaluation_bound (y : Digits r b) (x : X) : evaluation y x < factor X r * b := by
  have hb : 0 < b := (y 0).pos
  have hx : numbering X x ≤ Fintype.card X + 1 := by
    have hh := (Fintype.equivFin X x).isLt
    unfold numbering
    omega
  unfold evaluation factor
  calc
    _ ≤ ∑ _ : Fin (r+1), (Fintype.card X+1)^r * b := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul ((Nat.pow_le_pow_left hx _).trans
        (Nat.pow_le_pow_right (by omega) (by omega))) (y j).isLt.le
    _ = (r+1)*(Fintype.card X+1)^r*b := by simp [mul_assoc]
    _ < _ := Nat.mul_lt_mul_of_pos_right (by omega) hb

theorem evaluation_injective (f : Fin (r+1) → X) (hf : Function.Injective f)
    {y z : Digits r b} (he : ∀ j, evaluation y (f j) = evaluation z (f j)) : y = z := by
  let u := fun j => (numbering X (f j) : ℚ)
  have hu : Function.Injective u := Nat.cast_injective.comp (numbering_injective.comp hf)
  let M := Matrix.vandermonde u
  have hM : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hu)
  let lift := fun (a : Digits r b) j => ((a j).val : ℚ)
  have hv : ∀ a j, M.mulVec (lift a) j = evaluation a (f j) := by
    intro a j
    simp [M,u,lift,Matrix.mulVec,dotProduct,Matrix.vandermonde,evaluation]
  have hh : lift y = lift z := hM (funext fun j => by rw [hv,hv,he])
  exact funext fun j => Fin.ext (Nat.cast_injective (congrFun hh j))

abbrev Labels (A X : Type) [Fintype X] (r b : ℕ) := A × X × Fin (factor X r * b)

def tagCode (A : Type) [Fintype A] (game : Arena X (2^r)) (hh : L ≤ b^(r+1)) :
    Bundles L (Fintype.card (Labels A X r b)) where
  r := r
  X := X
  idx := A
  game := game
  label s i x := Fintype.equivFin _ (i,x,⟨evaluation (digits hh s) x,evaluation_bound ..⟩)
  unique _ _ _ _ _ he := by
    have h := (Fintype.equivFin (Labels A X r b)).injective he
    exact ⟨congrArg Prod.fst h,congrArg (fun z => z.2.1) h⟩

theorem tag_separates (game : Arena X (2^r)) (hh : L ≤ b^(r+1)) :
    (tagCode A game hh).Separates := by
  let code := tagCode A game hh
  constructor
  · intro _ _ _ _ _ _ he
    exact congrArg Prod.fst ((Fintype.equivFin (Labels A X r b)).injective he)
  · rintro ⟨t,i,w⟩ s hn
    let word : List X := w.val.val
    have hl : word.length = r+1 := w.property.1
    have hd : word.Nodup := w.property.2.imp (fun h => h.1)
    let f := fun j : Fin (r+1) => word.get (Fin.cast hl.symm j)
    have hf : Function.Injective f := fun _ _ he => Fin.cast_injective _ (hd.get_inj_iff.mp he)
    have diff : ∃ j, evaluation (digits hh t) (f j) ≠ evaluation (digits hh s) (f j) := by
      by_contra! he
      exact hn ((digits hh).injective (evaluation_injective f hf he))
    obtain ⟨j,hj⟩ := diff
    refine ⟨code.label t i (f j),⟨f j,List.get_mem ..,rfl⟩,fun a he => ?_⟩
    have eqn := (Fintype.equivFin (Labels A X r b)).injective he
    have ha : a = f j := congrArg (fun z => z.2.1) eqn
    subst a
    exact hj (congrArg (fun z => z.2.2.val) eqn.symm)

end OAI.Geometry.Hirsch.Layer
