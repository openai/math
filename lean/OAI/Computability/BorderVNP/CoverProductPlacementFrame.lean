import OAI.Computability.BorderVNP.CoverPlacedTileFrame
import OAI.Computability.BorderVNP.CoverRelativePlacement

/-! # Moving a row of product-tile addresses

For a fixed finite Hecke motion in each factor, a fixed permutation rewires the
factor inputs. Each factor computes the carry from its finite relative-type table
and the modular correction. A second variable deck operand translates each
result on the left, as in the product pack law.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)

/-- The concatenated address wires of the surface factors. -/
abbrev ProductSlots (q l : ℕ) := Fin q × Slots (width l)

/-- The canonical simultaneous address of a tuple of deck elements. -/
def productWires {q : ℕ} (l : ℕ) (x : Fin q → Deck l) : ProductSlots q l → Bool :=
  fun j => deckWires l (x j.1) j.2

/-- The product-tile output of a common pack motion with a specified permutation,
displacement table per factor, and independently supplied left translations. -/
noncomputable def translatedProductPlacement {q a d : ℕ}
    {g : Fin q → Cover.Frame.SL} (hg : ∀ i, Cover.Frame.Clears (g i) a) (hd : 1 ≤ d)
    (perm : Equiv.Perm (Fin q)) (offset : Fin q → Deck (1+2*a) → Deck (d+2*a))
    (shift : Fin q → Deck (d+2*a)) (x : Fin q → Deck (d+2*a+2*a)) : Fin q → Deck (d+2*a) :=
  fun i => shift i * Cover.Frame.placedTile (hg i) hd (offset i) (x (perm i))

/-- A genuine geometric table, built from the representative frame in each
factor, produces the carries of the moved frames. The left translations are
integral representatives of the output deck labels. -/
theorem translatedProductPlacement_geometric {q a d : ℕ} {g : Fin q → Cover.Frame.SL}
    (hg : ∀ i, Cover.Frame.Clears (g i) a) (hd : 1 ≤ d) (perm : Equiv.Perm (Fin q))
    (relative : Fin q → Cover.Frame.SL) (shift x : Fin q → gamma 1) :
    translatedProductPlacement hg hd perm
      (fun i low => (Cover.Frame.frameCarry (Cover.Frame.movedLowFrame (g i) low (relative (perm i))) :
        Deck (d+2*a))) (fun i => (shift i : Deck (d+2*a))) (fun i => (x i : Deck (d+2*a+2*a))) =
      fun i => (Cover.Frame.frameCarry (gammaSL 1 (shift i) *
        (g i * (gammaSL 1 (x (perm i)) * relative (perm i)))) : Deck (d+2*a)) := by
  funext i
  rw [Cover.Frame.frameCarry_translate, QuotientGroup.mk_mul, Cover.Frame.moved_carry_eq (hg i) hd]
  rfl

/-- Shared polynomial-size circuits for translated product placements. The
same bound works for every permutation, displacement table and input tuple. -/
theorem translatedProductPlacement_frames {q a : ℕ} {g : Fin q → Cover.Frame.SL}
    (hg : ∀ i, Cover.Frame.Clears (g i) a) :
    ∃ C e : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (perm : Equiv.Perm (Fin q))
      (offset : Fin q → Deck (1+2*a) → Deck (d+2*a)),
      ∃ f : Frame (ProductSlots q (d+2*a) ⊕ ProductSlots q (d+2*a+2*a)) (ProductSlots q (d+2*a)),
      f.size ≤ C*(d+1)^e ∧ ∀ shift x,
        f.eval (Sum.elim (productWires _ shift) (productWires _ x)) =
          productWires _ (translatedProductPlacement hg hd perm offset shift x) := by
  classical
  choose M m hM using fun i => placedTile_frames (hg i)
  obtain ⟨U,u,hU⟩ := deckMul_frames
  let P := ∑ i, M i
  let e := Finset.univ.sup m
  let out : TimeBound := TimeBound.variable + .const (2*a)
  let bound : TimeBound := 1 + .const q * (.const P * TimeBound.variable^e + .const U * out^u)
  obtain ⟨C,k,_,_,hb⟩ := bound.growth
  refine ⟨C,k,?_⟩
  intro d hd perm offset
  let l := d+2*a
  let z := l+2*a
  let X := ProductSlots q l ⊕ ProductSlots q z
  choose place hp he using fun i => hM i d hd (offset i)
  obtain ⟨mul,hm,hmul⟩ := hU l
  let shiftInput (i : Fin q) : Frame X (Slots (width l)) := Frame.initial (fun j => .inl (i,j))
  let permInput (i : Fin q) : Frame X (Slots (width z)) := Frame.initial (fun j => .inr (perm i,j))
  let lane (i : Fin q) := mul.subst (Crossing.parallelFrame (shiftInput i) ((place i).subst (permInput i)))
  obtain ⟨p,hs,heval⟩ := Crossing.exists_parallelFrames lane
  refine ⟨p.select (fun j => ⟨j.1,j.2⟩), ?_, ?_⟩
  · have hm' (i : Fin q) : M i ≤ P := Finset.single_le_sum (f := M)
        (fun j _ => Nat.zero_le (M j)) (Finset.mem_univ i)
    have hlane (i : Fin q) : (lane i).size ≤ P*(d+1)^e + U*(l+1)^u := by
      simp only [lane,shiftInput,permInput,Frame.subst_size,Crossing.parallelFrame_size,
        Frame.initial_size,zero_add]
      exact Nat.add_le_add ((hp i).trans (Nat.mul_le_mul (hm' i)
        (Nat.pow_le_pow_right (by omega) (Finset.le_sup (Finset.mem_univ i))))) hm
    have hs' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlane i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs'
    have ho : out.eval (d+1) = l+1 := by simp [out,l]; omega
    have hb' := hb (d+1) (by omega)
    simp only [bound,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_const,TimeBound.eval_pow,
      TimeBound.eval_variable,TimeBound.eval_numeral,ho] at hb'
    exact (hs.trans (Nat.add_le_add_left hs' 1)).trans hb'
  · intro shift x
    let input := Sum.elim (productWires _ shift) (productWires _ x)
    funext ⟨i,j⟩
    rw [Frame.select_eval,heval]
    have hi : (permInput i).eval input = deckWires z (x (perm i)) :=
      funext fun b => by simp [permInput,input,productWires,z,l]
    have ha : (Crossing.parallelFrame (shiftInput i) ((place i).subst (permInput i))).eval input =
        Sum.elim (deckWires l (shift i)) (deckWires l (Cover.Frame.placedTile (hg i) hd (offset i) (x (perm i)))) := by
      funext b
      cases b with
      | inl b => simp [shiftInput,input,productWires,l]
      | inr b =>
        rw [Crossing.parallelFrame_eval_inr,Frame.subst_eval,hi,Sum.elim_inr]
        exact congrFun (he i (x (perm i))) b
    change (mul.subst _).eval input j = _
    rw [Frame.subst_eval,ha]
    exact congrFun (hmul _ _) j

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
