import OAI.Computability.BorderVNP.PackedHistoryRouteRows
import OAI.Computability.BorderVNP.CoverDeckLookupFrame
import OAI.Computability.BorderVNP.CoverDeckFrameOperations

/-! # Translating a fixed finite geodesic catalog on public deck coordinates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.Catalog Shortening.PublicRelative Crossing Cover Cover.AddressCircuit Epoch
open StackFrame RationalHitting
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

private theorem productMul_frames :
    ∃ C e : ℕ, ∀ q l, ∃ f : Frame (ProductSlots q l ⊕ ProductSlots q l) (ProductSlots q l),
      f.size ≤ 1 + q*C*(l+1)^e ∧ ∀ a b : Fin q → Deck l,
        f.eval (Sum.elim (productWires l a) (productWires l b)) = productWires l (a*b) := by
  obtain ⟨C,e,hm⟩ := deckMul_frames
  refine ⟨C,e,?_⟩
  intro q l
  obtain ⟨f,hf,ev⟩ := hm l
  let wires (i : Fin q) : Slots (width l) ⊕ Slots (width l) → ProductSlots q l ⊕ ProductSlots q l :=
    Sum.elim (fun j => .inl (i,j)) (fun j => .inr (i,j))
  let row (i : Fin q) := f.subst (Frame.initial (wires i))
  obtain ⟨out,hs,he⟩ := exists_parallelFrames (out := fun _ : Fin q => Slots (width l)) row
  refine ⟨out.select (fun j : ProductSlots q l => ⟨j.1,j.2⟩),?_,?_⟩
  · simpa [row,Nat.mul_assoc] using hs.trans (Nat.add_le_add_left (Finset.sum_le_sum
      (fun (i : Fin q) _ => show (row i).size ≤ C*(l+1)^e by simpa [row] using hf)) 1)
  · intro a b
    let x := Sum.elim (productWires l a) (productWires l b)
    have hw (i : Fin q) : (Frame.initial (wires i)).eval x = Sum.elim (deckWires l (a i)) (deckWires l (b i)) := by
      funext j
      cases j <;> simp [wires,x,productWires]
    funext j
    rw [Frame.select_eval]
    change out.eval x ⟨j.1,j.2⟩ = _
    rw [he]
    exact (Frame.subst_eval f (Frame.initial (wires j.1)) x j.2).trans
      (by rw [hw,ev]; rfl)

variable {I M : Type*} [Fintype I] [Fintype M] {q : ℕ} (enum : Fin q ≃ I)

/-- A single lookup of a relative template provides its canonical chart index and its
tile carry. Right multiplication by that carry gives the true tile of the translated
point, including boundary points. The polynomial bound is uniform over the point table. -/
theorem translatedPoint_frames (S : Finset (HyperbolicHost I)) :
    ∃ C e : ℕ, ∀ (d : ℕ) (point : M → HyperbolicHost I),
      ∃ f : Frame (M ⊕ ProductSlots q (d+1)) (ProductSlots q (d+1) ⊕ ↥S),
        f.size ≤ C*(d+2)^e ∧ ∀ m (a : I → gamma 1),
          f.eval (Sum.elim (fun s => decide (s=m)) (productWires _ (fun i => (a (enum i) : Deck (d+1))))) =
            quotientRow enum S d rfl (productProjection (d+1) (translatePoint a (point m))) := by
  obtain ⟨U,u,hm⟩ := productMul_frames
  let B : TimeBound := 1 + .const (q*U)*TimeBound.variable^u +
    .const (Fintype.card M*(3*Fintype.card M+2)) +
    (.const (90*q)*TimeBound.variable + .const (Fintype.card ↥S)) * .const (2*Fintype.card M+1)
  obtain ⟨C,e,_,_,hb⟩ := B.growth
  refine ⟨C,e,?_⟩
  intro d point
  let l := d+1
  let one (m : M) := fun t => decide (t=m)
  have hinj : Function.Injective one := by
    intro a b h
    have h' := congrFun h a
    simpa [one] using h'
  let tab (m : M) : ProductSlots q l ⊕ ↥S → Bool := Sum.elim
    (productWires l (fun i => productAddress d (productProjection (d+1) (point m)) (enum i)))
    (fun t => decide (t.val=normalize (point m)))
  obtain ⟨table,ht,et⟩ := lookupFrame one hinj tab
  obtain ⟨mul,hs,em⟩ := hm q l
  let source := (table.subst (Frame.initial (Sum.inl : M → M ⊕ ProductSlots q l))).withInput
  let pair : ProductSlots q l ⊕ ProductSlots q l → (M ⊕ ProductSlots q l) ⊕ (ProductSlots q l ⊕ ↥S) :=
    Sum.elim (fun i => .inl (.inr i)) (fun i => .inr (.inl i))
  let suffix := parallelFrame (mul.subst (Frame.initial pair)) (Frame.initial (fun i : ↥S => .inr (.inr i)))
  refine ⟨suffix.subst source,?_,?_⟩
  · have hc : Fintype.card (ProductSlots q l ⊕ ↥S) = 90*q*(d+2)+Fintype.card ↥S := by
      simp [ProductSlots,Slots,width,l]; ring
    rw [hc] at ht
    have hsize : (suffix.subst source).size = table.size + mul.size := by simp [suffix,source]
    rw [hsize]
    have h := hb (d+2) (by omega)
    simp only [B,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,TimeBound.eval_variable,
      TimeBound.eval_const,TimeBound.eval_numeral] at h
    change mul.size ≤ 1 + q*U*(d+2)^u at hs
    omega
  · intro m a
    let x := Sum.elim (one m) (productWires l (fun i => (a (enum i) : Deck l)))
    have ht : (table.subst (Frame.initial (Sum.inl : M → M ⊕ ProductSlots q l))).eval x = tab m := by
      have hi : (Frame.initial (Sum.inl : M → M ⊕ ProductSlots q l)).eval x = one m := funext fun _ => by simp [x]
      funext j
      rw [Frame.subst_eval,hi,et]
    have hp : (Frame.initial pair).eval (source.eval x) = Sum.elim
        (productWires l (fun i => (a (enum i) : Deck l)))
        (productWires l (fun i => productAddress d (productProjection (d+1) (point m)) (enum i))) := by
      funext j
      cases j with
      | inl j => simp [pair,source,x]
      | inr j => simp only [pair,Frame.initial_eval,Sum.elim_inr,source,Frame.withInput_eval_inr,ht,tab,Sum.elim_inl]
    funext j
    cases j with
    | inl j =>
      change (suffix.subst source).eval x (.inl j) = _
      simp only [Frame.subst_eval,suffix,parallelFrame_eval_inl,hp,em,quotientRow,Sum.elim_inl,
        productAddress_translate]
      rfl
    | inr j =>
      change (suffix.subst source).eval x (.inr j) = _
      rw [Frame.subst_eval]
      simp only [suffix,parallelFrame_eval_inr,Frame.initial_eval,source,Frame.withInput_eval_inr,ht,
        tab,Sum.elim_inr,quotientRow,relative_projection,normalize_translate]

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
