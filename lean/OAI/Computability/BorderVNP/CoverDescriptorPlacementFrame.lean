import OAI.Computability.BorderVNP.CoverProductPlacementFrame

/-! # Placing dynamically typed segment rows

A finite catalog assigns a displacement table to each relative descriptor.
The row carries its catalog index in one-hot form. All coordinates of the
output consult the same index and the same tuple of deck translations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

private noncomputable def selectBit {T X Y : Type*} [Fintype T] (j : Y) :
    Expr ((T ⊕ X) ⊕ (Σ _ : T, Y)) :=
  Expr.disjoin (Finset.univ.toList.map fun t : T =>
    .and (.input (.inl (.inl t))) (.input (.inr ⟨t,j⟩)))

private theorem selectBit_size {T X Y : Type*} [Fintype T] (j : Y) :
    (selectBit (T := T) (X := X) j).size ≤ 4*Fintype.card T+1 := by
  apply (Expr.size_disjoin_le _ 3 ?_).trans
  · simp [mul_comm]
  · intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    rfl

/-- Dispatch a family of shared circuits on a one-hot type index. -/
theorem catalogDispatch {T X Y : Type*} [Fintype T] [DecidableEq T] [Fintype X] [Fintype Y]
    (rows : T → Frame X Y) :
    ∃ f : Frame (T ⊕ X) Y,
      f.size ≤ 1 + ∑ t, (rows t).size + Fintype.card Y*(4*Fintype.card T+1) ∧
      ∀ t x, f.eval (Sum.elim (fun u => decide (u=t)) x) = (rows t).eval x := by
  let fromRow := Frame.initial (Sum.inr : X → T ⊕ X)
  let bank (t : T) := (rows t).subst fromRow
  obtain ⟨p,hs,he⟩ := Crossing.exists_parallelFrames bank
  refine ⟨p.withInput.step selectBit, ?_, ?_⟩
  · have h := Frame.step_size_le p.withInput (selectBit (Y := Y)) _ selectBit_size
    exact h.trans (Nat.add_le_add_right (by simpa only [Frame.withInput_size,bank,
      Frame.subst_size,fromRow,Frame.initial_size,zero_add] using hs) _)
  · intro t x
    let v := Sum.elim (fun u => decide (u=t)) x
    have hi : fromRow.eval v = x := funext fun j => by simp [fromRow,v]
    have hbank (u : T) (j : Y) : p.withInput.eval v (.inr ⟨u,j⟩) = (rows u).eval x j := by
      rw [Frame.withInput_eval_inr,he,Frame.subst_eval,hi]
    have htype (u : T) : p.withInput.eval v (.inl (.inl u)) = decide (u=t) := by
      rw [Frame.withInput_eval_inl]; rfl
    funext j
    rw [Frame.step_eval]
    apply Bool.eq_iff_iff.mpr
    change (selectBit j).eval (p.withInput.eval v) = true ↔ (rows t).eval x j = true
    simp [selectBit,Expr.eval_disjoin_true,Expr.eval,htype,hbank]

/-- A finite type tag selects the displacement table dynamically in one
product-placement frame. The gate bound is uniform in the tables and the
permutation of the surface factors. -/
theorem descriptorPlacement_frames {T : Type*} [Fintype T] [DecidableEq T] {q a : ℕ}
    {g : Fin q → Cover.Frame.SL} (hg : ∀ i, Cover.Frame.Clears (g i) a) :
    ∃ C e : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (perm : Equiv.Perm (Fin q))
      (offset : T → Fin q → Deck (1+2*a) → Deck (d+2*a)),
      ∃ f : Frame (T ⊕ (ProductSlots q (d+2*a) ⊕ ProductSlots q (d+2*a+2*a)))
        (ProductSlots q (d+2*a)), f.size ≤ C*(d+1)^e ∧ ∀ t shift x,
      f.eval (Sum.elim (fun u => decide (u=t)) (Sum.elim (productWires _ shift) (productWires _ x))) =
        productWires _ (translatedProductPlacement hg hd perm (offset t) shift x) := by
  obtain ⟨M,m,hM⟩ := translatedProductPlacement_frames hg
  let A := Fintype.card T
  let out : TimeBound := TimeBound.variable + .const (2*a)
  let bound : TimeBound := 1 + .const (A*M) * TimeBound.variable^m +
    .const (90*q*(4*A+1)) * out
  obtain ⟨C,e,_,_,hb⟩ := bound.growth
  refine ⟨C,e,?_⟩
  intro d hd perm offset
  let l := d+2*a
  choose row hsize heval using fun t => hM d hd perm (offset t)
  obtain ⟨f,hf,he⟩ := catalogDispatch row
  refine ⟨f, ?_, ?_⟩
  · have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hsize i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    have ho : out.eval (d+1) = l+1 := by simp [out,l]; omega
    have hh := hb (d+1) (by omega)
    simp only [bound,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_const,TimeBound.eval_pow,
      TimeBound.eval_variable,TimeBound.eval_numeral,ho] at hh
    apply hf.trans
    calc
      _ ≤ 1 + (A * (M*(d+1)^m)) + Fintype.card (ProductSlots q l)*(4*A+1) :=
        Nat.add_le_add_right (Nat.add_le_add_left hs _) _
      _ = 1 + (A*M)*(d+1)^m + (90*q*(4*A+1))*(l+1) := by
        simp [ProductSlots,Slots,width]; ring
      _ ≤ _ := hh
  · intro t shift x
    rw [he,heval]

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
