import OAI.Computability.BorderVNP.ShortenEpochTerminalChoice
import OAI.Computability.BorderVNP.CoverProductPlacementFrame
import OAI.Computability.BorderVNP.ParseBatchVerifierConjunction

/-!
# Computing the first aligned final site move

Each candidate multiplies the source coordinates on the right by a fixed
product deck element. Comparing with the destination uses one gate row per
candidate. The old charge bit and the identity test yield the new charge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Terminal

open Cover Cover.AddressCircuit Epoch Crossing Shortening StackFrame RationalHitting
open ParseBatchVerifier
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped Classical

/-- Old charge and the two product deck words. True selects the source end. -/
abbrev CableIn (q l : ℕ) := Unit ⊕ (Bool × ProductSlots q l)

/-- The physical inputs to the move-name circuit. -/
def cableInput {q l : ℕ} (charge : Bool) (src dst : Fin q → Deck l) : CableIn q l → Bool :=
  Sum.elim (fun _ => charge) (fun j => productWires l (if j.1 then src else dst) j.2)

private def bitEqual {X : Type*} (a b : X) : Expr X :=
  .or (.and (.input a) (.input b)) (.and (.not (.input a)) (.not (.input b)))

private theorem bitEqual_eval {X : Type*} (a b : X) (x : X → Bool) :
    (bitEqual a b).eval x = true ↔ x a = x b := by
  cases ha : x a <;> cases hb : x b <;> simp [bitEqual,Expr.eval,ha,hb]

/-- One shared equality bit comparing all product-coordinate wires. -/
private noncomputable def equalWords (q l : ℕ) : Frame (ProductSlots q l ⊕ ProductSlots q l) Unit :=
  (Frame.initial id).step fun _ => every fun i : Fin (Fintype.card (ProductSlots q l)) =>
    let t := (Fintype.equivFin (ProductSlots q l)).symm i
    bitEqual (.inl t) (.inr t)

private theorem equalWords_size (q l : ℕ) :
    (equalWords q l).size ≤ 900*q*(l+1)+1 := by
  have h := Frame.step_size_le (Frame.initial (id : ProductSlots q l ⊕ ProductSlots q l → _))
    (fun _ : Unit => every fun i : Fin (Fintype.card (ProductSlots q l)) =>
      let t := (Fintype.equivFin (ProductSlots q l)).symm i
      bitEqual (.inl t) (.inr t)) (10*Fintype.card (ProductSlots q l)+1)
    (fun _ => every_size _ 9 (fun _ => le_rfl))
  simpa [equalWords,ProductSlots,Slots,width,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

private theorem equalWords_eval (q l : ℕ) (x y : Fin q → Deck l) :
    (equalWords q l).eval (Sum.elim (productWires l x) (productWires l y)) () = true ↔ x=y := by
  let z := Sum.elim (productWires l x) (productWires l y)
  have hi : (Frame.initial id).eval z = z := funext (Frame.initial_eval id z)
  change (equalWords q l).eval z () = true ↔ _
  simp only [equalWords,Frame.step_eval,hi,every_eval,bitEqual_eval,z,Sum.elim_inl,Sum.elim_inr]
  constructor
  · intro h
    funext i
    apply deckWires_injective l
    funext j
    simpa only [Equiv.symm_apply_apply,productWires] using h (Fintype.equivFin _ (i,j))
  · rintro rfl; exact fun _ => rfl

/-- Test a single right multiplication against the other end. The cost is
uniform over all fixed displacements in the current quotient. -/
theorem aligned_frames (q : ℕ) : ∃ C k : ℕ, ∀ l (step : Fin q → Deck l),
    ∃ f : Frame (CableIn q l) Unit, f.size ≤ C*(l+1)^k ∧ ∀ charge src dst,
      f.eval (cableInput charge src dst) () = true ↔ dst = src*step := by
  obtain ⟨M,m,hM⟩ := deckMul_frames
  let B : TimeBound := 2 + .const q * (.const 180 * TimeBound.variable + .const M*TimeBound.variable^m) +
    .const (900*q)*TimeBound.variable
  obtain ⟨C,k,_,_,hc⟩ := B.growth
  refine ⟨C,k,?_⟩
  intro l step
  obtain ⟨mul,hs,hmul⟩ := hM l
  let src (i : Fin q) := (Frame.initial (id : CableIn q l → _)).step
    (Sum.elim (fun j : Slots (width l) => Expr.input (.inr (true,i,j)))
      (fun j => Expr.const (deckWires l (step i) j)))
  let lane (i : Fin q) := mul.subst (src i)
  obtain ⟨bank,hbank,he⟩ := exists_parallelFrames (out := fun _ : Fin q => Slots (width l)) lane
  let pair := parallelFrame (bank.select (fun j : ProductSlots q l => ⟨j.1,j.2⟩))
    (Frame.initial fun j : ProductSlots q l => (.inr (false,j) : CableIn q l))
  refine ⟨(equalWords q l).subst pair,?_,?_⟩
  · have hsrc (i : Fin q) : (src i).size ≤ 180*(l+1) := by
      have h := Frame.step_size_le (Frame.initial (id : CableIn q l → _))
        (Sum.elim (fun j : Slots (width l) => Expr.input (.inr (true,i,j)))
          (fun j => Expr.const (deckWires l (step i) j))) 1 (by rintro (j|j) <;> rfl)
      apply h.trans
      simp [Slots,width]
      ring_nf
      rfl
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (lane i).size ≤ 180*(l+1)+M*(l+1)^m by rw [show lane i = _ from rfl,Frame.subst_size]; exact Nat.add_le_add (hsrc i) hs)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hsum
    have hout := equalWords_size q l
    simp only [Frame.subst_size,pair,parallelFrame_size,Frame.select_size,Frame.initial_size,add_zero]
    apply le_trans (b := B.eval (l+1)) _ (hc (l+1) (by omega))
    simp only [B,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_const,TimeBound.eval_numeral,
      TimeBound.eval_pow,TimeBound.eval_variable]
    omega
  · intro ch x y
    let z := cableInput ch x y
    have hr (i : Fin q) : (src i).eval z = Sum.elim (deckWires l (x i)) (deckWires l (step i)) := by
      funext j
      cases j <;> simp [src,z,cableInput,Expr.eval,productWires]
    have hp : pair.eval z = Sum.elim (productWires l (x*step)) (productWires l y) := by
      funext j
      cases j with
      | inl j =>
        simp only [pair,parallelFrame_eval_inl,Frame.select_eval,he,lane,Frame.subst_eval,hr,hmul,Sum.elim_inl]
        rfl
      | inr j => simp [pair,z,cableInput,Frame.initial_eval]
    change ((equalWords q l).subst pair).eval z () = true ↔ _
    rw [Frame.subst_eval,hp,equalWords_eval,eq_comm]

variable {I : Type} [Fintype I] {q : ℕ} (enum : Fin q ≃ I) (L : ℝ)

/-- Exact charge and first-move semantics at canonical deck addresses. -/
structure MoveSemantics (d : ℕ) (f : Frame (CableIn q (d+1)) (Unit ⊕ ↥(allowedMoves I L))) : Prop where
  /-- The old charge survives precisely when the addresses differ. -/
  charge : ∀ b (x y : I → Deck (d+1)),
    f.eval (cableInput b (x ∘ enum) (y ∘ enum)) (.inl ()) = (b && decide (x ≠ y))
  /-- The move index is one-hot at the first alignment. -/
  first : ∀ b (x y : I → Deck (d+1)) t, f.eval (cableInput b (x ∘ enum) (y ∘ enum)) (.inr t) = true ↔
    y = x * reduceMove d t.val ∧ ∀ j ∈ SiteRoutes.alignedIndices L d x y, Fintype.equivFin _ t ≤ j

set_option maxHeartbeats 1000000 in
/-- Scan the fixed move list once, including the identity used by the charge mask. -/
theorem move_frames : ∃ C k : ℕ, ∀ d, ∃ f, MoveSemantics enum L d f ∧ f.size ≤ C*(d+2)^k := by
  obtain ⟨M,m,hM⟩ := aligned_frames q
  let Move := ↥(allowedMoves I L)
  let n := Fintype.card Move
  let B : TimeBound := 1 + .const (n+1)*(.const M*TimeBound.variable^m) + .const ((n+1)*(3*n+4))
  obtain ⟨C,k,_,_,hc⟩ := B.growth
  refine ⟨C,k,?_⟩
  intro d
  let disp : Option Move → I → gamma 1 := Option.elim' 1 Subtype.val
  choose test ht he using fun s => hM (d+1) (reduceMove d (disp s) ∘ enum)
  obtain ⟨bank,hbank,hb⟩ := exists_parallelFrames (out := fun _ : Option Move => Unit) test
  let finish : Unit ⊕ Move → Expr (CableIn q (d+1) ⊕ (Σ _ : Option Move, Unit)) := Sum.elim
    (fun _ => .and (.input (.inl (.inl ()))) (.not (.input (.inr ⟨none,()⟩))))
    (fun t => .and (.input (.inr ⟨some t,()⟩))
      (every fun j : Fin n => if j < Fintype.equivFin Move t
        then .not (.input (.inr ⟨some ((Fintype.equivFin Move).symm j),()⟩)) else .const true))
  let f := bank.withInput.step finish
  have hit (b) (x y : I → Deck (d+1)) (s : Option Move) :
      bank.withInput.eval (cableInput b (x ∘ enum) (y ∘ enum)) (.inr ⟨s,()⟩) = true ↔
        y = x * reduceMove d (disp s) := by
    rw [Frame.withInput_eval_inr,hb,he]
    constructor
    · intro h; funext i; simpa [Function.comp_def] using congrFun h (enum.symm i)
    · intro h; subst y; rfl
  refine ⟨f,⟨?_,?_⟩,?_⟩
  · intro b x y
    apply Bool.eq_iff_iff.mpr
    simp only [f,Frame.step_eval,finish,Sum.elim_inl,Expr.eval,Bool.and_eq_true,Frame.withInput_eval_inl,
      Bool.not_eq_true',Bool.eq_false_iff,decide_eq_true_eq]
    change (b = true ∧ ¬ bank.withInput.eval (cableInput b (x ∘ enum) (y ∘ enum)) (.inr ⟨none,()⟩) = true) ↔ _
    rw [hit]
    have h : reduceMove d (disp none) = 1 := funext fun _ => rfl
    rw [h,mul_one]; exact and_congr_right fun _ => ne_comm
  · intro b x y t
    simp only [f,Frame.step_eval,finish,Sum.elim_inr,Expr.eval,Bool.and_eq_true,every_eval,hit]
    apply and_congr_right
    intro _
    constructor
    · intro h j hj
      apply le_of_not_gt
      intro hlt
      have hl : j < Fintype.equivFin Move t := hlt
      have hno := h j
      rw [ite_eq_left hl] at hno
      change (! bank.withInput.eval (cableInput b (x ∘ enum) (y ∘ enum))
        (.inr ⟨some ((Fintype.equivFin Move).symm j),()⟩)) = true at hno
      have hy := (hit b x y (some ((Fintype.equivFin Move).symm j))).mpr (Finset.mem_filter.mp hj).2
      rw [hy] at hno; contradiction
    · intro h j
      by_cases hj : j < Fintype.equivFin Move t
      · rw [ite_eq_left hj]
        change (! bank.withInput.eval (cableInput b (x ∘ enum) (y ∘ enum))
          (.inr ⟨some ((Fintype.equivFin Move).symm j),()⟩)) = true
        rw [Bool.not_eq_true',Bool.eq_false_iff]
        intro heq
        let t' : Move := (Fintype.equivFin Move).symm j
        have hs : y = x * reduceMove d t'.val := (hit b x y (some t')).mp heq
        have hm : j ∈ SiteRoutes.alignedIndices L d x y := Finset.mem_filter.mpr ⟨Finset.mem_univ j,hs⟩
        exact hj.not_ge (h j hm)
      · simp [hj,Expr.eval]
  · have hn : Fintype.card (Unit ⊕ Move) = n+1 := by simp [n,Nat.add_comm]
    have hbnd := Frame.step_size_le bank.withInput finish (3*n+4) (by
      rintro (u|t)
      · change 4 ≤ _; omega
      · change 1 + _ + 1 ≤ _
        have h := every_size (fun j : Fin n => if j < Fintype.equivFin Move t
          then Expr.not (Expr.input (Sum.inr (⟨some ((Fintype.equivFin Move).symm j),()⟩ : Σ _ : Option Move,Unit)))
          else (Expr.const true : Expr (CableIn q (d+1) ⊕ (Σ _ : Option Move,Unit)))) 2
          (fun j => by split <;> simp [Expr.size])
        omega)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ht i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_option,nsmul_eq_mul] at hsum
    rw [Frame.withInput_size,hn] at hbnd
    have h := hc (d+2) (by omega)
    simp only [B,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_const,TimeBound.eval_numeral,
      TimeBound.eval_pow,TimeBound.eval_variable] at h
    change (bank.withInput.step finish).size ≤ _
    apply hbnd.trans
    have hs' : bank.size ≤ 1+(n+1)*(M*(d+2)^m) := hbank.trans (Nat.add_le_add_left hsum 1)
    omega

end PackedHistoryCircuit.Terminal

end BorderVNP
end Computability
end OAI
