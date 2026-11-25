import OAI.Computability.BorderVNP.CrossingCoefficientFrame
import OAI.Computability.BorderVNP.CrossingDualPaths

/-!
# Combining the scalar and exterior word witnesses

A bare mode has one word witness and one scalar witness. A marked mode also guesses the
intermediate derivative subset and a second word witness for its dual coordinate. All the
witness banks are independent, so summing over them gives the product of the integer
entries and, for the marked mode, the required sum over derivative subsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.KernelFrame

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open Lemmata.FockCircuits.CrossingCircuit
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open CoefficientFrame (Query value query multiplier times times_value times_size)
open scoped BigOperators

/-- Occupancy masks of the word, the output state and the input state. -/
abbrev WordQuery (L : ℕ) := Fin L ⊕ Fin L ⊕ Fin L

/-- One deletion flag, mode code and multiplicity code per derivative order. -/
abbrev Packets (L : ℕ) := Fin L × (Unit ⊕ Fin (2*L+1) ⊕ Fin (2*L+1))

/-- Gates checking one normally ordered word. -/
abbrev WordCircuit (L : ℕ) := Frame (WordQuery L ⊕ Packets L) Bool

/-- The basis-state masks supplied to a word circuit. -/
def wordQuery {L : ℕ} (A I J : Index L) : WordQuery L → Bool :=
  Sum.elim (MaskCounter.mask A) (Sum.elim (MaskCounter.mask I) (MaskCounter.mask J))

/-- The integer path sum computed by a word circuit in either of the two fields. -/
def wordEntry {L : ℕ} (dual : Bool) (A I J : Index L) : ℤ :=
  let word := if dual then dualWord A else derivativeWord A
  ∑ p : ModePath L word.length, modeWeight word p I.val J.val

/-- Specification of the reusable single-word checking block. -/
def ChecksWord {L : ℕ} (dual : Bool) (f : WordCircuit L) : Prop := ∀ A I J : Index L,
  ∑ y : Packets L → Bool, value (f.eval (Sum.elim (wordQuery A I J) y)) = wordEntry dual A I J

/-- Guessing one bit per mode enumerates the finite derivative subsets exactly once. -/
def maskEquiv (L : ℕ) : Index L ≃ (Fin L → Bool) where
  toFun := MaskCounter.mask
  invFun x := ⟨(Finset.univ.filter fun i : Fin L => x i).map Fin.valEmbedding,
    Finset.mem_powerset.mpr (by intro k hk; obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk; exact Finset.mem_range.mpr i.isLt)⟩
  left_inv A := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      MaskCounter.mask, decide_eq_true_eq]
    constructor
    · rintro ⟨j,h,rfl⟩; exact h
    · intro hi; exact ⟨⟨i, Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) hi)⟩, hi, rfl⟩
  right_inv x := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp [MaskCounter.mask, Fin.val_inj]

private theorem sum_split {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (f : (A ⊕ B → Bool) → ℤ) :
    ∑ z, f z = ∑ a : A → Bool, ∑ b : B → Bool, f (Sum.elim a b) := by
  rw [← ((Equiv.sumArrowEquivProdArrow A B Bool).symm.sum_comp f), Fintype.sum_prod_type]
  rfl

/-- Separate witness banks for the bare and marked modes. -/
abbrev Hidden : Bool → ℕ → ℕ → Type
  | true, L, W => Fin L ⊕ Packets L ⊕ Packets L ⊕ Fin (CoefficientFrame.bits L W)
  | false, L, W => Packets L ⊕ Fin (CoefficientFrame.bits L W)

instance (marked : Bool) (L W : ℕ) : Fintype (Hidden marked L W) :=
  match marked with
  | false => inferInstanceAs (Fintype (Packets L ⊕ Fin (CoefficientFrame.bits L W)))
  | true => inferInstanceAs (Fintype (Fin L ⊕ Packets L ⊕ Packets L ⊕ Fin (CoefficientFrame.bits L W)))

instance (marked : Bool) (L W : ℕ) : DecidableEq (Hidden marked L W) :=
  match marked with
  | false => inferInstanceAs (DecidableEq (Packets L ⊕ Fin (CoefficientFrame.bits L W)))
  | true => inferInstanceAs (DecidableEq (Fin L ⊕ Packets L ⊕ Packets L ⊕ Fin (CoefficientFrame.bits L W)))

private abbrev BareInput (L W : ℕ) := Query L W ⊕ Hidden false L W
private abbrev MarkInput (L W : ℕ) := Query L W ⊕ Hidden true L W

private def bareWordWire {L W : ℕ} : WordQuery L ⊕ Packets L → BareInput L W :=
  Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl)

private def bareScalarWire {L W : ℕ} : Query L W ⊕ Fin (CoefficientFrame.bits L W) → BareInput L W :=
  Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)

private noncomputable def bareFrame {L : ℕ} (W : ℕ) (deriv : WordCircuit L) : Frame (BareInput L W) Bool :=
  times (deriv.subst (Frame.initial bareWordWire))
    ((CoefficientFrame.frame L W false).subst (Frame.initial bareScalarWire))

private def dualInputs {L W : ℕ} : WordQuery L ⊕ Packets L → Expr (MarkInput L W)
  | .inl (.inl i) => .input (.inl (.inr (.inl i)))
  | .inl (.inr (.inl i)) => .input (.inr (.inl i))
  | .inl (.inr (.inr _)) => .const false
  | .inr p => .input (.inr (.inr (.inl p)))

private def derivInputs {L W : ℕ} : WordQuery L ⊕ Packets L → MarkInput L W
  | .inl (.inl i) => .inr (.inl i)
  | .inl (.inr ij) => .inl (.inr (.inr ij))
  | .inr p => .inr (.inr (.inr (.inl p)))

private def markInputs {L W : ℕ} : Query L W ⊕ Fin (CoefficientFrame.bits L W) → MarkInput L W
  | .inl (.inl r) => .inl (.inl r)
  | .inl (.inr (.inl i)) => .inr (.inl i)
  | .inl (.inr (.inr ij)) => .inl (.inr (.inr ij))
  | .inr x => .inr (.inr (.inr (.inr x)))

private noncomputable def markedFrame {L : ℕ} (W : ℕ) (dual deriv : WordCircuit L) : Frame (MarkInput L W) Bool :=
  times (dual.subst ((Frame.initial id).step dualInputs))
    (times (deriv.subst (Frame.initial derivInputs)) ((CoefficientFrame.frame L W true).subst (Frame.initial markInputs)))

private def vac (L : ℕ) : Index L := ⟨∅, by simp⟩

private theorem value_subst {X Y : Type*} [Fintype X] [Fintype Y] (f : Frame Y Bool)
    (g : Frame X Y) (x : X → Bool) : value ((f.subst g).eval x) = value (f.eval (g.eval x)) := by
  simp only [value, Frame.subst_eval]

private theorem word_deriv {L : ℕ} (A I J : Index L) :
    wordEntry false A I J = matrix ℤ L (Pi.single A 1) I J := by
  rw [matrix_single_paths, one_mul]
  rfl

private theorem word_dual_vac {L : ℕ} (A B : Index L) : wordEntry true A B (vac L) = dualState ℤ L A.val B :=
  (dualState_paths A B).symm

private theorem bare_sum {L W : ℕ} (f : WordCircuit L) (hf : ChecksWord false f)
    (r : Fin W) (A I J : Index L) :
    ∑ y : Hidden false L W → Bool, value ((bareFrame W f).eval (Sum.elim (query r A I J) y)) =
      oppositeMode ℤ L W r (dualSign A.val • Pi.single A 1) I J := by
  rw [sum_split]
  simp only [bareFrame, times_value, value_subst]
  have h1 (p : Packets L → Bool) (s : Fin (CoefficientFrame.bits L W) → Bool) :
      (Frame.initial bareWordWire).eval (Sum.elim (query r A I J) (Sum.elim p s)) = Sum.elim (wordQuery A I J) p := by
    funext k; cases k <;> exact Frame.initial_eval _ _ _
  have h2 (p : Packets L → Bool) (s : Fin (CoefficientFrame.bits L W) → Bool) :
      (Frame.initial bareScalarWire).eval (Sum.elim (query r A I J) (Sum.elim p s)) = Sum.elim (query r A I J) s := by
    funext k; cases k <;> exact Frame.initial_eval _ _ _
  simp only [h1, h2, ← Finset.mul_sum, CoefficientFrame.frame_sum, ← Finset.sum_mul]
  rw [hf A I J, word_deriv]
  simp only [oppositeMode, diagonal, multiplier, Bool.false_eq_true, ite_false, matrix_smul,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

private theorem marked_sum {L W : ℕ} (dual deriv : WordCircuit L) (hdual : ChecksWord true dual)
    (hderiv : ChecksWord false deriv) (r : Fin W) (A I J : Index L) :
    ∑ y : Hidden true L W → Bool, value ((markedFrame W dual deriv).eval (Sum.elim (query r A I J) y)) =
      markedMode ℤ L W r (dualState ℤ L A.val) I J := by
  rw [sum_split, ← (maskEquiv L).sum_comp]
  simp_rw [sum_split (B := Packets L ⊕ Fin (CoefficientFrame.bits L W)),
    sum_split (B := Fin (CoefficientFrame.bits L W))]
  let inputs (B : Index L) (p d : Packets L → Bool) (s : Fin (CoefficientFrame.bits L W) → Bool) :
      MarkInput L W → Bool := Sum.elim (query r A I J) (Sum.elim (MaskCounter.mask B) (Sum.elim p (Sum.elim d s)))
  have h1 B p d s : ((Frame.initial id).step (dualInputs (L := L) (W := W))).eval (inputs B p d s) =
      Sum.elim (wordQuery A B (vac L)) p := by
    funext k; rcases k with (i | j | k) | q <;> simp [dualInputs, Expr.eval, inputs, query, wordQuery, vac, MaskCounter.mask]
  have h2 B p d s : (Frame.initial (derivInputs (L := L) (W := W))).eval (inputs B p d s) =
      Sum.elim (wordQuery B I J) d := by
    funext k; rcases k with (i | j | k) | q <;> exact Frame.initial_eval _ _ _
  have h3 B p d s : (Frame.initial (markInputs (L := L) (W := W))).eval (inputs B p d s) =
      Sum.elim (query r B I J) s := by
    funext k; rcases k with (i | j | k | t) | q <;> exact Frame.initial_eval _ _ _
  change ∑ B : Index L, ∑ p, ∑ d, ∑ s, value ((markedFrame W dual deriv).eval (inputs B p d s)) = _
  simp only [markedFrame, times_value, value_subst, h1, h2, h3, ← Finset.mul_sum,
    CoefficientFrame.frame_sum, ← Finset.sum_mul]
  simp only [multiplier, ite_true, markedMode, diagonal]
  split_ifs with h
  · rw [matrix_eq_sum_single]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mark_apply, Int.cast_id]
    apply Finset.sum_congr rfl
    intro B _
    rw [hdual A B (vac L), hderiv B I J, word_dual_vac, word_deriv]
    ring
  · simp

/-- Assemble the two word blocks with a binary signed scalar lookup. -/
noncomputable def assemble {L : ℕ} (marked : Bool) (W : ℕ) (dual deriv : WordCircuit L) :
    Frame (Query L W ⊕ Hidden marked L W) Bool :=
  match marked with
  | true => markedFrame W dual deriv
  | false => bareFrame W deriv

/-- A correctly implemented word checker yields the exact integer mode entry in both orientations. -/
theorem assemble_sum {L W : ℕ} (marked : Bool) (dual deriv : WordCircuit L)
    (hdual : ChecksWord true dual) (hderiv : ChecksWord false deriv) (r : Fin W) (A I J : Index L) :
    ∑ y : Hidden marked L W → Bool, value ((assemble marked W dual deriv).eval (Sum.elim (query r A I J) y)) =
      if marked then markedMode ℤ L W r (dualState ℤ L A.val) I J
      else oppositeMode ℤ L W r (dualSign A.val • Pi.single A 1) I J := by
  cases marked
  · exact bare_sum deriv hderiv r A I J
  · exact marked_sum dual deriv hdual hderiv r A I J

/-- Number of guessed bits when the banks are flattened to a single Boolean witness word. -/
def width (marked : Bool) (L W : ℕ) := Fintype.card (Hidden marked L W)

private theorem width_numeric (n : ℕ) : n + n*(1+(2*n+1)+(2*n+1)) + n*(1+(2*n+1)+(2*n+1)) +
    (n + n*(2*n+1)+1) ≤ (n+2)^6 := by
  zify
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- A uniform polynomial bound on all guessed bits. -/
theorem width_le (marked : Bool) (L W : ℕ) : width marked L W ≤ (L+W+2)^100 := by
  let n := L+W
  have hL : L ≤ n := Nat.le_add_right _ _
  have hW : W ≤ n := Nat.le_add_left _ _
  have hb : width marked L W ≤ n + n*(1+(2*n+1)+(2*n+1)) + n*(1+(2*n+1)+(2*n+1)) +
      (n + n*(2*n+1)+1) := by
    cases marked
    · change Fintype.card (Packets L ⊕ Fin (CoefficientFrame.bits L W)) ≤ _
      simp only [Packets, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin,
        CoefficientFrame.bits, CoefficientFrame.cap]
      apply Nat.add_le_add
      · calc
          _ ≤ n*(1+(2*n+1)+(2*n+1)) := by simp only [Nat.add_assoc]; gcongr
          _ ≤ _ := Nat.le_add_left _ _
      · gcongr
    · change Fintype.card (Fin L ⊕ Packets L ⊕ Packets L ⊕ Fin (CoefficientFrame.bits L W)) ≤ _
      simp only [Packets, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin,
        CoefficientFrame.bits, CoefficientFrame.cap, Nat.add_assoc]
      gcongr
  exact (hb.trans (width_numeric n)).trans (Nat.pow_le_pow_right (by omega) (by decide))

private def scalarCost (L W : ℕ) : ℕ :=
  let D := CoefficientFrame.cap L
  let b := CoefficientFrame.bits L W
  3*((L+D+1) + L*((L+D+1)*8)) + (W*(D+1)^3+b)*7 + 2*(W*(D+1)^3*(1+3*b+3)+1)

private theorem scalarCost_numeric (n : ℕ) : scalarCost n n ≤ (n+2)^30 := by
  unfold scalarCost CoefficientFrame.cap CoefficientFrame.bits
  dsimp only
  zify
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem assembly_overhead (n : ℕ) : 3*n + n*(1+(2*n+1)+(2*n+1)) ≤ (n+2)^6 := by
  zify
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Polynomial size of the assembled checker from the two polynomial-size word circuits. -/
theorem assemble_size {L W : ℕ} (marked : Bool) (dual deriv : WordCircuit L)
    (hd : dual.size ≤ (L+2)^20) (hv : deriv.size ≤ (L+2)^20) :
    (assemble marked W dual deriv).size ≤ (L+W+2)^100 := by
  let n := L+W
  have hL : L ≤ n := Nat.le_add_right _ _
  have hW : W ≤ n := Nat.le_add_left _ _
  have hbase : 2 ≤ n+2 := by omega
  have mono (k t : ℕ) (h : k ≤ t) : (n+2)^k ≤ (n+2)^t := Nat.pow_le_pow_right (by omega) h
  have hc (m : Bool) : (CoefficientFrame.frame L W m).size ≤ (n+2)^30 := by
    apply (CoefficientFrame.frame_size _ _ _).trans
    change scalarCost L W ≤ _
    apply le_trans _ (scalarCost_numeric n)
    have hd : CoefficientFrame.cap L ≤ CoefficientFrame.cap n := by
      unfold CoefficientFrame.cap
      gcongr
    have hb : CoefficientFrame.bits L W ≤ CoefficientFrame.bits n n :=
      Nat.add_le_add_right (Nat.add_le_add hW hd) 1
    unfold scalarCost
    dsimp only
    repeat' first | assumption | exact le_rfl | apply Nat.add_le_add | apply Nat.mul_le_mul
  have hdu : dual.size ≤ (n+2)^30 := hd.trans ((Nat.pow_le_pow_left (Nat.add_le_add_right hL 2) _).trans (mono _ _ (by decide)))
  have hde : deriv.size ≤ (n+2)^30 := hv.trans ((Nat.pow_le_pow_left (Nat.add_le_add_right hL 2) _).trans (mono _ _ (by decide)))
  have h14 : 14 ≤ (n+2)^30 := (show 14 ≤ 2^4 by decide).trans ((Nat.pow_le_pow_left hbase 4).trans (mono _ _ (by decide)))
  apply le_trans _ (mono 33 100 (by decide))
  calc
    _ ≤ 8*(n+2)^30 := by
      cases marked
      · have ht := times_size (deriv.subst (Frame.initial (bareWordWire (L := L) (W := W))))
          ((CoefficientFrame.frame L W false).subst (Frame.initial bareScalarWire))
        simp only [Frame.subst_size, Frame.initial_size, Nat.zero_add] at ht
        change (bareFrame W deriv).size ≤ _
        change (bareFrame W deriv).size ≤ _ at ht
        have := hc false
        omega
      · have hr := Frame.step_size_le (Frame.initial (id : MarkInput L W → _)) (dualInputs (L := L) (W := W)) 1
          (by rintro ((i|j|k)|p) <;> rfl)
        simp only [Frame.initial_size, WordQuery, Packets, Fintype.card_sum, Fintype.card_prod,
          Fintype.card_unit, Fintype.card_fin, Nat.zero_add, Nat.mul_one] at hr
        have hrow : ((Frame.initial (id : MarkInput L W → _)).step dualInputs).size ≤ (n+2)^30 := by
          apply hr.trans
          apply le_trans _ ((assembly_overhead n).trans (mono _ _ (by decide)))
          rw [show 3*n = n+(n+n) by omega, Nat.add_assoc 1]
          gcongr
        have hs := times_size (deriv.subst (Frame.initial (derivInputs (L := L) (W := W))))
          ((CoefficientFrame.frame L W true).subst (Frame.initial markInputs))
        have ht := times_size (dual.subst ((Frame.initial id).step dualInputs))
          (times (deriv.subst (Frame.initial derivInputs)) ((CoefficientFrame.frame L W true).subst (Frame.initial markInputs)))
        simp only [Frame.subst_size, Frame.initial_size, Nat.zero_add] at hs ht
        change (markedFrame W dual deriv).size ≤ _ at ht ⊢
        have := hc true
        omega
    _ ≤ (n+2)^3*(n+2)^30 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase 3)
    _ = _ := by rw [← pow_add]

end Crossing.Signed.KernelFrame

end BorderVNP
end Computability
end OAI
