import OAI.Computability.BorderVNP.ResidueFourierEntry
import OAI.Computability.BorderVNP.ResidueIndexScale
import OAI.Computability.VPVNP.JointScalarCore
import OAI.Computability.VPVNP.LogBounds

/-! # Preprocessing the variable Laurent monomial indices in §10.2

Encode each signed coordinate by adding `H`. For shifted words `E,M,K` for
`e,μ,k`, the signed Fourier index difference `sourceIndex q (k-μ) - e` is
the difference of two unsigned words `A = qK + q-1 + H` and `B = qM + E`.
The box test uses `B ≤ A ≤ B + width`, so its verdict is correct even when
the requested difference would underflow unsigned subtraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueIndex

open VPVNP.VerifierNetwork ParseBatchSort ParseRecords ResidueBox ResidueFourier
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

/-- Three signed Laurent exponent vectors, stored with a common offset, MSB first. -/
abbrev Raw (σ : Type*) (w : ℕ) := Fin 3 × Option σ × Fin w

/-- A validity flag and one little-endian exponent word per grid coordinate. -/
abbrev Out (σ : Type*) (w : ℕ) := Unit ⊕ Option σ × Fin w

/-- Range condition on a signed index before adding the encoding offset. -/
def Fits {σ : Type*} (H : ℕ) (e : Exponent σ) : Prop :=
  ∀ i, -(H : ℤ) ≤ e i ∧ e i ≤ H

/-- Every paper box index can be encoded by offsetting all coordinates by `H`. -/
theorem fits_of_inBox {σ : Type*} {e : Exponent σ} {H : ℕ} (h : InBox H e) : Fits H e
  | none => h.1
  | some i => ⟨(by omega : -(H : ℤ) ≤ 0).trans (h.2 i).1,(h.2 i).2⟩

/-- Canonical binary query input for the row, multiplier and column exponent. -/
def encode {σ : Type*} (w H : ℕ) (e μ k : Exponent σ) : Raw σ w → Bool := fun (s,i,b) =>
  let a := if s = 0 then e i else if s = 1 then μ i else k i
  (a+H).toNat.testBit (w-1-b.val)

variable {σ : Type*} [Fintype σ] {w : ℕ}

private abbrev Words (σ : Type*) (w : ℕ) := (Fin 3 × Option σ) × Fin w

private noncomputable def scaled (q w : ℕ) : Frame (Raw σ w) (Words σ w) :=
  (scale (Fin 3 × Option σ) w w q).subst (Frame.initial fun ((s,i),b) => (s,i,b))

private def arithmetic (q H width : ℕ) (i : Option σ) (s : Fin 3) :
    Fin w → Expr (Raw σ w ⊕ Words σ w) :=
  let qa : Fin w → Expr _ := fun b => .input (.inr ((2,i),b))
  let qm : Fin w → Expr _ := fun b => .input (.inr ((1,i),b))
  let e : Fin w → Expr _ := fun b => .input (.inl (0,i,b))
  let bword := addWord qm e
  if s = 0 then addWord qa (constWord w (q-1+H))
    else if s = 1 then bword else addWord bword (constWord w width)

private noncomputable def limits (q H width w : ℕ) : Frame (Raw σ w) (Words σ w) :=
  (scaled q w).withInput.step fun ((s,i),b) => arithmetic q H width i s b

private abbrev Local (σ : Type*) (w : ℕ) := Option σ ⊕ Option σ × Fin w

private def pin (s : Fin 3) (i : Option σ) (b : Fin w) : Words σ w := ((s,i),b)

private def localBits : Local σ w → Expr (Words σ w)
  | .inl i => .not (.and (leExpr (pin 1 i) (pin 0 i)) (leExpr (pin 0 i) (pin 2 i)))
  | .inr (i,b) => subWord (fun l => .input (pin 0 i l)) (fun l => .input (pin 1 i l)) b.rev

private noncomputable def gather : Out σ w → Expr (Local σ w)
  | .inl _ => VPVNP.JointScalar.allZero (Sum.inl ∘ (Fintype.equivFin (Option σ)).symm)
  | .inr j => .input (.inr j)

/-- Joint Boolean circuit producing the shifted-box flag and all bits of the nonnegative
difference required to raise the inverse grid point to the correct Laurent power. -/
noncomputable def frame (σ : Type*) [Fintype σ] (q H width w : ℕ) : Frame (Raw σ w) (Out σ w) :=
  ((limits q H width w).step localBits).step gather

private def offset (H : ℕ) (a : ℤ) : ℕ := (a+H).toNat

private theorem offset_spec (H : ℕ) (a : ℤ) (h : -(H:ℤ) ≤ a ∧ a ≤ H) :
    (offset H a : ℤ) = a+H ∧ offset H a ≤ 2*H := by
  unfold offset
  omega

private def left (q H : ℕ) (k : ℤ) := q * offset H k + (q-1+H)
private def right (q H : ℕ) (μ e : ℤ) := q * offset H μ + offset H e

omit [Fintype σ] in
private theorem difference (q H : ℕ) (hq : 0 < q) (e μ k : Exponent σ) (i : Option σ)
    (he : Fits H e) (hm : Fits H μ) (hk : Fits H k) :
    (left q H (k i) : ℤ) - right q H (μ i) (e i) = sourceIndex q (k-μ) i - e i := by
  simp only [left,right,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ q),
    Nat.cast_one, (offset_spec _ _ (he i)).1, (offset_spec _ _ (hm i)).1,
    (offset_spec _ _ (hk i)).1, sourceIndex, Pi.sub_apply]
  ring

private theorem limits_value (q H width w : ℕ) (hq : 0 < q)
    (hw : 2*H*q+3*H+q+width+1 < 2^w) (e μ k : Exponent σ)
    (he : Fits H e) (hm : Fits H μ) (hk : Fits H k) (i : Option σ) (s : Fin 3) :
    value ((limits q H width w).eval (encode w H e μ k) ∘ pin s i) =
      if s = 0 then left q H (k i) else if s = 1 then right q H (μ i) (e i)
      else right q H (μ i) (e i) + width := by
  let x := encode w H e μ k
  let z := (scaled q w).withInput.eval x
  let sq (s : Fin 3) : Fin w → Expr (Raw σ w ⊕ Words σ w) := fun j => .input (.inr ((s,i),j))
  let er : Fin w → Expr (Raw σ w ⊕ Words σ w) := fun j => .input (.inl (0,i,j))
  have ek := (offset_spec H _ (hk i)).2
  have em := (offset_spec H _ (hm i)).2
  have ee := (offset_spec H _ (he i)).2
  have kq : q * offset H (k i) ≤ 2*H*q := by simpa [mul_comm q] using Nat.mul_le_mul_left q ek
  have mq : q * offset H (μ i) ≤ 2*H*q := by simpa [mul_comm q] using Nat.mul_le_mul_left q em
  have bitval (s : Fin 3) (a : ℤ)
      (hs : (fun j : Fin w => x (s,i,j)) = fun j => (offset H a).testBit (w-1-j.val))
      (ha : offset H a ≤ 2*H) : value (fun j : Fin w => x (s,i,j)) = offset H a := by
    rw [hs,bigValue_testBit,Nat.mod_eq_of_lt (by omega)]
  have xv0 : value (fun j : Fin w => x (0,i,j)) = offset H (e i) := bitval 0 _ (by rfl) ee
  have xv1 : value (fun j : Fin w => x (1,i,j)) = offset H (μ i) := bitval 1 _ (by rfl) em
  have xv2 : value (fun j : Fin w => x (2,i,j)) = offset H (k i) := bitval 2 _ (by rfl) ek
  have sv (s : Fin 3) (v : ℕ) (hs : value (fun j : Fin w => x (s,i,j)) = v)
      (hv : q*v < 2^w) : wordValue z (sq s) = q*v := by
    simp only [wordValue,z,sq,StatementCircuit.Expr.eval,Frame.withInput_eval_inr,scaled,Frame.subst_eval]
    let xx := (Frame.initial (fun ((t,k),b) => (t,k,b) : Words σ w → Raw σ w)).eval x
    have hx : value (fun j => xx ((s,i),j)) = v := by simpa [xx] using hs
    rw [scale_value w q xx (s,i) (by omega) (hx ▸ hv),hx]
  have sk := sv 2 _ xv2 (by omega)
  have sm := sv 1 _ xv1 (by omega)
  have se : wordValue z er = offset H (e i) := by
    simpa [wordValue,z,er,StatementCircuit.Expr.eval] using xv0
  have sb : wordValue z (addWord (sq 1) er) = right q H (μ i) (e i) := by
    rw [addWord_value z _ _ (by rw [sm,se]; omega),sm,se,right]
  have hl := constWord_value z w (q-1+H) (by omega)
  have hd := constWord_value z w width (by omega)
  simp only [limits,Function.comp_def,pin,Frame.step_eval,arithmetic]
  split_ifs with h0 h1
  · change wordValue z (addWord (sq 2) _) = left q H (k i)
    rw [addWord_value z _ _ (by rw [sk,hl]; omega),sk,hl,left]
  · exact sb
  · change wordValue z (addWord (addWord (sq 1) er) _) = _
    rw [addWord_value z _ _ (by rw [sb,hd,right]; omega),sb,hd]

/-- Exact membership test for the shifted Laurent box, including failure below the
lower face. -/
theorem frame_valid (q H width w : ℕ) (hq : 0 < q)
    (hw : 2*H*q+3*H+q+width+1 < 2^w) (e μ k : Exponent σ)
    (he : Fits H e) (hm : Fits H μ) (hk : Fits H k) :
    (frame σ q H width w).eval (encode w H e μ k) (.inl ()) = true ↔
      inShiftedBox e (sourceIndex q (k-μ)) width := by
  let z := (limits q H width w).eval (encode w H e μ k)
  have val := limits_value q H width w hq hw e μ k he hm hk
  have localOK (i : Option σ) : (localBits (Sum.inl i : Local σ w)).eval z = false ↔
      e i ≤ sourceIndex q (k-μ) i ∧ sourceIndex q (k-μ) i ≤ e i + width := by
    have h := difference q H hq e μ k i he hm hk
    simp only [localBits,StatementCircuit.Expr.eval,Bool.not_eq_false',Bool.and_eq_true,
      leExpr_eval, decide_eq_true_eq, z, val]
    norm_num
    omega
  simp only [frame, Frame.step_eval, gather, VPVNP.JointScalar.allZero_eval, decide_eq_true_eq,
    Function.comp_apply]
  constructor
  · intro h i
    exact (localOK i).mp (by simpa using h (Fintype.equivFin _ i))
  · intro h i
    exact (localOK _).mpr (h _)

/-- On a valid row, the preprocessor emits the requested inverse-monomial exponent
in little-endian order. -/
theorem frame_delta (q H width w : ℕ) (hq : 0 < q)
    (hw : 2*H*q+3*H+q+width+1 < 2^w) (e μ k : Exponent σ)
    (he : Fits H e) (hm : Fits H μ) (hk : Fits H k)
    (hv : inShiftedBox e (sourceIndex q (k-μ)) width) (i : Option σ) (b : Fin w) :
    (frame σ q H width w).eval (encode w H e μ k) (.inr (i,b)) =
      ((sourceIndex q (k-μ) i - e i).toNat).testBit b.val := by
  let z := (limits q H width w).eval (encode w H e μ k)
  let aw : Fin w → Expr (Words σ w) := fun j => .input (pin 0 i j)
  let bw : Fin w → Expr (Words σ w) := fun j => .input (pin 1 i j)
  let d := (sourceIndex q (k-μ) i - e i).toNat
  have ha : wordValue z aw = left q H (k i) := by
    simpa [wordValue,z,aw,Function.comp_def,StatementCircuit.Expr.eval] using
      limits_value q H width w hq hw e μ k he hm hk i 0
  have hb : wordValue z bw = right q H (μ i) (e i) := by
    simpa [wordValue,z,bw,Function.comp_def,StatementCircuit.Expr.eval] using
      limits_value q H width w hq hw e μ k he hm hk i 1
  have h := difference q H hq e μ k i he hm hk
  have hi := hv i
  have heq : wordValue z (subWord aw bw) = d := by
    rw [subWord_value z _ _ (by rw [ha,hb]; omega),ha,hb]
    dsimp [d]; omega
  have hd : d < 2^w := heq ▸ value_lt _
  have hx := value_injective w (heq.trans ((bigValue_testBit w d).trans (Nat.mod_eq_of_lt hd)).symm)
  simp only [frame,Frame.step_eval,gather,StatementCircuit.Expr.eval,localBits]
  change (subWord aw bw b.rev).eval z = d.testBit b.val
  simpa [Fin.val_rev,show w-1-(w-(b+1:ℕ)) = b.val by have := b.isLt; omega] using congrFun hx b.rev

/-- A sufficient word width, logarithmic even when the extraction power and chart
degree are singly exponential. -/
def workWidth (q H width : ℕ) : ℕ := Nat.clog 2 (2*H*q+3*H+q+width+2)

/-- The chosen word width avoids overflow in both endpoints of every comparison. -/
theorem workWidth_fit (q H width : ℕ) : 2*H*q+3*H+q+width+1 < 2^workWidth q H width :=
  Nat.lt_of_succ_le (Nat.le_pow_clog Nat.one_lt_two _)

/-- Polynomial bit lengths of the radius, power and interval imply polynomial working width. -/
theorem polynomiallyBounded_workWidth {q H width : ℕ → ℕ}
    (hq : VPVNP.PolynomiallyBounded fun n => Nat.clog 2 (q n))
    (hH : VPVNP.PolynomiallyBounded fun n => Nat.clog 2 (H n))
    (hw : VPVNP.PolynomiallyBounded fun n => Nat.clog 2 (width n)) :
    VPVNP.PolynomiallyBounded fun n => workWidth (q n) (H n) (width n) :=
  let c (n : ℕ) := (VPVNP.PolynomiallyBounded.const n).clog
  VPVNP.PolynomiallyBounded.clog_add (VPVNP.PolynomiallyBounded.clog_add
    (VPVNP.PolynomiallyBounded.clog_add (VPVNP.PolynomiallyBounded.clog_add
      (VPVNP.PolynomiallyBounded.clog_mul (VPVNP.PolynomiallyBounded.clog_mul (c 2) hH) hq)
      (VPVNP.PolynomiallyBounded.clog_mul (c 3) hH)) hq) hw) (c 2)

omit [Fintype σ] in
private theorem arithmetic_size (q H width : ℕ) (i : Option σ) (s : Fin 3) (b : Fin w) :
    (arithmetic q H width i s b).size ≤ 512*(w+1)^2 := by
  unfold arithmetic
  split_ifs
  · exact (sumWord_size_le false _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) b).trans (by nlinarith)
  · exact (sumWord_size_le false _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) b).trans (by nlinarith)
  · have sub (j : Fin w) : (addWord (fun b => (.input (.inr ((1,i),b)) : Expr (Raw σ w ⊕ Words σ w)))
        (fun b => .input (.inl (0,i,b))) j).size ≤ 16*w+22 :=
      sumWord_size_le false _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) j
    exact (sumWord_size_le false _ _ (16*w+22) sub (fun _ => (by
      change 1 ≤ 16*w+22; omega)) b).trans (by nlinarith)

omit [Fintype σ] in
private theorem local_size (j : Local σ w) : (localBits j).size ≤ 64*(w+1) := by
  rcases j with i | ⟨i,b⟩
  · simp only [localBits,StatementCircuit.Expr.size,leExpr_size]
    omega
  · exact (subWord_size_le _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) b.rev).trans (by omega)

private theorem gather_size (j : Out σ w) : (gather j).size ≤ 2*Fintype.card (Option σ)+2 := by
  rcases j with j | j
  · exact VPVNP.JointScalar.allZero_size _
  · change 1 ≤ 2*Fintype.card (Option σ)+2; omega

/-- Explicit bound for the shared binary preprocessor, with `h` including the parameter
coordinate and `w` the working width. -/
def budget (h w : ℕ) : ℕ :=
  (w+1)*(3*h*w*(64*(w+1))) + 3*h*w*(512*(w+1)^2) +
    (h+h*w)*(64*(w+1)) + (1+h*w)*(2*h+2)

/-- The entire shared multi-output frame has polynomial size. -/
theorem frame_size (σ : Type*) [Fintype σ] (q H width w : ℕ) :
    (frame σ q H width w).size ≤ budget (Fintype.card (Option σ)) w := by
  let h := Fintype.card (Option σ)
  have hs : (scaled (σ := σ) q w).size ≤ (w+1)*(3*h*w*(64*(w+1))) := by
    simpa only [scaled,Frame.subst_size,Frame.initial_size,zero_add,Fintype.card_prod,Fintype.card_fin,h]
      using scale_size (I := Fin 3 × Option σ) (w := w) w q
  have hl := (scaled (σ := σ) q w).withInput.step_size_le
    (fun ((s,i),b) => arithmetic q H width i s b) (512*(w+1)^2)
    (fun ((s,i),b) => arithmetic_size q H width i s b)
  change (limits (σ := σ) q H width w).size ≤ _ at hl
  simp only [Frame.withInput_size,Fintype.card_prod,Fintype.card_fin] at hl
  have hb := (limits (σ := σ) q H width w).step_size_le localBits (64*(w+1)) local_size
  have hf := ((limits (σ := σ) q H width w).step localBits).step_size_le gather (2*h+2) gather_size
  change (frame σ q H width w).size ≤ _ at hf
  simp only [Local,Out,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit] at hb hf
  exact hf.trans (Nat.add_le_add_right (hb.trans (Nat.add_le_add_right
    (hl.trans (Nat.add_le_add_right hs _)) _)) _)

/-- A polynomially bounded coordinate count and word width give polynomial gate cost. -/
theorem polynomiallyBounded_budget {h w : ℕ → ℕ}
    (hh : VPVNP.PolynomiallyBounded h) (hw : VPVNP.PolynomiallyBounded w) :
    VPVNP.PolynomiallyBounded fun n => budget (h n) (w n) :=
  let c := VPVNP.PolynomiallyBounded.const
  let sw := hw.add (c 1)
  let n := ((c 3).mul hh).mul hw
  let bit := (c 64).mul sw
  (((sw.mul (n.mul bit)).add (n.mul ((c 512).mul (sw.pow 2)))).add
    ((hh.add (hh.mul hw)).mul bit)).add (((c 1).add (hh.mul hw)).mul (((c 2).mul hh).add (c 2)))

end ResidueIndex

end BorderVNP
end Computability
end OAI
