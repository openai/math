import OAI.Computability.BorderVNP.CoverMotionFrames
import OAI.Computability.BorderVNP.StackFramePairCode

/-! # Multiplication and projection on deck wires

Both operands to the multiplier are variable inputs. The lower-depth
projection shares one modular-remainder procedure across all depth pairs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting RationalHitting.StackLanguage BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)

/-- One polynomial-size circuit multiplies any two independently supplied
deck elements at the specified depth. -/
theorem deckMul_frames :
    ∃ C e : ℕ, ∀ l : ℕ, ∃ f : Frame (Slots (width l) ⊕ Slots (width l)) (Slots (width l)),
      f.size ≤ C*(l+1)^e ∧ ∀ x y : Deck l,
      f.eval (Sum.elim (deckWires l x) (deckWires l y)) = deckWires l (x*y) := by
  obtain ⟨C,e,hce⟩ := binaryProduct_frames
  let w : TimeBound := 30*TimeBound.variable
  let v : TimeBound := 80*TimeBound.variable
  let budget : TimeBound := 30*v*(w+1) + 3*v + .const C * TimeBound.variable^e
  obtain ⟨D,k,_,_,hbudget⟩ := budget.growth
  refine ⟨D,k,?_⟩
  intro l
  let W := 80*(l+1)
  let header := codeWord (7^l).bits
  obtain ⟨mul,hs,hm⟩ := hce l
  let pair := pairCodeFrame (width l) (width l) W
  let pre := prependFrame W W header
  refine ⟨mul.subst (pre.subst pair), ?_, ?_⟩
  · have h := hbudget (l+1) (by omega)
    simp only [budget,w,v,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_const,TimeBound.eval_variable,TimeBound.eval_pow] at h
    exact (show (mul.subst (pre.subst pair)).size ≤ 30*W*(width l+1) + 3*W + C*(l+1)^e by
      simp only [Frame.subst_size]
      exact Nat.add_le_add (Nat.add_le_add (pairCodeFrame_size ..) (prependFrame_size ..)) hs).trans h
  · intro x y
    let X := (deckAddress l x).val
    let Y := (deckAddress l y).val
    let fields := pairCode id id (word l X,word l Y)
    have hf : fields.length ≤ W := by
      have hx := binaryProduct_input_length l X Y
      change (header ++ fields).length+1 ≤ W at hx
      rw [List.length_append] at hx
      omega
    have hp := pairCodeFrame_correct (Wout := W) (word l X) (word l Y) (word_length ..) (word_length ..)
    have hpre := prependFrame_correct W W header fields hf
    funext i
    change (mul.subst (pre.subst pair)).eval (Sum.elim (padded _ (word l X)) (padded _ (word l Y))) i = _
    rw [Frame.subst_eval]
    have both := funext (Frame.subst_eval pre pair (Sum.elim (padded _ (word l X)) (padded _ (word l Y))))
    rw [both,hp,hpre]
    have hout := congrFun (hm X Y) i
    change mul.eval (padded W (header ++ fields)) i = wires l (X*Y) i at hout
    change _ = wires l (deckAddress l (x*y)).val i
    rw [map_mul]
    exact hout

private abbrev ModCoords := {m : ℕ // 0 < m} × BinaryCoords

private theorem reduce_poly : Poly (fun z : ModCoords => Cover.Frame.lowCoords z.1.val z.2) := by
  have rem {f : ModCoords → ℕ} (hf : Poly f) : Poly (fun p => f p % p.1.val) :=
    modularRemainder_poly.comp (hf.pair Poly.fst)
  exact (rem (by fun_prop)).pair ((rem (by fun_prop)).pair ((rem (by fun_prop)).pair (rem (by fun_prop))))

private theorem reduction_correct {k l : ℕ} (h : k ≤ l) (x : Deck l) :
    Cover.Frame.lowCoords (7^k) (binaryCoords l (deckAddress l x).val) =
      binaryCoords k (deckAddress k (deckReduction h x)).val := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective ((gamma l).subgroupOf (gamma 1)) x
  exact Cover.Frame.lowCoords_correct h v.val.val

/-- A polynomial number of shared gates, uniform over every shallower level,
projects a depth-`l` tile to its actual lower quotient. -/
theorem deckReduction_frames :
    ∃ C e : ℕ, ∀ (l k : ℕ) (h : k ≤ l), ∃ f : Frame (Slots (width l)) (Slots (width k)),
      f.size ≤ C*(l+1)^e ∧ ∀ x : Deck l, f.eval (deckWires _ x) = deckWires _ (deckReduction h x) := by
  obtain ⟨p⟩ := reduce_poly
  let wt : TimeBound := 40*TimeBound.variable
  obtain ⟨C,e,hce⟩ := procedureFrames p wt
  let budget : TimeBound := 3*wt + .const C * TimeBound.variable^e
  obtain ⟨D,z,_,_,hb⟩ := budget.growth
  refine ⟨D,z,?_⟩
  intro l k h
  let W := 40*(l+1)
  let pre := codeWord (7^k).bits
  let prep := prependFrame (width l) W pre
  let run := programFrame p.program p.input p.output W (p.bound.eval W)
  have hw : width k ≤ W := by dsimp [width,W]; omega
  let pick (j : Slots (width k)) : Slots W := (j.1.castLE hw,j.2)
  refine ⟨(run.subst prep).select pick, ?_, ?_⟩
  · have hs : run.size ≤ C*(l+1)^e := hce l
    have hh := hb (l+1) (by omega)
    simp only [budget,wt,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_const,TimeBound.eval_variable,TimeBound.eval_pow] at hh
    simpa only [Frame.select_size,Frame.subst_size] using
      (Nat.add_le_add (prependFrame_size (width l) W pre) hs).trans hh
  · intro x
    let X := (deckAddress l x).val
    let src : ModCoords := (⟨7^k,by positivity⟩,binaryCoords l X)
    obtain ⟨t,ht,he⟩ := p.correct src
    have hs : (code src).length+1 ≤ W := by
      change (pre ++ word l X).length+1 ≤ W
      have hx := word_length l X
      have hm := modulus_length k
      simp only [pre,List.length_append,codeWord_length,W,width] at hx ⊢
      omega
    have hv := programFrame_correct p.program p.input p.output he (W := W) (by omega) (ht.trans (p.bound.monotone hs))
    have hpre := prependFrame_correct (width l) W pre (word l X) (word_length ..)
    funext i
    change ((run.subst prep).select pick).eval (padded (width l) (word l X)) i = _
    rw [Frame.select_eval,Frame.subst_eval,hpre]
    have heval := congrFun hv (pick i)
    change _ = padded W (code (Cover.Frame.lowCoords (7^k) (binaryCoords l X))) (pick i) at heval
    rw [reduction_correct h x] at heval
    exact heval

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
