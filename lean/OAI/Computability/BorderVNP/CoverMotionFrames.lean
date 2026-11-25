import OAI.Computability.BorderVNP.CoverAddressCoding
import OAI.Computability.BorderVNP.CoverMotionProgram
import OAI.Computability.VPVNP.VerifierMachineSplice

/-! # Shared Boolean frames for quaternion arithmetic

The stack procedures for modular products and cleared motions each give one
Boolean frame for every cover depth. The frame works simultaneously on all
addresses of that depth. Prefixing a fixed binary modulus or unary depth
costs at most one gate per output wire.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting RationalHitting.StackLanguage BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame Expr)

private def prependExpr (I O : ℕ) (pre : List Bool) (j : Slots O) : Expr (Slots I) :=
  if j.1.val < pre.length then .const (decide (pre[j.1.val]? = j.2))
  else if h : j.1.val - pre.length < I then .input (⟨j.1.val-pre.length,h⟩, j.2)
  else .const (decide ((none : Option Bool) = j.2))

/-- Prefix literal bits to an incoming serialized word, padding or truncating
at the prescribed output width. -/
noncomputable def prependFrame (I O : ℕ) (pre : List Bool) : Frame (Slots I) (Slots O) :=
  (Frame.initial id).step (prependExpr I O pre)

/-- All slots of a bounded input are read from their correct shifted positions. -/
theorem prependFrame_correct (I O : ℕ) (pre x : List Bool) (hx : x.length ≤ I) :
    (prependFrame I O pre).eval (padded I x) = padded O (pre ++ x) := by
  funext ⟨j,b⟩
  rw [prependFrame,Frame.step_eval]
  by_cases h : j.val < pre.length
  · simp [prependExpr,h,padded,List.getElem?_append_left h,
      BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]
  · have he := List.getElem?_append_right (l₂ := x) (le_of_not_gt h)
    by_cases hj : j.val-pre.length < I
    · simp [prependExpr,h,hj,padded,he,
        BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]
    · have hz : x[j.val-pre.length]? = none := List.getElem?_eq_none (by omega)
      simp [prependExpr,h,hj,padded,he,hz,
        BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]

/-- The fixed prefix adds at most one gate per Boolean output wire. -/
theorem prependFrame_size (I O : ℕ) (pre : List Bool) :
    (prependFrame I O pre).size ≤ 3*O := by
  have h := Frame.step_size_le (Frame.initial id) (prependExpr I O pre) 1
    (by intro i; unfold prependExpr; split_ifs <;> rfl)
  simpa [prependFrame,Slots,mul_comm] using h

/-- Simulating any fixed polynomial-time procedure on a polynomial width
uses a polynomial number of shared gates, uniformly in the depth. -/
theorem procedureFrames {A B : Type} {ca : A → List Bool} {cb : B → List Bool} {f : A → B}
    (p : Procedure ca cb f) (widthBound : TimeBound) :
    ∃ C e : ℕ, ∀ d : ℕ,
      let W := widthBound.eval (d+1)
      (programFrame p.program p.input p.output W (p.bound.eval W)).size ≤ C*(d+1)^e := by
  obtain ⟨c,hc⟩ := programFrame_size p.program p.input p.output
  let bound : TimeBound := .const c * (widthBound + p.bound.comp widthBound + 3)^2
  obtain ⟨C,e,_,_,hb⟩ := bound.growth
  refine ⟨C,e,fun d => (hc _ _).trans ?_⟩
  simpa only [bound,TimeBound.eval_mul,TimeBound.eval_pow,TimeBound.eval_add,
    TimeBound.eval_comp,TimeBound.eval_const,TimeBound.eval_numeral] using hb (d+1) (by omega)

/-- Every depth has a single polynomial-size frame for modular multiplication
of the two serialized input addresses. Its output captures the complete product. -/
theorem binaryProduct_frames :
    ∃ C e : ℕ, ∀ l : ℕ, ∃ f : Frame (Slots (80*(l+1))) (Slots (width l)),
      f.size ≤ C*(l+1)^e ∧ ∀ x y : Address l,
      f.eval (padded _ (code ((⟨7^l, by positivity⟩, binaryCoords l x, binaryCoords l y)
        : ProductInput))) = wires l (x*y) := by
  obtain ⟨p,hp⟩ := binaryProduct_bit_steps
  obtain ⟨C,e,hce⟩ := procedureFrames p (80*TimeBound.variable)
  refine ⟨C,e,?_⟩
  intro l
  let W := 80*(l+1)
  let f := programFrame p.program p.input p.output W (p.bound.eval W)
  have hwidth : width l ≤ W := by dsimp [width,W]; omega
  let pick (j : Slots (width l)) : Slots W := (j.1.castLE hwidth,j.2)
  refine ⟨f.select pick, ?_, ?_⟩
  · exact hce l
  · intro x y
    obtain ⟨t,ht,he⟩ := hp l x y
    have hw := binaryProduct_input_length l x y
    have hv := programFrame_correct p.program p.input p.output he (W := W) (by omega) ht
    funext i
    exact (Frame.select_eval ..).trans (congrFun hv (pick i))

/-- A fixed cleared motion acts on canonical deck-address wires at polynomial
cost in the running depth. Its finite low table is built into the program. -/
theorem motionDeck_frames {g : Cover.Frame.SL} {a : ℕ} (hg : Cover.Frame.Clears g a) :
    ∃ C e : ℕ, ∀ d : ℕ, ∃ f : Frame (Slots (width (d+2*a))) (Slots (width d)),
      f.size ≤ C*(d+1)^e ∧ ∀ (hd : 1 ≤ d) (x : Deck (d+2*a)),
      f.eval (deckWires _ x) = deckWires _ (Cover.Frame.motionDeck hg hd x) := by
  obtain ⟨u,v,p,hp⟩ := Cover.Frame.motionDeck_bit_steps hg
  let wt : TimeBound := 30 * (TimeBound.variable + .const (2*a))
  obtain ⟨C,e,hce⟩ := procedureFrames p wt
  let budget : TimeBound := 3*wt + .const C * TimeBound.variable^e
  obtain ⟨D,k,_,_,hbudget⟩ := budget.growth
  refine ⟨D,k,?_⟩
  intro d
  let W := width (d+2*a)
  have hw : wt.eval (d+1) = W := by simp [wt,W,width]; omega
  let pre := codeWord (code (⟨d⟩ : Unary))
  let f := programFrame p.program p.input p.output W (p.bound.eval W)
  let combined := f.subst (prependFrame W W pre)
  have hwidth : width d ≤ W := by dsimp [width,W]; omega
  let pick (j : Slots (width d)) : Slots W := (j.1.castLE hwidth,j.2)
  refine ⟨combined.select pick, ?_, ?_⟩
  · have hs := hce d
    dsimp only at hs
    rw [hw] at hs
    have hh := hbudget (d+1) (by omega)
    simp only [budget,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,hw,
      TimeBound.eval_const,TimeBound.eval_pow,TimeBound.eval_variable] at hh
    simpa only [Frame.select_size,combined,Frame.subst_size] using
      (Nat.add_le_add (prependFrame_size W W pre) hs).trans hh
  · intro hd x
    obtain ⟨t,ht,he⟩ := hp d hd x
    have hx := Cover.Frame.motionDeck_input_length d a (deckAddress _ x).val
    have hv := programFrame_correct p.program p.input p.output he (W := W) (by dsimp [W,width]; omega) ht
    have hpref := prependFrame_correct W W pre (word _ (deckAddress _ x).val) (word_length ..)
    funext i
    change ((f.subst (prependFrame W W pre)).select pick).eval (padded W _) i = _
    rw [Frame.select_eval,Frame.subst_eval,hpref]
    exact congrFun hv (pick i)

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
