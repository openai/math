import OAI.Computability.BorderVNP.CoverMotionFrames
import OAI.Computability.BorderVNP.CoverDeckProductKey
import OAI.Computability.BorderVNP.CoverProductPlacementFrame

/-! # Inverting a dynamically selected product-deck key

The score uses pullback translation. Actual geometric posttranslation
therefore uses the inverse of the selected group element. For the norm-one
quaternion deck group, inversion conjugates the four coordinates, so its
gate cost is polynomial in the depth even before sharing it across rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting RationalHitting.StackLanguage BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)

private abbrev Input := {m : ℕ // 0 < m} × BinaryCoords

private def complement (m v : ℕ) := ((m : ℤ)-(v : ℤ)).natAbs % m

private def conjugateCoords (p : Input) : BinaryCoords :=
  let x := p.2
  (x.1,complement p.1 x.2.1,complement p.1 x.2.2.1,complement p.1 x.2.2.2)

private theorem conjugate_poly : Poly conjugateCoords := by
  have neg {f : Input → ℕ} (hf : Poly f) : Poly (fun p => complement p.1 (f p)) := by
    have h := Poly.natDifferenceAbs.comp ((Poly.subtypeVal _ |>.comp Poly.fst).pair hf)
    exact modularRemainder_poly.comp (h.pair Poly.fst)
  exact Poly.pair (by fun_prop) ((neg (by fun_prop)).pair
    ((neg (by fun_prop)).pair (neg (by fun_prop))))

private theorem complement_val {m : ℕ} [NeZero m] (v : ZMod m) :
    complement m v.val = (-v).val := by
  have hv := (ZMod.val_lt v).le
  have hd : (((m : ℤ) - (v.val : ℤ)).natAbs) = m-v.val := by
    rw [← Nat.cast_sub hv,Int.natAbs_natCast]
  rw [complement,hd,← ZMod.val_natCast,Nat.cast_sub hv,ZMod.natCast_self,zero_sub,ZMod.natCast_zmod_val]

private theorem conjugate_correct (l : ℕ) (x : Deck l) :
    conjugateCoords (⟨7^l,by positivity⟩,binaryCoords l (deckAddress l x).val) =
      binaryCoords l (deckAddress l x⁻¹).val := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective ((gamma l).subgroupOf (gamma 1)) x
  change conjugateCoords (_,binaryCoords l (reduce l v.val.val)) =
    binaryCoords l (reduce l (v.val⁻¹ : Orderˣ).val)
  rw [inverse_star v.val v.2.1]
  rcases v.val.val with ⟨s,i,j,k⟩
  simp [conjugateCoords,binaryCoords,reduce,QuaternionAlgebra.star_mk,complement_val]

/-- Modular conjugation computes the inverse deck address on the physical
coordinate bits with a polynomial number of gates in the cover depth. -/
theorem deckInverse_frames :
    ∃ C e : ℕ, ∀ l, ∃ f : Frame (Slots (width l)) (Slots (width l)),
      f.size ≤ C*(l+1)^e ∧ ∀ x : Deck l, f.eval (deckWires l x) = deckWires l x⁻¹ := by
  obtain ⟨p⟩ := conjugate_poly
  let wt : TimeBound := 40*TimeBound.variable
  obtain ⟨C,e,hce⟩ := procedureFrames p wt
  let bound : TimeBound := 3*wt + .const C*TimeBound.variable^e
  obtain ⟨D,z,_,_,hb⟩ := bound.growth
  refine ⟨D,z,?_⟩
  intro l
  let W := 40*(l+1)
  let pre := codeWord (7^l).bits
  let prep := prependFrame (width l) W pre
  let run := programFrame p.program p.input p.output W (p.bound.eval W)
  have hw : width l ≤ W := by dsimp [width,W]; omega
  let pick (j : Slots (width l)) : Slots W := (j.1.castLE hw,j.2)
  refine ⟨(run.subst prep).select pick, ?_, ?_⟩
  · have hs : run.size ≤ C*(l+1)^e := hce l
    have hh := hb (l+1) (by omega)
    simp only [bound,wt,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_const,TimeBound.eval_variable,TimeBound.eval_pow] at hh
    simpa only [Frame.select_size,Frame.subst_size] using
      (Nat.add_le_add (prependFrame_size (width l) W pre) hs).trans hh
  · intro x
    let X := (deckAddress l x).val
    let src : Input := (⟨7^l,by positivity⟩,binaryCoords l X)
    obtain ⟨t,ht,he⟩ := p.correct src
    have hs : (code src).length+1 ≤ W := by
      change (pre ++ word l X).length+1 ≤ W
      have hx := word_length l X
      have hm := modulus_length l
      simp only [pre,List.length_append,codeWord_length,W,width] at hx ⊢
      omega
    have hv := programFrame_correct p.program p.input p.output he (W := W) (by omega)
      (ht.trans (p.bound.monotone hs))
    have hpre := prependFrame_correct (width l) W pre (word l X) (word_length ..)
    funext i
    change ((run.subst prep).select pick).eval (padded (width l) (word l X)) i = _
    rw [Frame.select_eval,Frame.subst_eval,hpre]
    have heval := congrFun hv (pick i)
    change _ = padded W (code (conjugateCoords src)) (pick i) at heval
    rw [show conjugateCoords src = binaryCoords l (deckAddress l x⁻¹).val from conjugate_correct l x] at heval
    exact heval

/-- Inverting the key output by the score circuit and exposing all physical
posttranslation wires takes one modular conjugation per surface factor. -/
theorem inverseKey_frames :
    ∃ C e : ℕ, ∀ q l, ∃ f : Frame (Fin (keyWidth q l)) (ProductSlots q l),
      f.size ≤ 1+q*C*(l+1)^e ∧ ∀ h : Fin q → Deck l, f.eval (keyWord q l h) = productWires l h⁻¹ := by
  obtain ⟨C,e,hC⟩ := deckInverse_frames
  refine ⟨C,e,?_⟩
  intro q l
  obtain ⟨inv,hs,he⟩ := hC l
  let input (i : Fin q) := Frame.initial (fun b => keySlots q l (i,b))
  let each (i : Fin q) := inv.subst (input i)
  obtain ⟨all,ha,hev⟩ := Crossing.exists_parallelFrames each
  refine ⟨all.select (fun j : ProductSlots q l => ⟨j.1,j.2⟩), ?_, ?_⟩
  · have hsize : all.size ≤ 1 + q*inv.size := by simpa [each,input] using ha
    exact hsize.trans (Nat.add_le_add_left (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left q hs) 1)
  · intro h
    funext ⟨i,b⟩
    have hi : (input i).eval (keyWord q l h) = deckWires l (h i) := funext fun _ => by simp [input]
    rw [Frame.select_eval,hev,Frame.subst_eval,hi,he]
    rfl

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
