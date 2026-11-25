import OAI.Computability.BorderVNP.CoverDeckFrameOperations
import OAI.Computability.BorderVNP.CoverDeckLookupFrame
import OAI.Computability.BorderVNP.CoverMotionFibers
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-!
# Computing the tile of a moved relative pattern

Given the deep tile address, two parallel frames compute the motion correction and
the shallower residue used to select a displacement. Their product is the geometric
placement. The polynomial gate bound depends on the motion and its clearing exponent
and works for every displacement table at every depth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)

/-- Polynomial gate bound for the actual relative-pattern placement, uniform over
arbitrary fixed displacements on the finite low-residue domain. -/
theorem placedTile_frames {g : Cover.Frame.SL} {a : ℕ} (hg : Cover.Frame.Clears g a) :
    ∃ C e : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (offset : Deck (1+2*a) → Deck (d+2*a)),
      ∃ f : Frame (Slots (width (d+2*a+2*a))) (Slots (width (d+2*a))),
        f.size ≤ C*(d+1)^e ∧ ∀ x, f.eval (deckWires _ x) =
          deckWires _ (Cover.Frame.placedTile hg hd offset x) := by
  obtain ⟨M,m,hM⟩ := motionDeck_frames hg
  obtain ⟨R,r,hR⟩ := deckReduction_frames
  obtain ⟨U,u,hU⟩ := deckMul_frames
  let k := 1+2*a
  let A := Fintype.card (Deck k)
  let out : TimeBound := TimeBound.variable + .const (2*a)
  let deep : TimeBound := out + .const (2*a)
  let lookup : TimeBound := .const (A*(9*width k+2)) + .const (90*(2*A+1)) * out
  let bound : TimeBound := (.const M * out^m + (.const R * deep^r + lookup)) + .const U * out^u
  obtain ⟨C,e,_,_,hC⟩ := bound.growth
  refine ⟨C,e,?_⟩
  intro d hd offset
  let l := d+2*a
  let z := l+2*a
  have hk : k ≤ z := by dsimp [k,z,l]; omega
  have hl : 1 ≤ l := by dsimp [l]; omega
  obtain ⟨move,hm,hmove⟩ := hM l
  obtain ⟨low,hr,hlow⟩ := hR z k hk
  obtain ⟨table,ht,htable⟩ := offsetFrame k l offset
  obtain ⟨mul,hu,hmul⟩ := hU l
  let pair := Crossing.parallelFrame move (table.subst low)
  refine ⟨mul.subst pair, ?_, ?_⟩
  · have ho : out.eval (d+1) = l+1 := by simp [out,l]; omega
    have hz : deep.eval (d+1) = z+1 := by simp [deep,ho,z]; omega
    have ht' : table.size ≤ lookup.eval (d+1) := by
      simp only [lookup,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_const,ho]
      exact ht.trans (by dsimp [width,A]; ring_nf; rfl)
    have h := Nat.add_le_add (Nat.add_le_add hm (Nat.add_le_add hr ht')) hu
    simp only [pair,Frame.subst_size,Crossing.parallelFrame_size]
    apply h.trans
    simpa only [bound,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_const,TimeBound.eval_pow,ho,hz]
      using hC (d+1) (by omega)
  · intro x
    have hpair : pair.eval (deckWires z x) = Sum.elim
        (deckWires l (Cover.Frame.motionDeck hg hl x))
        (deckWires l (offset (deckReduction hk x))) := by
      funext i
      cases i with
      | inl i => simpa only [pair,Crossing.parallelFrame_eval_inl,Sum.elim_inl] using congrFun (hmove hl x) i
      | inr i =>
        simp only [pair,Crossing.parallelFrame_eval_inr,Sum.elim_inr,Frame.subst_eval,hlow,htable]
    funext i
    rw [Frame.subst_eval,hpair]
    exact congrFun (hmul _ _) i

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
