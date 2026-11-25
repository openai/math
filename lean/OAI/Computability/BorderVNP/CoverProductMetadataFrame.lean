import OAI.Computability.BorderVNP.CoverDeckFrameOperations
import OAI.Computability.BorderVNP.CoverDeckLookupFrame
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-!
# Relative metadata selected by low product-tile addresses

A relative catalog entry is supplied by its one-hot type and the current
product tile by its canonical deck wires. Each coordinate is projected to the
fixed low quotient before a single finite lookup emits all requested
metadata bits. The lookup table can contain segment IDs, bins, or histogram
positions, and its gate bound is uniform in the high cover depth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)

/-- Dynamic relative type and product-address input for a finite metadata table. -/
def metadataInput {T : Type*} [DecidableEq T] {q : ℕ} (l : ℕ) (t : T) (x : Fin q → Deck l) :
    T ⊕ (Fin q × Slots (width l)) → Bool :=
  Sum.elim (fun s => decide (s=t)) (fun p => deckWires l (x p.1) p.2)

private theorem metadataInput_injective {T : Type*} [DecidableEq T] (q k : ℕ) :
    Function.Injective (fun p : T × (Fin q → Deck k) => metadataInput k p.1 p.2) := by
  intro a b h
  apply Prod.ext
  · have he := congrFun h (.inl a.1)
    simpa [metadataInput] using he
  · funext i
    apply deckWires_injective k
    funext j
    exact congrFun h (.inr (i,j))

/-- A polynomial-size frame performs any fixed finite lookup indexed by the
one-hot relative type and all low residues of a `q`-factor tile. All table
entries share the same actual high-to-low quotient computations. -/
theorem productMetadataFrames {T I : Type*} [Fintype T] [DecidableEq T] [Fintype I]
    (q k : ℕ) :
    ∃ C e : ℕ, ∀ (l : ℕ) (h : k ≤ l) (table : T → (Fin q → Deck k) → I → Bool),
      ∃ f : Frame (T ⊕ (Fin q × Slots (width l))) I, f.size ≤ C*(l+1)^e ∧
        ∀ (t : T) (x : Fin q → Deck l),
          f.eval (metadataInput l t x) = table t (fun i => deckReduction h (x i)) := by
  obtain ⟨D,e,hD⟩ := deckReduction_frames
  let N := Fintype.card (T × (Fin q → Deck k))
  let L := N*(3*Fintype.card (T ⊕ (Fin q × Slots (width k)))+2) + Fintype.card I*(2*N+1)
  refine ⟨1+q*D+L,e,?_⟩
  intro l h table
  obtain ⟨low,hl,hel⟩ := hD l k h
  let read (i : Fin q) (j : Slots (width l)) : T ⊕ (Fin q × Slots (width l)) := .inr (i,j)
  let factors (i : Fin q) := low.subst (Frame.initial (read i))
  obtain ⟨all,ha,hea⟩ := Crossing.exists_parallelFrames (out := fun _ : Fin q => Slots (width k)) factors
  let joint := Crossing.parallelFrame (Frame.initial Sum.inl)
    (all.select fun z : Fin q × Slots (width k) => ⟨z.1,z.2⟩)
  have hj : joint.size ≤ 1+q*D*(l+1)^e := by
    have hb : all.size ≤ 1+q*low.size := by
      simpa [factors] using ha
    simp only [joint, Crossing.parallelFrame_size, Frame.initial_size, zero_add, Frame.select_size]
    exact hb.trans (Nat.add_le_add_left (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left q hl) _)
  have hjEval (t : T) (x : Fin q → Deck l) :
      joint.eval (metadataInput l t x) = metadataInput k t (fun i => deckReduction h (x i)) := by
    funext j
    cases j with
    | inl s => simp [joint,metadataInput]
    | inr z =>
      have hr : (Frame.initial (read z.1)).eval (metadataInput l t x) = deckWires l (x z.1) :=
        funext fun i => by simp [read,metadataInput]
      simp only [joint, Crossing.parallelFrame_eval_inr, Frame.select_eval, hea, factors,
        Frame.subst_eval, hr, hel]
      rfl
  let key (p : T × (Fin q → Deck k)) := metadataInput k p.1 p.2
  obtain ⟨pick,hp,hep⟩ := lookupFrame key (metadataInput_injective q k) (fun p => table p.1 p.2)
  refine ⟨pick.subst joint, ?_, ?_⟩
  · change pick.size ≤ L at hp
    rw [Frame.subst_size]
    have hz : 1 ≤ (l+1)^e := Nat.one_le_pow _ _ (by omega)
    apply (Nat.add_le_add hj hp).trans
    have hL := Nat.mul_le_mul_left L hz
    simp only [Nat.mul_one] at hL
    nlinarith only [hz,hL]
  · intro t x
    funext i
    rw [Frame.subst_eval,hjEval]
    exact congrFun (hep (t,fun j => deckReduction h (x j))) i

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
