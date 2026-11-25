import OAI.Computability.BorderVNP.CoverDescriptorPlacementFrame
import OAI.Computability.BorderVNP.CoverProductMetadataFrame

/-! # Exact tile and relative metadata of a moved pack row

The circuit reads a relative catalog index, a tuple of shared posttranslations
and a deep tile address. It emits both the moved tile and all finite metadata
bits in one shared frame. Instantiating the finite tables by geometric carries
and relative-frame predicates computes the actual results on representatives,
including tie-resolved tile boundaries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)

/-- Input wires of a single typed pack row, with its common deck translation. -/
def rowInput {T : Type*} [DecidableEq T] {q l z : ℕ} (t : T)
    (shift : Fin q → Deck l) (x : Fin q → Deck z) : T ⊕ (ProductSlots q l ⊕ ProductSlots q z) → Bool :=
  Sum.elim (fun u => decide (u=t)) (Sum.elim (productWires l shift) (productWires z x))

/-- One polynomial bound covers all finite displacement and metadata tables.
The output is the moved tile together with every low-residue metadata bit. -/
theorem packRow_frames {T I : Type*} [Fintype T] [DecidableEq T] [Fintype I] {q a : ℕ}
    {g : Fin q → Cover.Frame.SL} (hg : ∀ i, Cover.Frame.Clears (g i) a) :
    ∃ C e : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (perm : Equiv.Perm (Fin q))
      (offset : T → Fin q → Deck (1+2*a) → Deck (d+2*a))
      (table : T → (Fin q → Deck (1+2*a)) → I → Bool),
      ∃ f : Frame (T ⊕ (ProductSlots q (d+2*a) ⊕ ProductSlots q (d+2*a+2*a)))
        (ProductSlots q (d+2*a) ⊕ I), f.size ≤ C*(d+1)^e ∧ ∀ t shift x,
      f.eval (rowInput t shift x) =
        Sum.elim (productWires _ (translatedProductPlacement hg hd perm (offset t) shift x))
          (table t (fun i => deckReduction (show 1+2*a ≤ d+2*a+2*a by omega) (x i))) := by
  obtain ⟨P,p,hP⟩ := descriptorPlacement_frames (T := T) hg
  obtain ⟨M,m,hM⟩ := productMetadataFrames (T := T) (I := I) q (1+2*a)
  let zt : TimeBound := TimeBound.variable + .const (2*a+2*a)
  let cost : TimeBound := .const P * TimeBound.variable^p + .const M * zt^m
  obtain ⟨C,e,_,_,hc⟩ := cost.growth
  refine ⟨C,e,?_⟩
  intro d hd perm offset table
  let z := d+2*a+2*a
  have hk : 1+2*a ≤ z := by dsimp [z]; omega
  obtain ⟨place,hp,hep⟩ := hP d hd perm offset
  obtain ⟨lookup,hm,hem⟩ := hM z hk table
  let pick (i : T ⊕ ProductSlots q z) : T ⊕ (ProductSlots q (d+2*a) ⊕ ProductSlots q z) :=
    i.elim Sum.inl (Sum.inr ∘ Sum.inr)
  let get := Frame.initial pick
  refine ⟨Crossing.parallelFrame place (lookup.subst get), ?_, ?_⟩
  · have hz : zt.eval (d+1) = z+1 := by simp [zt,z]; omega
    have h := hc (d+1) (by omega)
    simp only [cost,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,
      TimeBound.eval_variable,TimeBound.eval_const,hz] at h
    simpa only [Crossing.parallelFrame_size,Frame.subst_size,get,Frame.initial_size,zero_add] using
      (Nat.add_le_add hp hm).trans h
  · intro t shift x
    have hget : get.eval (rowInput t shift x) = metadataInput z t x := by
      funext i
      cases i <;> simp [get,pick,rowInput,metadataInput,productWires]
    funext i
    cases i with
    | inl i => exact (Crossing.parallelFrame_eval_inl ..).trans (congrFun (hep t shift x) i)
    | inr i =>
      rw [Crossing.parallelFrame_eval_inr,Frame.subst_eval,hget,hem]
      rfl

set_option maxHeartbeats 1200000 in
/-- The complete per-row geometric computation. The relative type supplies
the frame in each source factor, and any finite classification of the moved
relative frames (for example the segment or bin) is emitted alongside the
true translated tile. The polynomial bound is uniform in all these tables. -/
theorem geometricPackRow_frames {T I : Type*} [Fintype T] [DecidableEq T] [Fintype I] {q a : ℕ}
    {g : Fin q → Cover.Frame.SL} (hg : ∀ i, Cover.Frame.Clears (g i) a) :
    ∃ C e : ℕ, ∀ (d : ℕ) (_ : 1 ≤ d) (perm : Equiv.Perm (Fin q))
      (relative : T → Fin q → Cover.Frame.SL) (classify : T → (Fin q → Cover.Frame.SL) → I → Bool),
      ∃ f : Frame (T ⊕ (ProductSlots q (d+2*a) ⊕ ProductSlots q (d+2*a+2*a)))
        (ProductSlots q (d+2*a) ⊕ I), f.size ≤ C*(d+1)^e ∧ ∀ t (shift x : Fin q → gamma 1),
        let moved (i : Fin q) := gammaSL 1 (shift i) *
          (g i * (gammaSL 1 (x (perm i)) * relative t (perm i)))
        f.eval (rowInput t (fun i => (shift i : Deck (d+2*a))) (fun i => (x i : Deck (d+2*a+2*a)))) =
          Sum.elim (productWires _ fun i => (Cover.Frame.frameCarry (moved i) : Deck (d+2*a)))
            (classify t fun i => Cover.Frame.relativeFrame (moved i)) := by
  obtain ⟨C,e,hr⟩ := packRow_frames (T := T) (I := I) hg
  refine ⟨C,e,?_⟩
  intro d hd perm relative classify
  let offset (t : T) (i : Fin q) (low : Deck (1+2*a)) : Deck (d+2*a) :=
    (Cover.Frame.frameCarry (Cover.Frame.movedLowFrame (g i) low (relative t (perm i))) : Deck (d+2*a))
  let table (t : T) (low : Fin q → Deck (1+2*a)) := classify t (fun i =>
    Cover.Frame.relativeFrame (Cover.Frame.movedLowFrame (g i) (low (perm i)) (relative t (perm i))))
  obtain ⟨f,hs,he⟩ := hr d hd perm offset table
  refine ⟨f,hs,?_⟩
  intro t shift x
  dsimp only
  rw [he,translatedProductPlacement_geometric hg hd perm (relative t) shift x]
  congr 1
  apply congrArg (classify t)
  funext i
  rw [Cover.Frame.relativeFrame_translate,Cover.Frame.moved_relative_eq (hg i)]
  rfl

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
