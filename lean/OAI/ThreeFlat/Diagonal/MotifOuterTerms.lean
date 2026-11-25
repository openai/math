import OAI.Computability.VPVNP.MotifSelector
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Communicating the selector sequence on the surviving supply graph

Terms are indexed by a small outer payload profile. In each term, every
supply edge carries a uniform selector code. An incidence check and one
local decoding check at each party enforce a single valid sequence whose
totals equal that profile. Each accepted sequence contributes once.
-/

namespace ThreeFlat.Diagonal.MotifOuterTerms

open Computability.VPVNP.MotifSelector
open scoped Classical

variable {J E Code Q V F : Type*} [CommSemiring F] [Fintype J] [Nonempty J]
  [Fintype E] [Fintype Code] [Fintype Q] [Fintype V] [DecidableEq V]

/-- Local decoding of a selector with the prescribed aggregate profile.
Invalid encodings and words having a different profile both give zero. -/
noncomputable def decodeLocal (profile : Q → V) (encode : Q ↪ Code) (v : V)
    (entry : J → {s // profile s = v} → F) (j : J) (c : Code) : F := by
  classical
  exact if h : ∃ q : {s // profile s = v}, encode q = c then entry j h.choose else 0

omit [Fintype J] [Nonempty J] [Fintype Code] [Fintype V] in
private theorem decode_valid (profile : Q → V) (encode : Q ↪ Code) (v : V)
    (entry : J → {s // profile s = v} → F) (j : J) (q : {s // profile s = v}) :
    decodeLocal profile encode v entry j (encode q) = entry j q := by
  classical
  let h : ∃ y : {s // profile s = v}, encode y = encode q := ⟨q, rfl⟩
  unfold decodeLocal
  rw [dite_eq_left h]
  exact congrArg _ (Subtype.ext (encode.injective h.choose_spec))

omit [Fintype V] in
/-- All independently carried edge codes of a given outer term reduce to
the sum over its valid full selector sequences. The local `entry` may also
read any fixed incident payload bits. -/
theorem codes_for_profile (G : Supply J E) (profile : Q → V) (encode : Q ↪ Code)
    (v : V) (entry : J → {s // profile s = v} → F) :
    (∑ c : E → Code, ∏ j, if Agrees G c j then decodeLocal profile encode v entry j (c (G.anchor j)) else 0) =
      ∑ q : {s // profile s = v}, ∏ j, entry j q := by
  classical
  rw [sum_local_checks G]
  let f := fun q : {s // profile s = v} => encode q
  have hf : Function.Injective f := encode.injective.comp Subtype.val_injective
  let s := Finset.univ.image f
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun c _ hc => ?_)]
  · rw [Finset.sum_image (fun _ _ _ _ he => hf he)]
    simp only [f, decode_valid]
  · have h : ¬ ∃ q : {s // profile s = v}, encode q = c := by
      simpa [s, f] using hc
    simp [decodeLocal, h]

/-- Summing the outer profile and its payload assignment recovers the
independent choices of all base tiles, exactly once per sequence. -/
theorem sum_outer_profiles (G : Supply J E) (profile : Q → V) (encode : Q ↪ Code)
    (Payload : V → Type*) [∀ v, Fintype (Payload v)]
    (entry : ∀ v, Payload v → J → {s // profile s = v} → F) :
    (∑ v, ∑ z : Payload v, ∑ c : E → Code, ∏ j,
      if Agrees G c j then decodeLocal profile encode v (entry v z) j (c (G.anchor j)) else 0) =
      ∑ q, ∑ z : Payload (profile q), ∏ j, entry (profile q) z j ⟨q,rfl⟩ := by
  classical
  simp_rw [codes_for_profile G profile encode]
  rw [← Fintype.sum_fiberwise profile (fun q => ∑ z : Payload (profile q), ∏ j,
    entry (profile q) z j ⟨q,rfl⟩)]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  rintro ⟨q,rfl⟩ _
  rfl

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
