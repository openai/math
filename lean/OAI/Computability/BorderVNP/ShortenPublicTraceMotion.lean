import OAI.Computability.BorderVNP.CoverDeckInverseFrame
import OAI.Computability.BorderVNP.CoverDeckPackSequence
import OAI.Computability.BorderVNP.ShortenPublicPreBatchSample

/-!
# Recovering the shared forward motions from the concentration circuit

Each score trace reports one candidate and its pullback tile. The physical
site and histogram stages share the same inverse, computed once per pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Cover Cover.Frame Cover.AddressCircuit Epoch PublicSegments Hecke PreparedBins
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

/-- Compile the forward translation bank for all packs, using exactly the
one-hot motion and pullback key emitted by the concentration trace. -/
theorem traceMotion_frames :
    ∃ C e : ℕ, ∀ {D q : ℕ} (enum : Fin q ≃ Cube D) (B : Type) [Fintype B]
      (l m w copies : ℕ),
      ∃ f : Frame (PackTracePins B q l m w copies) (Motion (Fin m) q l copies),
        f.size ≤ 1+copies*(1+q*C*(l+1)^e) ∧
        ∀ (x : PackTracePins B q l m w copies → Bool) (pick : Fin copies → Fin m)
          (pull : Fin copies → Fin q → Deck l),
          (∀ i j, x (.inr (i,.inl j)) = true ↔ j = pick i) →
          (∀ i j, x (.inr (i,.inr j)) = keyWord q l (pull i) j) →
          f.eval x = motionWires enum pick (fun i => (pull i ∘ enum.symm)⁻¹) := by
  obtain ⟨C,e,make⟩ := inverseKey_frames
  refine ⟨C,e,?_⟩
  intro D q enum B inst l m w copies
  let Src := PackTracePins B q l m w copies
  obtain ⟨inv,hs,he⟩ := make q l
  let pins (i : Fin copies) : Frame Src (Fin (keyWidth q l)) :=
    Frame.initial (fun j => .inr (i,.inr j))
  let each (i : Fin copies) := inv.subst (pins i)
  obtain ⟨all,hall,out⟩ := Crossing.exists_parallelFrames
    (out := fun _ : Fin copies => ProductSlots q l) each
  let route : Motion (Fin m) q l copies → Src ⊕ (Σ _ : Fin copies, ProductSlots q l)
    | (i,.inl j) => .inl (.inr (i,.inl j))
    | (i,.inr j) => .inr ⟨i,j⟩
  refine ⟨all.withInput.select route,?_,?_⟩
  · have hsum : all.size ≤ 1+copies*inv.size := by simpa [each,pins] using hall
    exact hsum.trans (Nat.add_le_add_left (Nat.mul_le_mul_left copies hs) 1)
  · intro x pick pull flag key
    have hkey (i : Fin copies) : (pins i).eval x = keyWord q l (pull i) := by
      funext j; simpa only [pins,Frame.initial_eval] using key i j
    funext z
    rcases z with ⟨i,j|⟨c,j⟩⟩
    · simp only [Frame.select_eval,route,Frame.withInput_eval_inl,motionWires,Sum.elim_inl]
      exact Bool.eq_iff_iff.mpr ((flag i j).trans decide_eq_true_iff.symm)
    · simp only [Frame.select_eval,route,Frame.withInput_eval_inr,out,each,Frame.subst_eval,hkey,he,
        motionWires,Sum.elim_inr,productWires,Pi.inv_apply,Function.comp_apply,Equiv.symm_apply_apply]

set_option maxHeartbeats 900000 in
/-- The selector indices and forward translations obtained from a physical
concentration witness coincide with the candidate and shifts consumed by
the canonical site pattern. -/
theorem deckSample_motionWires {D q l l' n m copies : ℕ} (enum : Fin q ≃ Cube D)
    (index : Fin m ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)
    (level : l=l') (pick : Fin copies → Fin m) (pull : Fin copies → Fin q → Deck l) :
    let ω := fun i => deckSample enum index (pick i,pull i)
    motionWires enum (fun i => sampledChoice index (ω i))
      (fun i j => deckCast level ((ω i).2.2 j)) =
      motionWires enum pick (fun i j => deckCast level ((pull i ∘ enum.symm)⁻¹ j)) := by
  cases level
  dsimp only
  have h (i : Fin copies) : sampledChoice index (deckSample enum index (pick i,pull i)) = pick i :=
    index.symm_apply_apply (pick i)
  simp_rw [h]
  rfl

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
