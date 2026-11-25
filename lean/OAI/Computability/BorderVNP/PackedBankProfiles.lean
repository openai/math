import OAI.Computability.BorderVNP.PackedProfileCounts
import OAI.Computability.BorderVNP.ShortenAddressReplacement

/-! # Executing public profile choices at all seeds

An accepted fixed-width tuple indexes one and only one term of the physical tensor sum.
Conversely every term has one such tuple, also at a seed with no matched blocks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCircuit

open ParseBatchSort VPVNP.VerifierNetwork Shortening

variable {D m : ℕ} {K : Type*} [Field K] (e : Crossing.PaidIdentity K D m) {A : Type}

/-- Publicly guessed histogram bits, with one fixed-width word per term per seed. -/
abbrev HistogramBits (w : ℕ) := A → Fin e.count → Fin w → Bool

/-- Exactly the public bits accepted by the profile count check at every seed. -/
def Accepted (j : A → ℕ) {w : ℕ} (bits : HistogramBits e (A := A) w) : Prop :=
  ∀ a, (fun t => value (bits a t)) ∈ Crossing.Profile.profiles e.count (j a)

/-- With enough bits for the matched size, accepted transcripts are in bijection with
the actual term indices of the simultaneous profile tensor identity. -/
noncomputable def branches {w : ℕ} (j : A → ℕ) (room : ∀ a, j a < 2^w) :
    {bits : HistogramBits e w // Accepted e j bits} ≃ ProfileCounts e j where
  toFun x a := ⟨fun t => value (x.val a t),x.property a⟩
  invFun q := by
    have h (a : A) (t : Fin e.count) : (q a).val t < 2^w :=
      (Finset.single_le_sum (fun i _ => Nat.zero_le ((q a).val i)) (Finset.mem_univ t)).trans_lt
        ((profileCounts_total e j q a).trans_lt (room a))
    let b (a : A) (t : Fin e.count) := (ParseBatchCounts.numberWords w).symm ⟨(q a).val t,h a t⟩
    refine ⟨b, fun a => ?_⟩
    have hb : (fun t => value (b a t)) = (q a).val := funext fun _ => ParseBatchCounts.value_encode _
    rw [hb]
    exact (q a).property
  left_inv x := by
    apply Subtype.ext
    funext a t
    apply value_injective w
    exact ParseBatchCounts.value_encode _
  right_inv q := by
    funext a
    apply Subtype.ext
    funext t
    exact ParseBatchCounts.value_encode _

/-- The physical branch indexed by accepted words has exactly those count values. -/
theorem branches_count {w : ℕ} (j : A → ℕ) (room : ∀ a, j a < 2^w)
    (b : {bits : HistogramBits e w // Accepted e j bits}) (a : A) (t : Fin e.count) :
    (((branches e j room) b a).val t) = value (b.val a t) := rfl

/-- Number of gates sufficient for one count checker, including its carry bits. -/
def guardBudget (terms w : ℕ) : ℕ :=
  let W := w + Nat.clog 2 (terms+1)
  (terms+1)*W + (2*terms+1)*(100*(W+1)^2) + (30*W+3)

/-- The actual Boolean check returns one validity bit per seed. A source frame can
supply the matched sizes from the sorting/pool pass and the guessed count words jointly.
Every bit setting, including a malformed word tuple, has the displayed acceptance semantics. -/
theorem exists_checks [Fintype A] {σ : Type*} [Fintype σ] (w : ℕ)
    (source : Frame σ (A × Option (Fin e.count) × Fin w)) :
    ∃ f : Frame σ A, f.size ≤ source.size + 1 + Fintype.card A * guardBudget e.count w ∧
      ∀ x, (∀ a, f.eval x a = true) ↔ Accepted e
        (fun a => value (fun j => source.eval x (a,none,j)))
        (fun a t j => source.eval x (a,some t,j)) := by
  classical
  obtain ⟨g,hg,hvalue⟩ := exists_profileGuard e.count w
  let one (a : A) := g.subst (Frame.initial (fun i : Option (Fin e.count) × Fin w => (a,i)))
  obtain ⟨joint,hs,he⟩ := Crossing.exists_parallelFrames one
  let pick (a : A) : Σ _ : A, Unit := ⟨a,()⟩
  refine ⟨(joint.select pick).subst source, ?_, fun x => ?_⟩
  · have hlocal (a : A) : (one a).size ≤ guardBudget e.count w := by simpa [one,guardBudget] using hg
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at hsum
    simp only [Frame.subst_size,Frame.select_size]
    exact (Nat.add_le_add_left (hs.trans (Nat.add_le_add_left hsum 1)) _).trans_eq (by omega)
  · apply forall_congr'
    intro a
    let z := fun i : Option (Fin e.count) × Fin w => source.eval x (a,i)
    have ha : ((joint.select pick).subst source).eval x a = g.eval z () := by
      simp [pick,he,one,z]
      congr 1
      funext i
      simp
    rw [ha]
    exact hvalue z

end Packing.BankCircuit

end BorderVNP
end Computability
end OAI
