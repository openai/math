import OAI.Computability.NearSquareRoot.KernelPassRectBudget
import OAI.Computability.NearSquareRoot.KernelPencilDyadicMix
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleSystem

/-! # Signed binary rectangle weights and the one-pencil call bound -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect.Binary
open OAI.LinearAlgebra.FiniteFourier Matrix Finset
open scoped CyclotomicCode BigOperators Classical

variable {L b A : ℕ} {W J : Type} [Fintype W] [Fintype J] [DecidableEq W]

abbrev Label (L b : ℕ) := BitLabel L b
abbrev Free (L b : ℕ) := FreeBitRectangle 2 L b
abbrev Paid (L b : ℕ) := ChargedRectangle L b (L / 2)
abbrev System (L b : ℕ) := PrimeRectangleSystem Dyadic 2 L b

noncomputable def system (L b : ℕ) : System L b :=
  (exists_primeRectangleSystem Dyadic 2 L b
    (isUnit_iff_exists_inv'.mpr ⟨Dyadic.ofIntWithPrec 1 1, by decide⟩)).some

noncomputable def freeSupport (S : System L b) (r : Free L b) : Support (Label L b) :=
  ⟨(bitSources r.val).toFinset, (bitTargets r.val).toFinset, PencilDyadicMix.encode (S.freeWeight r)⟩

noncomputable def chargedSupport (S : System L b) (r : Paid L b) : Support (Label L b) :=
  ⟨(chargedEndpoint r).toFinset, (chargedEndpoint r).toFinset, PencilDyadicMix.encode (S.chargedWeight r)⟩

theorem weight_identity (S : System L b) (w v : Label L b) :
    (∑ r, (freeSupport S r).coeff w v) + (∑ r, (chargedSupport S r).coeff w v) =
      if w = v then 1 else 0 := by
  classical
  have e := congrArg PencilDescent.toRatHom (S.identity v w)
  simp only [map_add, map_sum, apply_ite PencilDescent.toRatHom, map_zero, map_one] at e
  have hc (d : Dyadic) : PencilDescent.toRatHom d = d.toRat := rfl
  simp only [hc] at e
  rw [add_comm]
  by_cases hvw : v = w <;> simp only [hvw, eq_comm (a := w) (b := v), ite_true, ite_false] at e ⊢ <;>
  simpa only [freeSupport, chargedSupport, Support.coeff, PencilDyadicMix.value_encode,
    Set.mem_toFinset] using e

private theorem filter_card_le (E : BitRectangle L b → Set (Label L b)) (v : Label L b) :
    (univ.filter (fun r : Free L b => v ∈ E r.val)).card ≤
      Fintype.card {r : BitRectangle L b // v ∈ E r} := by
  rw [← Fintype.card_coe]
  apply Fintype.card_le_of_injective
    (fun r => (⟨r.val.val, (mem_filter.mp (show r.val ∈ univ.filter (fun u : Free L b => v ∈ E u.val) from r.property)).2⟩ : {r : BitRectangle L b // v ∈ E r}))
  intro r s he
  exact Subtype.ext (Subtype.ext (congrArg (fun t : {r : BitRectangle L b // v ∈ E r} => t.val) he))

theorem free_sources_le (S : System L b) (v : Label L b) :
    (univ.filter (fun r => v ∈ (freeSupport S r).sources)).card ≤ (1+b)^L := by
  simpa [freeSupport, card_bitSource_incidence] using filter_card_le bitSources v

theorem free_targets_le (S : System L b) (w : Label L b) :
    (univ.filter (fun r => w ∈ (freeSupport S r).destinations)).card ≤ (1+b)^L := by
  simpa [freeSupport, card_bitTarget_incidence] using filter_card_le bitTargets w

theorem card_label : Fintype.card (Label L b) = (2^b)^L := by
  simp [Label, BitLabel, BitLetter]

/-- A concrete stage bound from the binary weighted rectangles. The supplied
singleton plans implement the geometric endpoint maps. -/
theorem calls_binary_le (S : System L b)
    (Frees : Free L b → FreeData A (Label L b) J) (Charged : Paid L b → ChargedData A (Label L b) J)
    (hf : ∀ r, (Frees r).toSupport = freeSupport S r)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient)
    (hs : ∀ r v, v ∈ (Frees r).sources → ((Frees r).source v).calls ≤ 2*S.D)
    (ht : ∀ r w, w ∈ (Frees r).destinations → ((Frees r).target w).calls ≤ 2*S.D)
    (hc : ∀ r j, ((Charged r).common j).calls ≤ 2*S.D) :
    (pencil Frees Charged B₀ B).calls ≤
      2*S.D*Fintype.card W * (2*(2^b)^L*(1+b)^L + Fintype.card J * (2^L*(2^b)^(L/2))) := by
  simpa only [card_label] using calls_pencil_le Frees Charged B₀ B (2*S.D) _ _ hs ht hc
    (fun v => by simpa only [hf] using free_sources_le S v)
    (fun w => by simpa only [hf] using free_targets_le S w) (card_chargedRectangle_le L b (L/2))

end KernelPass.Rect.Binary

end NearSquareRoot
end Computability
end OAI
