import OAI.Combinatorics.Sunflower.Basic
import OAI.Combinatorics.Sunflower.ColorCount
import OAI.Combinatorics.Sunflower.Rounding
import Mathlib.Data.Finset.Lattice.Union

/-! # Transferring word bounds to uniform set families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- Ordering each rainbow member by color gives a word. A finite alphabet suffices
even when the ground type is infinite. -/
private theorem rainbow_encoding {α : Type*} [DecidableEq α] {k : ℕ}
    (G : Finset (Finset α)) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x)) :
    ∃ (n : ℕ) (encode : G → Fin k → Fin n) (decode : Fin n → α),
      Function.Injective decode ∧
      ∀ (A : G) (x : α), x ∈ (A : Finset α) ↔ decode (encode A (c x)) = x := by
  classical
  let U := G.biUnion id
  let e (A : G) : (A : Finset α) ≃ Fin k := Equiv.ofBijective _ (hc A A.property)
  let point (A : G) (j : Fin k) : U :=
    ⟨(e A).symm j, Finset.mem_biUnion.mpr ⟨A, A.property, ((e A).symm j).property⟩⟩
  let encode (A : G) (j : Fin k) := U.equivFin (point A j)
  let decode (u : Fin U.card) : α := U.equivFin.symm u
  have hdecode (A : G) (j : Fin k) :
      decode (encode A j) = ((e A).symm j).val := by
    simp [decode, encode, point]
  refine ⟨U.card, encode, decode, Subtype.val_injective.comp U.equivFin.symm.injective, ?_⟩
  intro A x
  rw [hdecode]
  constructor
  · intro hx
    have he : (e A) ⟨x, hx⟩ = c x := rfl
    rw [← he, Equiv.symm_apply_apply]
  · intro hx
    exact hx ▸ ((e A).symm (c x)).property

/-- A rainbow subfamily of a sunflower-free family embeds as an equally large
sunflower-free family of words over one finite alphabet. -/
theorem exists_word_family_of_rainbow {α : Type*} [DecidableEq α] {k r : ℕ}
    {G F : Finset (Finset α)} (hGF : G ⊆ F) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x))
    (hfree : ¬ HasSunflower r F) :
    ∃ (n : ℕ) (W : Finset (Fin k → Fin n)), W.card = G.card ∧ WordFree r W := by
  classical
  obtain ⟨n, encode, decode, hd, hmem⟩ := rainbow_encoding G c hc
  have hinj : Function.Injective encode := by
    intro A B hab
    apply Subtype.ext
    ext x
    rw [hmem, hmem, hab]
  let W := Finset.univ.image encode
  refine ⟨n, W, ?_, ?_⟩
  · simp [W, Finset.card_image_of_injective _ hinj]
  intro w hw hadm
  by_contra hnc
  have hwi := hadm.injective_of_not_isConstant hnc
  have hlift (i : Fin r) : ∃ A : G, encode A = w i := by
    obtain ⟨A, _, ha⟩ := Finset.mem_image.mp (hw i)
    exact ⟨A, ha⟩
  choose A hA using hlift
  have hAinj : Function.Injective (fun i => (A i : Finset α)) := by
    intro i j hij
    apply hwi
    rw [← hA i, ← hA j, Subtype.ext hij]
  have hAmem (i : Fin r) (x : α) :
      x ∈ (A i : Finset α) ↔ decode (w i (c x)) = x := by rw [← hA, hmem]
  let K := (G.biUnion id).filter fun x => ∀ i, x ∈ (A i : Finset α)
  apply hfree
  apply hasSunflower_of_indexed (K := K) (fun i => hGF (A i).property) hAinj
  intro i j hij
  ext x
  constructor
  · intro hx
    obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨A i, (A i).property, hi⟩, ?_⟩
    have heq : w i (c x) = w j (c x) :=
      hd (((hAmem i x).mp hi).trans ((hAmem j x).mp hj).symm)
    rcases hadm (c x) with hall | hdistinct
    · intro t
      exact (hAmem t x).mpr ((congrArg decode (hall t i)).trans ((hAmem i x).mp hi))
    · exact (hij (hdistinct heq)).elim
  · intro hx
    have hAll := (Finset.mem_filter.mp hx).2
    exact Finset.mem_inter.mpr ⟨hAll i, hAll j⟩

universe u

/-- A uniform fixed base for finite word alphabets gives a uniform fixed base for
set families on every ground type in a specified universe. -/
theorem fixedBase_of_wordBound {r D : ℕ}
    (hWord : ∀ (k n : ℕ) (W : Finset (Fin k → Fin n)), WordFree r W → W.card ≤ D ^ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (k : ℕ) (α : Type u) [DecidableEq α] (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card → HasSunflower r F := by
  refine ⟨3 * max 1 D, by omega, ?_⟩
  intro k α _ F hF hlarge
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero] at hlarge
    exact (hlarge.not_ge (zero_uniform_card_le_one hF)).elim
  obtain ⟨c, G, hGF, hc, hcount⟩ := exists_rainbow_subfamily (Nat.pos_of_ne_zero hk) F hF
  by_contra hfree
  obtain ⟨n, W, hcard, hW⟩ := exists_word_family_of_rainbow hGF c hc hfree
  have hG : G.card ≤ (max 1 D) ^ k :=
    hcard ▸ (hWord k n W hW).trans (Nat.pow_le_pow_left (le_max_right 1 D) _)
  apply hlarge.not_ge
  apply Nat.le_of_mul_le_mul_right (c := k.factorial) _ (Nat.factorial_pos _)
  calc
    F.card * k.factorial ≤ G.card * k ^ k := hcount
    _ ≤ (max 1 D) ^ k * (3 ^ k * k.factorial) :=
      Nat.mul_le_mul hG (pow_self_le_three_pow_mul_factorial k)
    _ = (3 * max 1 D) ^ k * k.factorial := by rw [mul_pow]; ac_rfl

end Sunflower
end Combinatorics
end OAI
