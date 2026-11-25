import OAI.Computability.BorderVNP.CoverDeckDigitFrames
import OAI.Computability.BorderVNP.CoverDeckDigitCost

/-! # A near-linear circuit for the complete deck refinement

Starting from the unique level-one residue, successive digit circuits refine
the chosen product address. Each layer retains direct references to the two
original count arrays. The final address agrees with the deterministic
minimum-score choice and its squared-deviation increment meets the uniform
deck average.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open VPVNP.VerifierNetwork (Frame)

/-- Center the prior histogram by its fixed mean and read the candidate
histogram from its second, uncentered bank. -/
def centeredPrior {B : Type*} {q l w : ℕ} (z : CountBits B q l w → Bool) (base : B → ℚ)
    (b : B) (g : Fin q → Deck l) : ℚ := (physicalCount z false b g : ℚ) - base b

/-- The raw candidate bin counts as exact rationals. -/
def candidateCounts {B : Type*} {q l w : ℕ} (z : CountBits B q l w → Bool)
    (b : B) (g : Fin q → Deck l) : ℚ := physicalCount z true b g

/-- All the refinement steps share a single physical input. The chosen output
is exactly the canonical first-minimizing translation of the full tower. -/
theorem refinement_frames (B : Type) [Fintype B] (q : ℕ) :
    ∃ D p : ℕ, ∀ k w : ℕ,
      ∃ f : Frame (CountBits B q (1+k) w) (Fin (keyWidth q (1+k))),
      f.size ≤ Fintype.card (Fin q → Deck (1+k))*D*(1+k+w+1)^p ∧
      ∀ (z : CountBits B q (1+k) w → Bool) (base mean : B → ℚ),
        (∀ s b, (∑ g, physicalCount z s b g) < 2^w) →
        ∃ v, refineDigits q 1 (1+k) (centeredPrior z base) (candidateCounts z) mean 1 k le_rfl =
          some v ∧ f.eval z = keyWord q (1+k) v := by
  obtain ⟨U,t,C,e,hdigit⟩ := digit_frames
  obtain ⟨D,p,hcost⟩ := digitCost_uniform B q U t C e
  refine ⟨D+keyWidth q 1,p+1,?_⟩
  intro k w
  let l := 1+k
  let V := Fintype.card (Fin q → Deck l)
  let S := l+w+1
  let stepCost := V*D*S^p
  have build (j : ℕ) (hj : 1+j ≤ l) :
      ∃ f : Frame (CountBits B q l w) (Fin (keyWidth q (1+j))),
      f.size ≤ keyWidth q 1+j*stepCost ∧
      ∀ (z : CountBits B q l w → Bool) (base mean : B → ℚ),
        (∀ s b, (∑ g, physicalCount z s b g) < 2^w) →
        ∃ v, refineDigits q 1 l (centeredPrior z base) (candidateCounts z) mean 1 j hj = some v ∧
          f.eval z = keyWord q (1+j) v := by
    induction j with
    | zero =>
      let src := Frame.initial (Empty.elim : Empty → CountBits B q l w)
      let literal (b : Fin (keyWidth q 1)) :
          BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr Empty :=
        .const (keyWord q 1 1 b)
      refine ⟨src.step literal, ?_, ?_⟩
      · simpa [src] using Frame.step_size_le src literal 1 (fun _ => le_rfl)
      · intro z base mean _
        exact ⟨1,rfl,funext fun b => (Frame.step_eval src literal z b).trans rfl⟩
    | succ j ih =>
      obtain ⟨prev,hp,he⟩ := ih (by omega)
      obtain ⟨next,hn,he'⟩ := hdigit B q (1+j) l w hj
      refine ⟨next.subst prev.withInput, ?_, ?_⟩
      · have hnext : next.size ≤ stepCost := hn.trans (hcost l w (1+j) (by omega) hj)
        simpa only [Frame.subst_size,Frame.withInput_size,Nat.succ_mul,Nat.add_assoc] using
          Nat.add_le_add hp hnext
      · intro z base mean fits
        obtain ⟨u,hu,hu'⟩ := he z base mean fits
        obtain ⟨v,hv,hv'⟩ := he' z u base mean fits
        have hread : prev.withInput.eval z = Sum.elim z (keyWord q (1+j) u) := by
          funext i
          cases i <;> simp [hu']
        refine ⟨v, ?_, ?_⟩
        · rw [refineDigits,hu,Option.bind_some]
          exact hv
        · funext b
          rw [Frame.subst_eval,hread]
          exact congrFun hv' b
  obtain ⟨f,hf,he⟩ := build k le_rfl
  refine ⟨f, ?_, he⟩
  have hV : 1 ≤ V := Fintype.card_pos
  have hS : 1 ≤ S := Nat.succ_pos _
  have hk : k ≤ S := by dsimp [S,l]; omega
  have hroot : keyWidth q 1 ≤ V*(keyWidth q 1)*S^(p+1) :=
    (Nat.le_mul_of_pos_left _ hV).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hS))
  calc
    f.size ≤ keyWidth q 1 + k*stepCost := hf
    _ ≤ V*(keyWidth q 1)*S^(p+1) + S*stepCost :=
      Nat.add_le_add hroot (Nat.mul_le_mul_right stepCost hk)
    _ = V*(D+keyWidth q 1)*S^(p+1) := by dsimp only [stepCost]; rw [pow_succ]; ring

/-- A circuit whose size is linear in the volume up to a polynomial in depth
and word length outputs a translation meeting the unconditional squared-
deviation bound for the actual input counts, including arbitrary rational
centering constants. -/
theorem translationChoice_frames (B : Type) [Fintype B] (q : ℕ) :
    ∃ D p : ℕ, ∀ (l w : ℕ), 1 ≤ l →
      ∃ f : Frame (CountBits B q l w) (Fin (keyWidth q l)),
      f.size ≤ Fintype.card (Fin q → Deck l)*D*(l+w+1)^p ∧
      ∀ (z : CountBits B q l w → Bool) (base mean : B → ℚ),
        (∀ s b, (∑ g, physicalCount z s b g) < 2^w) →
        ∃ v : Fin q → Deck l, f.eval z = keyWord q l v ∧
          CoverDeck.increment (centeredPrior z base) (candidateCounts z) mean v ≤
            (∑ h, CoverDeck.increment (centeredPrior z base) (candidateCounts z) mean h) /
              Fintype.card (Fin q → Deck l) := by
  obtain ⟨D,p,make⟩ := refinement_frames B q
  refine ⟨D,p,?_⟩
  intro l w hl
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hl
  obtain ⟨f,hs,he⟩ := make k w
  refine ⟨f,hs,?_⟩
  intro z base mean fits
  obtain ⟨v,hv,hev⟩ := he z base mean fits
  obtain ⟨u,hu,havg⟩ := refineDigits_uniform q k (centeredPrior z base) (candidateCounts z) mean
  rw [hv,Option.some.injEq] at hu
  exact ⟨v,hev,hu.symm ▸ havg⟩

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
