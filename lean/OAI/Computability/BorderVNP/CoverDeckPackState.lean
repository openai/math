import OAI.Computability.BorderVNP.CoverDeckPackSelection
import OAI.Computability.BorderVNP.CoverDeckPackCost
import OAI.Computability.BorderVNP.CoverDeckShiftBank

/-!
# Updating both public banks after a deterministic pack motion

The finite candidate and its deck translation are chosen once. A sparse
batched read computes the translated counts and adds them to the prior
bank. The updated mean numerators use the same candidate distribution at
every level. Both banks can feed the following pack directly.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedDeckCandidate
open VPVNP.VerifierNetwork (Frame)

/-- Stored physical counts and mean numerators between successive packs. -/
abbrev PriorPins (B : Type*) (q l w : ℕ) := (B × (Fin q → Deck l) × Fin w) ⊕ (B × Fin w)

/-- The motion-selection ports and the newly accumulated physical counts. -/
abbrev BankStatePins (B : Type*) (q l m w : ℕ) :=
  SelectionPins B q l m w ⊕ (B × (Fin q → Deck l) × Fin w)

/-- Direct wire to the new state bank for the next pack. -/
def nextPriorPin {B : Type*} {q l m w : ℕ} : PriorPins B q l w → BankStatePins B q l m w :=
  Sum.elim Sum.inr (fun p => .inl (.inl (.inl (.inl (.inr p)))))

/-- The selected physical motion and its exact accumulated histogram. -/
structure BankState {B : Type*} [Fintype B] {q l m w : ℕ} (P : ℕ) (prob : Fin m → ℚ)
    (x : Input B (Fin q → Deck l) m w → Bool) (base : B → ℚ)
    (y : BankStatePins B q l m w → Bool) (j : Fin m) (h : Fin q → Deck l) : Prop where
  /-- All candidate flags, mean numerators, and the selected pullback address. -/
  selected : PackSelected P prob x base (y ∘ Sum.inl) j h
  /-- The histogram after physically moving rows by the inverse translation. -/
  accumulated : ∀ b g, ParseBatchSort.value (fun i => y (.inr (b,g,i))) =
    inputCounts x none b g + inputCounts x (some j) b (h*g)

/-- A sum of two output-linear gate bounds has the same single volume factor. -/
theorem addVolumeCost (v a b r s n : ℕ) (hn : 0 < n) :
    v*a*n^r + v*b*n^s ≤ v*(a+b)*n^(r+s) := by
  have hr := Nat.pow_le_pow_right hn (Nat.le_add_right r s)
  have hs := Nat.pow_le_pow_right hn (Nat.le_add_left s r)
  exact (Nat.add_le_add (Nat.mul_le_mul_left (v*a) hr) (Nat.mul_le_mul_left (v*b) hs)).trans_eq (by ring)

private theorem sum_fits {B : Type*} {q l m w P K A : ℕ}
    {x : Input B (Fin q → Deck l) m w → Bool} {base : B → ℚ} (hP : 0 < P)
    (hx : PackInputFits q l m w P K A x base) : K+K < 2^w := by
  let n := Fintype.card (Fin q → Deck l)
  let D := P*n
  let L := A+P*(n*K)
  have hn : 1 ≤ n := Fintype.card_pos
  have hmass : K ≤ L := calc
    K = 1*K := (one_mul K).symm
    _ ≤ n*K := Nat.mul_le_mul_right K hn
    _ = 1*(n*K) := (one_mul _).symm
    _ ≤ P*(n*K) := Nat.mul_le_mul_right _ hP
    _ ≤ L := Nat.le_add_left _ _
  have hbig : K+L+3*D*n^2*K^2+2*n^2*L*K < 2^choiceBits n D K L := Nat.lt_log2_self
  exact (lt_of_le_of_lt (by omega : K+K ≤ K+L+3*D*n^2*K^2+2*n^2*L*K) hbig).trans_le
    (Nat.pow_le_pow_right (by decide) hx.width)

/-- Complete physical bank update after selection, with one full-cover
volume factor in its gate count. The probability denominator is independent
of the depth and count width. -/
theorem bankState_frames (B : Type) [Fintype B] (q m : ℕ) (prob : Fin m → ℚ)
    (hn : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1) :
    ∃ P D p : ℕ, 0 < P ∧ ∀ l w : ℕ, 1 ≤ l → P < 2^w →
      ∃ f : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w),
        f.size ≤ Fintype.card (Fin q → Deck l)*D*(l+w+1)^p ∧
        ∀ x base K A, PackInputFits q l m w P K A x base →
          ∃ j h, BankState P prob x base (f.eval x) j h := by
  obtain ⟨P,U,t,C,e,M,z,D₁,p₁,hP,makeSelect⟩ := packSelection_frames B q m prob hn hsum
  obtain ⟨D₂,p₂,compact⟩ := packCost_uniform B q m U t C e M z
  obtain ⟨D₃,p₃,makeUpdate⟩ := shiftBank_frames B q
  refine ⟨P,D₂+D₁+D₃,p₂+p₁+p₃,hP,?_⟩
  intro l w hl hw
  let v := Fintype.card (Fin q → Deck l)
  let n := l+w+1
  have hn' : 0 < n := by dsimp [n]; omega
  obtain ⟨sel,hs,hsel⟩ := makeSelect l w hl hw
  obtain ⟨upd,hu,hupd⟩ := makeUpdate l w
  let get : Frame (SelectionPins B q l m w) (CountBits B q l w ⊕ Fin (keyWidth q l)) :=
    Frame.initial (Sum.elim (fun a => .inl (.inr a)) Sum.inr)
  let f := (upd.subst get).withInput.subst sel
  refine ⟨f,?_,?_⟩
  · have h₁ := hs.trans ((Nat.add_le_add_right (compact l w) _).trans (addVolumeCost v D₂ D₁ p₂ p₁ n hn'))
    simpa [f,get,v,n] using (Nat.add_le_add h₁ hu).trans (addVolumeCost v (D₂+D₁) D₃ (p₂+p₁) p₃ n hn')
  · intro x base K A hx
    obtain ⟨j,h,chosen⟩ := hsel x base K A hx
    have first : f.eval x ∘ Sum.inl = sel.eval x := by funext a; simp [f]
    have raw : get.eval (sel.eval x) = Sum.elim (bankWord x j) (keyWord q l h) := by
      funext a
      cases a <;> simp [get,chosen.banks,chosen.key]
    refine ⟨j,h,⟨first.symm ▸ chosen,?_⟩⟩
    intro b g
    have row : (fun i => f.eval x (.inr (b,g,i))) =
        fun i => upd.eval (Sum.elim (bankWord x j) (keyWord q l h)) (b,g,i) := by
      funext i; simp [f,raw]
    rw [row,hupd]
    have cap := (Nat.add_le_add (hx.counts none b g) (hx.counts (some j) b (h*g))).trans_lt (sum_fits hP hx)
    exact Nat.mod_eq_of_lt cap

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
