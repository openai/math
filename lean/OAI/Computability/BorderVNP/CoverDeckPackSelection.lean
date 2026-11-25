import OAI.Computability.BorderVNP.CoverDeckPackBanks

/-! # One circuit selects the finite pack motion and its deck translation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedDeckCandidate
open VPVNP.VerifierNetwork (Frame)

/-- The selected motion, its two count banks, and the pullback tile address. -/
abbrev SelectionPins (B : Type*) (q l m w : ℕ) :=
  (ChoicePins B q l m w ⊕ CountBits B q l w) ⊕ Fin (keyWidth q l)

/-- Natural range and mean-bank invariants of the physical input at one pack. -/
structure PackInputFits {B : Type*} (q l m w P K A : ℕ)
    (x : Input B (Fin q → Deck l) m w → Bool) (base : B → ℚ) : Prop where
  /-- The previous accumulator is the cleared numerator of the previous means. -/
  mean : ∀ b, ((P * Fintype.card (Fin q → Deck l) : ℕ) : ℚ)*base b = meanNumerator x b
  /-- Bound on the stored previous numerator. -/
  old : ∀ b, meanNumerator x b ≤ A
  /-- Bounds on physical counts, including the prior bank. -/
  counts : ∀ s b g, inputCounts x s b g ≤ K
  /-- A common bit width for counts and all scalar charge comparisons. -/
  width : let n := Fintype.card (Fin q → Deck l)
    choiceBits n (P*n) K (A+P*(n*K)) ≤ w

/-- Uniform source mean at one tile, independent of the tile by deck averaging. -/
noncomputable def packMean {B : Type*} {q l m w : ℕ} (prob : Fin m → ℚ)
    (x : Input B (Fin q → Deck l) m w → Bool) (b : B) : ℚ :=
  PackedDeckMean.mean prob (fun c => inputCounts x (some c)) b 1

/-- Meaning of every output port, and the conditional-expectation guarantee
of the combined finite-motion and deck choice. -/
structure PackSelected {B : Type*} [Fintype B] {q l m w : ℕ} (P : ℕ) (prob : Fin m → ℚ)
    (x : Input B (Fin q → Deck l) m w → Bool) (base : B → ℚ)
    (y : SelectionPins B q l m w → Bool) (j : Fin m) (h : Fin q → Deck l) : Prop where
  /-- The first minimizing finite motion is the unique flagged ordinal. -/
  flags : ∀ i, y (.inl (.inl (.inr i))) = true ↔ i = j
  /-- Every unselected count bank remains available to subsequent geometric reads. -/
  original : ∀ p, y (.inl (.inl (.inl (.inl p)))) = x (.inl p)
  /-- Both banks of the selected comparison, in the order expected by deck arithmetic. -/
  banks : ∀ p, y (.inl (.inr p)) = bankWord x j p
  /-- The pullback translation for counts; the physical posttranslation is its inverse. -/
  key : ∀ b, y (.inr b) = keyWord q l h b
  /-- The new accumulated bin means, with the same fixed probability denominator. -/
  updated : ∀ b, ((P * Fintype.card (Fin q → Deck l) : ℕ) : ℚ) * (base b + packMean prob x b) =
    meanNumerator (fun a => y (.inl (.inl (.inl a)))) b
  /-- The actual full choice costs no more than the average over both random choices. -/
  increment_le : CoverDeck.increment (centeredPrior (bankWord x j) base)
    (candidateCounts (bankWord x j)) (packMean prob x) h ≤
    ∑ i, prob i * uniformScore (inputCounts x none) (inputCounts x (some i)) base (packMean prob x)

private theorem first_minimum {m : ℕ} (prob score : Fin m → ℚ) (hn : ∀ i, 0 ≤ prob i)
    (hs : ∑ i, prob i = 1) :
    ∃ j, (List.finRange m).argmin score = some j ∧ score j ≤ ∑ i, prob i * score i := by
  have hm : 0 < m := by
    by_contra! hz
    have he : m = 0 := by omega
    subst m
    simp at hs
  cases he : (List.finRange m).argmin score with
  | none =>
    have hlen := congrArg List.length (List.argmin_eq_none.mp he)
    simp at hlen
    omega
  | some j =>
    refine ⟨j,rfl,?_⟩
    calc
      score j = ∑ i, prob i * score j := by rw [← Finset.sum_mul,hs,one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (List.le_of_mem_argmin (List.mem_finRange i) he) (hn i)

/-- One shared circuit for the exact two-part choice. The finite probability
denominator is selected before the cover level. -/
theorem packSelection_frames (B : Type) [Fintype B] (q m : ℕ) (prob : Fin m → ℚ)
    (hn : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1) :
    ∃ P U t C e M z D p : ℕ, 0 < P ∧ ∀ (l w : ℕ), 1 ≤ l → P < 2^w →
      ∃ f : Frame (Input B (Fin q → Deck l) m w) (SelectionPins B q l m w),
        f.size ≤ PackedDeckMean.candidateCost B (Fin q → Deck l) m w U t C e M z +
          Fintype.card (CountBits B q l w)*(4*m+1) + Fintype.card (Fin q → Deck l)*D*(l+w+1)^p ∧
        ∀ x base K A, PackInputFits q l m w P K A x base →
          ∃ j h, PackSelected P prob x base (f.eval x) j h := by
  obtain ⟨U,t,C,e,M,z,hfinite⟩ := PackedDeckMean.weightedChoice_frames
  obtain ⟨P,hP,makeFinite⟩ := hfinite m prob hn hsum
  obtain ⟨D,p,makeDeck⟩ := translationChoice_frames B q
  refine ⟨P,U,t,C,e,M,z,D,p,hP,?_⟩
  intro l w hl hw
  obtain ⟨win,hsize,horig,hwin⟩ := makeFinite B (Fin q → Deck l) w hw
  obtain ⟨deck,hdeck,choose⟩ := makeDeck l w hl
  let staged := (packBanks B q l m w).withInput.subst win
  let next := (deck.subst (Frame.initial (Sum.inr : CountBits B q l w → ChoicePins B q l m w ⊕ _))).withInput
  let f := next.subst staged
  refine ⟨f,?_,?_⟩
  · simpa [f,next,staged] using Nat.add_le_add (Nat.add_le_add hsize (packBanks_size B q l m w)) hdeck
  · intro x base K A hx
    obtain ⟨hmean,hflag⟩ := hwin x base K A hx.mean hx.old hx.counts hx.width
    let score i := uniformScore (inputCounts x none) (inputCounts x (some i)) base (packMean prob x)
    obtain ⟨j,hj,havg⟩ := first_minimum prob score hn hsum
    have flags (i : Fin m) : win.eval x (.inr i) = true ↔ i=j := by
      rw [hflag]
      change (List.finRange m).argmin score = some i ↔ _
      rw [hj,Option.some.injEq]
      exact eq_comm
    have hb := packBanks_eval (win.eval x) x j (horig x) flags
    have hmid : staged.eval x = Sum.elim (win.eval x) (bankWord x j) := by
      funext a
      cases a <;> simp [staged,hb]
    let n := Fintype.card (Fin q → Deck l)
    let L := A+P*(n*K)
    have hL : L < 2^w := (fields_fit n (P*n) K L).2.trans_le (Nat.pow_le_pow_right (by decide) hx.width)
    have hcap : n*K < 2^w := lt_of_le_of_lt (by
      have hmult := Nat.mul_le_mul_right (n*K) (show 1 ≤ P from hP)
      dsimp [L]
      simpa only [one_mul] using hmult.trans (Nat.le_add_left _ A)) hL
    have hfits (s : Bool) (b : B) : (∑ g, physicalCount (bankWord x j) s b g) < 2^w := by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hx.counts (if s then some j else none) b g)
      exact (by simpa [n] using h : (∑ g, physicalCount (bankWord x j) s b g) ≤ n*K).trans_lt hcap
    obtain ⟨h,hkey,hbound⟩ := choose (bankWord x j) base (packMean prob x) hfits
    have hroute : (Frame.initial (Sum.inr : CountBits B q l w → ChoicePins B q l m w ⊕ _)).eval
        (staged.eval x) = bankWord x j := by funext a; simp [hmid]
    have first (a : ChoicePins B q l m w) : f.eval x (.inl (.inl a)) = win.eval x a := by
      simp [f,next,hmid]
    refine ⟨j,h,⟨fun i => by rw [first]; exact flags i,
      fun p => by rw [first]; exact horig x p, fun a => by simp [f,next,hmid],
      fun b => by simp [f,next,hroute,hkey],?_,?_⟩⟩
    · intro b
      have hbank : (fun a => f.eval x (.inl (.inl (.inl a)))) = win.eval x ∘ Sum.inl :=
        funext fun a => first (.inl a)
      rw [hbank]
      exact hmean b
    · apply hbound.trans
      change score j ≤ ∑ i, prob i * score i
      exact havg

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
