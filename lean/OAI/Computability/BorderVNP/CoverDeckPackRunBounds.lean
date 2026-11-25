import OAI.Computability.BorderVNP.CoverDeckPackRunData

/-! # Capacity and mean invariants for all stages of the pack circuit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedDeckCandidate
open VPVNP.VerifierNetwork (Frame)

variable {B : Type*} [Fintype B] {q l m w K P H : ℕ}

/-- One working width covers the entire sequence of K packs when all individual
candidate cells are bounded by H. -/
def packRunWidth (n P K H : ℕ) : ℕ :=
  choiceBits n (P*n) (K*H+H) ((P*n)*(K*H)+P*(n*(K*H+H)))

/-- The physically read and written bank-state specification of the compiled
stage. -/
def VerifiedPackStep (P : ℕ) (prob : Fin m → ℚ)
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w)) : Prop :=
  ∀ x base N A, PackInputFits q l m w P N A x base → ∃ j h, BankState P prob x base (step.eval x) j h

private theorem fitsAt (prob : Fin m → ℚ) (hn : ∀ j, 0 ≤ prob j) (hs : ∑ j, prob j = 1)
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (hc : ∀ i j b g, tableCount z i j b g ≤ H)
    (hw : packRunWidth (Fintype.card (Fin q → Deck l)) P K H ≤ w) (i : Fin K)
    (hc0 : ∀ b g, bankAt step z i.val b g ≤ i.val*H)
    (hT : ∀ b, ((P*Fintype.card (Fin q → Deck l) : ℕ) : ℚ)*baseAt prob z i.val b = storedAt step z i.val b) :
    PackInputFits q l m w P (K*H+H) ((P*Fintype.card (Fin q → Deck l))*(K*H))
      (stageAssignment z (priorAt step z i.val) i) (baseAt prob z i.val) := by
  let D := P*Fintype.card (Fin q → Deck l)
  refine ⟨hT,?_,?_,hw⟩
  · intro b
    change storedAt step z i.val b ≤ D*(K*H)
    have h₁ := baseAt_le prob hn hs z H hc i.val b
    have h₂ : (i.val : ℚ)*H ≤ (K : ℚ)*H :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr i.isLt.le) (Nat.cast_nonneg _)
    have hh : (storedAt step z i.val b : ℚ) ≤ (D : ℚ)*((K:ℚ)*H) := by
      rw [← hT b]
      exact mul_le_mul_of_nonneg_left (h₁.trans h₂) (Nat.cast_nonneg D)
    exact_mod_cast hh
  · rintro (_|j) b g
    · exact (hc0 b g).trans ((Nat.mul_le_mul_right H i.isLt.le).trans (Nat.le_add_right _ _))
    · exact (hc i j b g).trans (Nat.le_add_left _ _)

/-- The two stored banks stay within range and contain the exact physical
counts and cleared expected means at every prefix. -/
theorem runBankBounds (prob : Fin m → ℚ) (hn : ∀ j, 0 ≤ prob j) (hs : ∑ j, prob j = 1)
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (verified : VerifiedPackStep P prob step) (z : PackTables B q l m w K → Bool)
    (hc : ∀ i j b g, tableCount z i j b g ≤ H)
    (hw : packRunWidth (Fintype.card (Fin q → Deck l)) P K H ≤ w) (r : ℕ) (hr : r ≤ K) :
    (∀ b g, bankAt step z r b g ≤ r*H) ∧
    ∀ b, ((P*Fintype.card (Fin q → Deck l) : ℕ) : ℚ)*baseAt prob z r b = storedAt step z r b := by
  induction r with
  | zero => simp [baseAt]
  | succ r ih =>
    let i : Fin K := ⟨r,by omega⟩
    obtain ⟨hcounts,hT⟩ := ih (by omega)
    obtain ⟨j,h,hstate⟩ := verified _ _ _ _ (fitsAt prob hn hs step z hc hw i hcounts hT)
    obtain ⟨nextCount,nextMean⟩ := nextBank_eq step z i
    constructor
    · intro b g
      have h₁ : bankAt step z (r+1) b g = bankAt step z r b g + tableCount z i j b (h*g) :=
        (nextCount b g).trans (hstate.accumulated b g)
      rw [h₁,Nat.succ_mul]
      exact Nat.add_le_add (hcounts b g) (hc i j b (h*g))
    · intro b
      change ((P*Fintype.card (Fin q → Deck l) : ℕ) : ℚ)*baseAt prob z (i.val+1) b = storedAt step z (i.val+1) b
      rw [baseAt_succ,nextMean]
      exact hstate.selected.updated b

/-- Each circuit stage has a genuine selected finite candidate and deck
translation, with no assumption about a future pack's choice. -/
theorem allStates (prob : Fin m → ℚ) (hn : ∀ j, 0 ≤ prob j) (hs : ∑ j, prob j = 1)
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (verified : VerifiedPackStep P prob step) (z : PackTables B q l m w K → Bool)
    (hc : ∀ i j b g, tableCount z i j b g ≤ H)
    (hw : packRunWidth (Fintype.card (Fin q → Deck l)) P K H ≤ w) (i : Fin K) :
    ∃ j h, BankState P prob (stageAssignment z (priorAt step z i.val) i) (baseAt prob z i.val)
      (stateAt step z i) j h := by
  obtain ⟨hcounts,hT⟩ := runBankBounds prob hn hs step verified z hc hw i.val i.isLt.le
  exact verified _ _ _ _ (fitsAt prob hn hs step z hc hw i hcounts hT)

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
