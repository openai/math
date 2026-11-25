import OAI.Computability.BorderVNP.CoverDeckPackRunBounds
import OAI.Computability.BorderVNP.PackedDeckEnergyArrays

/-!
# The normalized concentration bound for the compiled pack choices

The input provides all candidate physical counts. The Boolean output chooses
one motion and one deck key per pack and contains the final histogram and
mean numerator. Under the per-candidate second-moment bound, the choices
on these very wires achieve the normalized bound in equation (6.2).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedDeckCandidate PackedDeckEnergy

private theorem sum_updates {K : ℕ} (A : ℕ → ℕ) (f : Fin K → ℕ) (hz : A 0 = 0)
    (hs : ∀ i : Fin K, A (i.val+1) = A i.val + f i) : A K = ∑ i, f i := by
  let term t := if ht : t < K then f ⟨t,ht⟩ else 0
  have go (t : ℕ) (ht : t ≤ K) : A t = ∑ r ∈ Finset.range t, term r := by
    induction t with
    | zero => simp [hz]
    | succ t ih =>
      have h := hs ⟨t,ht⟩
      simpa [Finset.sum_range_succ,← ih (by omega),term,show t < K from ht] using h
  rw [go K le_rfl,← Fin.sum_univ_eq_sum_range term]
  exact Finset.sum_congr rfl fun i _ => by simp [term,i.isLt]

/-- Eq. (6.2) for the selected motions on the output wires of the actual
near-linear pack sequence. The circuit has fixed gate constants and a
fixed probability denominator across levels and count widths. -/
theorem packConcentration_frames (B : Type) [Fintype B] (q m : ℕ) (prob : Fin m → ℚ)
    (hn : ∀ j, 0 ≤ prob j) (hs : ∑ j, prob j = 1) :
    ∃ P D p : ℕ, 0 < P ∧ ∀ K l w : ℕ, 0 < K → 1 ≤ l → P < 2^w →
      ∃ f : VPVNP.VerifierNetwork.Frame (PackTables B q l m w K) (PackTracePins B q l m w K),
        f.size ≤ 1 + K*(Fintype.card (Fin q → Deck l)*D*(l+w+1)^p) ∧
        ∀ (z : PackTables B q l m w K → Bool) (H : ℕ),
          (∀ i j b g, tableCount z i j b g ≤ H) →
          packRunWidth (Fintype.card (Fin q → Deck l)) P K H ≤ w →
          ∃ (choice : Fin K → Fin m) (deck : Fin K → Fin q → Deck l),
            (∀ i j, f.eval z (.inr (i,.inl j)) = true ↔ j = choice i) ∧
            (∀ i b, f.eval z (.inr (i,.inr b)) = keyWord q l (deck i) b) ∧
            (∀ b g, ParseBatchSort.value (fun s => f.eval z (.inl (.inl (b,g,s)))) =
              ∑ i, tableCount z i (choice i) b (deck i*g)) ∧
            (∀ b, ((P*Fintype.card (Fin q → Deck l) : ℕ) : ℚ)*baseAt prob z K b =
              ParseBatchSort.value (fun s => f.eval z (.inl (.inr (b,s))))) ∧
            ∀ radius : ℝ, 0 ≤ radius →
              (∀ i j, (Fintype.card (Fin q → Deck l) : ℝ) *
                Epoch.binEnergy (fun a : (Fin q → Deck l) × B => (tableCount z i j a.2 a.1 : ℝ)) ≤ radius^2) →
              Real.sqrt (Fintype.card (Fin q → Deck l)) * Real.sqrt (Epoch.binEnergy
                (fun a : (Fin q → Deck l) × B =>
                  (∑ i, moved (tableCount z) i (choice i,deck i) a)/K -
                  (∑ i, Epoch.motionMean (motionWeight (fun _ => prob)) (moved (tableCount z)) i a)/K)) ≤
                radius / Real.sqrt K := by
  obtain ⟨P,D,p,hP,make⟩ := packSequence_frames B q m prob hn hs
  refine ⟨P,D,p,hP,?_⟩
  intro K l w hK hl hw
  obtain ⟨step,f,hsize,verified,trace⟩ := make K l w hl hw
  refine ⟨f,hsize,?_⟩
  intro z H hc hcap
  choose choice deck state using allStates prob hn hs step verified z hc hcap
  have updates (i : Fin K) (b : B) (g : Fin q → Deck l) : bankAt step z (i.val+1) b g =
      bankAt step z i.val b g + tableCount z i (choice i) b (deck i*g) :=
    ((nextBank_eq step z i).1 b g).trans ((state i).accumulated b g)
  have hstart (b : B) (g : Fin q → Deck l) : (bankAt step z 0 b g : ℚ) = baseAt prob z 0 b := by
    simp [baseAt]
  have picked (i : Fin K) : CoverDeck.increment
      (fun b g => (bankAt step z i.val b g : ℚ) - baseAt prob z i.val b)
      (fun b g => (tableCount z i (choice i) b g : ℚ)) (fun b => PackedDeckMean.mean prob (tableCount z i) b 1)
      (deck i) ≤ ∑ j, prob j * uniformScore (bankAt step z i.val) (tableCount z i j) (baseAt prob z i.val)
        (fun b => PackedDeckMean.mean prob (tableCount z i) b 1) := (state i).selected.increment_le
  have hT := (runBankBounds prob hn hs step verified z hc hcap K le_rfl).2
  refine ⟨choice,deck,?_,?_,?_,?_,?_⟩
  · intro i j
    rw [trace z]
    exact (state i).selected.flags j
  · intro i b
    rw [trace z]
    exact (state i).selected.key b
  · intro b g
    rw [trace z]
    exact sum_updates (fun t => bankAt step z t b g) _ (bankAt_zero step z b g) (fun i => updates i b g)
  · intro b
    rw [trace z]
    exact hT b
  · intro radius hr hbound
    have h := run_concentrated hK hr (fun _ => prob) (fun _ => hn) (fun _ => hs) (tableCount z)
      (bankAt step z) (baseAt prob z) choice deck hstart updates (baseAt_succ prob z) picked
      (fun i j => by simpa only [energy_cast_counts] using hbound i j)
    rw [normalized_array (fun _ => prob) (tableCount z) (bankAt step z) (baseAt prob z) choice deck
      hstart updates (baseAt_succ prob z)] at h
    exact h

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
