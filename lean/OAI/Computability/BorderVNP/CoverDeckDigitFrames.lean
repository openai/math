import OAI.Computability.BorderVNP.CoverDeckDigitRead

/-!
# Boolean circuits for a complete conditional deck-digit choice

The only variable inputs are the two physical count arrays and the current
product tile. Relative-bin means cancel in the comparisons, so one circuit
works for all rational centering constants. Its output is the child chosen
by the exact rational routine in the manuscript.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open VPVNP.VerifierNetwork (Frame)

/-- Prior and candidate physical count arrays on the full cover. -/
abbrev CountBits (B : Type*) (q l w : ℕ) := Bool × B × (Fin q → Deck l) × Fin w

/-- A nonnegative bin count represented by ordinary most-significant-first wires. -/
def physicalCount {B : Type*} {q l w : ℕ} (z : CountBits B q l w → Bool)
    (s : Bool) (b : B) (g : Fin q → Deck l) : ℕ :=
  ParseBatchSort.value fun j => z (s,b,g,j)

/-- The complete deterministic digit circuit and its explicit gate bound,
uniform in the number of factors, full depth, digit position and word width. -/
theorem digit_frames :
    ∃ U t C e : ℕ, ∀ (B : Type) [Fintype B] (q d l w : ℕ) (hle : d+1 ≤ l),
      ∃ f : Frame (CountBits B q l w ⊕ Fin (keyWidth q d)) (Fin (keyWidth q (d+1))),
        f.size ≤ digitCost B q d l w U t C e ∧
        ∀ (z : CountBits B q l w → Bool) (u : Fin q → Deck d) (base mean : B → ℚ),
          (∀ s b, (∑ g, physicalCount z s b g) < 2^w) →
          ∃ v, CoverDeck.chooseResidue (CoverDeck.conditionalScore (productReduction q hle)
            (fun b g => (physicalCount z false b g : ℚ) - base b)
            (fun b g => (physicalCount z true b g : ℚ)) mean) (digitChildren q d u) = some v ∧
            f.eval (Sum.elim z (keyWord q d u)) = keyWord q (d+1) v := by
  obtain ⟨U,t,makeRequest⟩ := childRequests_frames
  obtain ⟨C,e,makeChoice⟩ := PackedDeckChoice.exists_choices
  refine ⟨U,t,C,e,?_⟩
  intro B instB q d l w hle
  let m := childCount q d
  let k := keyWidth q (d+1)
  let Raw := CountBits B q l w
  let Parent := Fin (keyWidth q d)
  let Children := Fin m × Fin k
  let Reads := Fin m × (Fin q → Deck (d+1)) × Fin k
  let Src := Raw ⊕ Parent
  let Mid := Src ⊕ (Children ⊕ Reads)
  let π := productReduction q hle
  obtain ⟨req,hr,child,translate⟩ := makeRequest q d
  obtain ⟨decide,hs,choice⟩ := makeChoice B (Fin q → Deck l) (Fin q → Deck (d+1))
    m k w π (productReduction_surjective q hle) (productKey q (d+1))
  let moved : Frame Src (Children ⊕ Reads) := req.subst (Frame.initial Sum.inr)
  let before : Frame Src Mid := moved.withInput
  let inputs : Frame Mid (Raw ⊕ Reads) :=
    Frame.initial (Sum.elim (fun b => .inl (.inl b)) (fun r => .inr (.inr r)))
  let view : Frame Mid (Children ⊕ Fin m) := (decide.subst inputs).withInput.select
    (Sum.elim (fun c => .inl (.inr (.inl c))) Sum.inr)
  let f := (readFlagged m k).subst (view.subst before)
  refine ⟨f,?_,?_⟩
  · have h := Nat.add_le_add (Nat.add_le_add hr hs) (readFlagged_size m k)
    have hb : before.size = req.size := (Frame.withInput_size moved).trans (by simp [moved])
    simpa [f,view,inputs,hb,digitCost,m,k] using h
  · intro z u base mean fits
    let kids := childAt q d u
    let a : Src → Bool := Sum.elim z (keyWord q d u)
    let ch : Children → Bool := fun p => keyWord q (d+1) (kids p.1) p.2
    let read : Reads → Bool := fun p => keyWord q (d+1) (kids p.1 * p.2.1) p.2.2
    let mid : Mid → Bool := Sum.elim a (Sum.elim ch read)
    let x : Raw ⊕ Reads → Bool := Sum.elim z read
    have hparent : (Frame.initial (Sum.inr : Parent → Src)).eval a = keyWord q d u := by
      funext b
      simp [a]
    have hmoved : moved.eval a = req.eval (keyWord q d u) := by
      funext p; simp only [moved,Frame.subst_eval,hparent]
    have hbefore : before.eval a = mid := by
      funext j
      rcases j with j | (j | j)
      · exact Frame.withInput_eval_inl moved a j
      · exact (Frame.withInput_eval_inr moved a (.inl j)).trans
          ((congrFun hmoved (.inl j)).trans (child u j.1 j.2))
      · exact (Frame.withInput_eval_inr moved a (.inr j)).trans
          ((congrFun hmoved (.inr j)).trans (translate u j.1 j.2.1 j.2.2))
    have hx : inputs.eval mid = x := by funext j; cases j <;> simp [inputs,mid,a,x]
    let score := CoverDeck.conditionalScore π
      (fun b g => (physicalCount z false b g : ℚ) - base b)
      (fun b g => (physicalCount z true b g : ℚ)) mean
    have haddr (i : Fin m) (v : Fin q → Deck (d+1)) :
        PackedDeckScore.translated x i v = (productKey q (d+1) (kids i * v)).val := rfl
    have hfit s b v : CoverDeck.histogram π (PackedDeckScore.counts x s b) v < 2^w :=
      (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans_lt (fits s b)
    have hflags (i : Fin m) : decide.eval x i = true ↔
        (List.finRange m).argmin (score ∘ kids) = some i :=
      choice x kids base mean haddr hfit i
    obtain ⟨j,hj⟩ : ∃ j, (List.finRange m).argmin (score ∘ kids) = some j := by
      cases h : (List.finRange m).argmin (score ∘ kids) with
      | some i => exact ⟨i,rfl⟩
      | none =>
        have hl := congrArg List.length (List.argmin_eq_none.mp h)
        have hp := childCount_pos q d
        simp [m] at hl
        omega
    refine ⟨kids j,?_,?_⟩
    · simpa only [kids,childAt_list] using PackedDeckChoice.chosen_child kids score hj
    · have winner (i : Fin m) : view.eval mid (.inr i) = true ↔ i = j := by
        simp only [view,Frame.select_eval,Sum.elim_inr,Frame.withInput_eval_inr,Frame.subst_eval,hx]
        rw [hflags i,hj,Option.some.injEq]
        exact eq_comm
      have selected (b : Fin k) : view.eval mid (.inl (j,b)) = keyWord q (d+1) (kids j) b := by
        simp [view,mid,ch]
      funext b
      simp only [f,Frame.subst_eval]
      change (readFlagged m k).eval ((view.subst before).eval a) b = _
      have hv : (view.subst before).eval a = view.eval mid := by
        funext i; simp [hbefore]
      rw [hv]
      exact (readFlagged_eval m k (view.eval mid) j winner b).trans (selected b)

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
