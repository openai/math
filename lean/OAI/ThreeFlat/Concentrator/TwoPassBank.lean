import OAI.ThreeFlat.Concentrator.Family
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Public data for a constructive two-pass concentrator

The greedy candidates, the reserve incidence graph, and the placement of both
banks are specified before the input mask. The residue and sparse-mixing bounds
therefore apply directly to the checkable, bounded-width two-pass reports.
-/

namespace ThreeFlat.Concentrator

noncomputable section

/-- A public pair of banks, including all the data read by the two-pass checker. -/
structure TwoPassBank (C q degree R : ℕ) where
  primary : ℕ
  reserveSize : ℕ
  slots : ℕ
  threshold : ℕ
  N : Fin (C*R) → List (Fin primary)
  G : ReserveGraph (Fin (C*R)) (Fin reserveSize)
  address : (Fin primary ⊕ (Fin reserveSize × Fin slots)) ≃ Fin R
  reserveBound : reserveSize ≤ 2*(C*R)
  slotBound : slots ≤ degree
  thresholdBound : threshold ≤ C*R
  sorted : ∀ x, (N x).toFinset.sort (· ≤ ·) = N x
  primaryDegree : ∀ x, (N x).length ≤ degree
  reverseDegree : ∀ y, (Finset.univ.filter fun x => y ∈ N x).card ≤ degree
  incidentDegree : ∀ v, (G.incident Finset.univ v).card ≤ degree
  missed : ∀ xs : List (Fin (C*R)), q*xs.length + R ≤ q*R →
    (Greedy.run N xs Finset.univ).missed.card < threshold
  sparse : ∀ H : Finset (Fin reserveSize), (slots+1)*H.card ≤ 2*threshold →
    4*(G.internalEdges Finset.univ H).card ≤ (slots+1)*H.card

/-- There are uniform-degree public two-pass data at every sufficiently large size. -/
theorem exists_two_pass_banks {C q : ℕ} (hC : 0 < C) (hq : 0 < q) :
    ∃ cutoff degree, ∀ R, cutoff ≤ C*R → Nonempty (TwoPassBank C q degree R) := by
  classical
  let K := budgetDenom C q
  have hK : 0 < K := by simp only [K, budgetDenom]; positivity
  let ρ : ℝ := 1 / (32 * (K : ℝ)^2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨g, graphs⟩ := exists_greedy_candidate_cover.{0,0} hρ
  obtain ⟨d, hd, reserves⟩ := exists_reserve_family_with_size hC hq
  let cutoff := max d (16*K^2)
  refine ⟨cutoff, g+2*d, fun R large => ?_⟩
  obtain ⟨m, _, mBound, capacity, G, rev, sparse⟩ := reserves R ((le_max_left _ _).trans large)
  let s := reserveSlots C q d
  let t := reserveThreshold C q R
  let p := R-m*s
  have bound : m*s+t ≤ R := (Nat.le_mul_of_pos_left _ hq).trans capacity
  have psize : p ≤ C*R := (Nat.sub_le ..).trans (Nat.le_mul_of_pos_left _ hC)
  have workPos : 0 < C*R := hd.trans_le ((le_max_left _ _).trans large)
  obtain ⟨N, left, right, greedy⟩ := graphs (Fin (C*R)) (Fin p) (C*R) workPos
    (by simp) (by simpa using psize)
  let sortedN (x) := (N x).toFinset.sort (· ≤ ·)
  have covers (x r) : r ∈ N x → r ∈ sortedN x := by simp [sortedN]
  have card : Fintype.card (Fin p ⊕ (Fin m × Fin s)) = R := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
    dsimp [p]
    omega
  refine ⟨⟨p, m, s, t, sortedN, G, Fintype.equivFinOfCardEq card, mBound, ?_, ?_,
    fun x => by simp [sortedN], ?_, ?_,
    fun v => (rev v).trans (by omega), ?_, sparse⟩⟩
  · exact (Nat.div_le_self _ _).trans (by omega : d ≤ g+2*d)
  · exact Nat.div_le_self _ _
  · intro x
    simp only [sortedN, Finset.length_sort]
    exact (N x).toFinset_card_le.trans ((left x).trans (by omega))
  · intro y
    simpa [sortedN] using (right y).trans (by omega : g ≤ g+2*d)
  · intro xs legal
    have budget : xs.length + t + m*s ≤ R := by
      apply Nat.le_of_mul_le_mul_left (c := q) _ hq
      calc
        q*(xs.length+t+m*s) = q*xs.length+q*(m*s+t) := by ring
        _ ≤ q*xs.length+R := Nat.add_le_add_left capacity _
        _ ≤ _ := legal
    have slack : xs.length+t ≤ p := by dsimp [p]; omega
    exact greedy sortedN covers xs Finset.univ t (by simpa using slack)
      (threshold_density hC hq ((le_max_right _ _).trans large))

end
end ThreeFlat.Concentrator

end OAI
