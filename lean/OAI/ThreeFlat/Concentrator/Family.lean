import OAI.ThreeFlat.Concentrator.GreedyFamily
import OAI.ThreeFlat.Concentrator.ReserveFamily
import OAI.ThreeFlat.Concentrator.TwoPass
import OAI.ThreeFlat.Concentrator.PublicGraph

namespace OAI
/-! # Fixed bounded-degree concentrators

For each constant left-to-right ratio `C` and reciprocal slack `q`, one
degree bound applies at every right-bank size. The public neighbors are fixed
before the active mask. The matched positions are drawn from exactly `R`
slots, including the reserve.
-/

namespace ThreeFlat.Concentrator

/-- The matching and bounded-degree conclusions of the concentrator lemma for
the integral ratio `C` and slack `1/q`. -/
theorem exists_concentrator_family {C q : ℕ} (hC : 0 < C) (hq : 0 < q) :
    ∃ degree : ℕ, ∀ R : ℕ, ∃ N : Fin (C * R) → Finset (Fin R),
      (∀ x, (N x).card ≤ degree) ∧
      (∀ r, (Finset.univ.filter fun x => r ∈ N x).card ≤ degree) ∧
      ∀ (xs : List (Fin (C * R))), xs.Nodup → q * xs.length + R ≤ q * R →
        ∃ assign : xs.toFinset ↪ Fin R, ∀ x, assign x ∈ N x.val := by
  classical
  let K := budgetDenom C q
  have hK : 0 < K := by simp only [K, budgetDenom]; positivity
  let ρ : ℝ := 1 / (32 * (K : ℝ) ^ 2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨g, graphs⟩ := exists_greedy_candidates.{0,0} hρ
  obtain ⟨d, hd, reserves⟩ := exists_reserve_family hC hq
  let cutoff := max d (16 * K ^ 2)
  let degree := cutoff + g + 2 * d
  refine ⟨degree, fun R => ?_⟩
  have rle := Nat.le_mul_of_pos_left R hC
  by_cases large : cutoff ≤ C * R
  · obtain ⟨m, _, capacity, G, rev, sparse⟩ :=
      reserves R ((le_max_left _ _).trans large)
    let s := reserveSlots C q d
    let t := reserveThreshold C q R
    let primary := R - m * s
    have bound : m * s + t ≤ R := (Nat.le_mul_of_pos_left _ hq).trans capacity
    have workPos : 0 < C * R := hd.trans_le ((le_max_left _ _).trans large)
    have psize : primary ≤ C * R := (Nat.sub_le ..).trans rle
    obtain ⟨N, left, right, greedy⟩ := graphs (Fin (C * R)) (Fin primary) (C * R) workPos
      (by simp) (by simpa using psize)
    have card : Fintype.card (Fin primary ⊕ (Fin m × Fin s)) = R := by
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
      dsimp [primary]
      omega
    let e := (Fintype.equivFinOfCardEq card).toEmbedding
    refine ⟨publicNeighbors e N G, ?_, ?_, ?_⟩
    · intro x
      have hs : s ≤ d := Nat.div_le_self ..
      exact (publicNeighbors_left_degree e N G left x).trans (by dsimp [degree]; omega)
    · intro r
      exact (publicNeighbors_right_degree e N G right rev r).trans (by dsimp [degree]; omega)
    · intro xs nodup legal
      have budget : xs.length + t + m * s ≤ R := by
        apply Nat.le_of_mul_le_mul_left (c := q) _ hq
        calc
          q * (xs.length + t + m * s) = q * xs.length + q * (m * s + t) := by ring
          _ ≤ q * xs.length + R := Nat.add_le_add_left capacity _
          _ ≤ _ := legal
      have slack : xs.length + t ≤ primary := by dsimp [primary]; omega
      have size := threshold_density hC hq ((le_max_right _ _).trans large)
      have missed := greedy xs Finset.univ t (by simpa using slack) size
      let cap := Nat.log 2 t + 1
      have long : t ≤ 2 ^ cap := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) t).le
      obtain ⟨f, hits⟩ := two_pass_matching_of_residual N G xs Finset.univ Finset.univ
        t s cap nodup (fun _ _ => Finset.mem_univ _) missed sparse long
      refine ⟨f.trans e, fun x => ?_⟩
      apply mem_publicNeighbors_of_adjacent e N G x.val (f x)
      have hit := hits x
      cases he : f x with
      | inl a => rw [he] at hit; exact hit.2
      | inr z => simpa only [he] using hit
  · refine ⟨fun _ => Finset.univ, ?_, ?_, ?_⟩
    · intro x
      simp only [Finset.card_univ, Fintype.card_fin]
      dsimp [degree]
      omega
    · intro r
      apply (Finset.card_le_univ _).trans
      simp only [Fintype.card_fin]
      dsimp [degree]
      omega
    · intro xs nodup legal
      have n : xs.length ≤ R := Nat.le_of_mul_le_mul_left
        ((Nat.le_add_right _ R).trans legal) hq
      obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := xs.toFinset) (β := Fin R)
        (by simpa only [Fintype.card_coe, Fintype.card_fin, List.toFinset_card_of_nodup nodup] using n)
      exact ⟨f, fun _ => Finset.mem_univ _⟩

/-- With at most `C R` left slots, any activity mask of density at most
`1 - ε` relative to the right bank can be injected into its public neighbors.
The degree bound is uniform in the sizes and the mask. -/
theorem exists_concentrator {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ degree : ℕ, ∀ n R : ℕ, (n : ℝ) ≤ C * R →
      ∃ N : Fin n → Finset (Fin R), (∀ x, (N x).card ≤ degree) ∧
        (∀ r, (Finset.univ.filter fun x => r ∈ N x).card ≤ degree) ∧
        ∀ (xs : List (Fin n)), xs.Nodup → (xs.length : ℝ) ≤ (1 - ε) * R →
          ∃ assign : xs.toFinset ↪ Fin R, ∀ x, assign x ∈ N x.val := by
  classical
  obtain ⟨q, hq, masks⟩ := exists_slack_denominator hε
  let k := ⌈C⌉₊
  have hk : 0 < k := Nat.ceil_pos.mpr (zero_lt_one.trans_le hC)
  obtain ⟨degree, graphs⟩ := exists_concentrator_family hk hq
  refine ⟨degree, fun n R ratio => ?_⟩
  have hn : n ≤ k * R := by
    exact_mod_cast ratio.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg R))
  let e := Fin.castLEEmb hn
  obtain ⟨N, left, right, matchAll⟩ := graphs R
  refine ⟨fun x => N (e x), fun x => left _, ?_, ?_⟩
  · intro r
    have sub : (Finset.univ.filter fun x => r ∈ N (e x)).map e ⊆
        Finset.univ.filter (fun y => r ∈ N y) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    simpa only [Finset.card_map] using (Finset.card_le_card sub).trans (right r)
  · intro xs nodup legal
    have bound := masks R xs.length legal
    obtain ⟨f, hf⟩ := matchAll (xs.map e) (nodup.map e.injective) (by simpa using bound)
    let lift : xs.toFinset ↪ (xs.map e).toFinset :=
      { toFun := fun x => ⟨e x.val, List.mem_toFinset.mpr (List.mem_map.mpr
          ⟨x.val, List.mem_toFinset.mp x.property, rfl⟩)⟩
        inj' := fun x y he => Subtype.ext (e.injective
          (congrArg (fun z : (xs.map e).toFinset => z.val) he)) }
    exact ⟨lift.trans f, fun x => hf (lift x)⟩

end ThreeFlat.Concentrator

end OAI
