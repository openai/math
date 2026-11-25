import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Charging balanced separators to vertices

The planar separator theorem supplies a hereditary bound on the size of a vertex
separator. Splitting at that separator recursively until all components are small
deletes a uniformly small fraction of the vertices. The argument applies to any
finite induced subgraph satisfying the same separator bound.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

universe u

variable {V : Type*} [DecidableEq V]

/-- The connected components of a finite induced subgraph, as vertex sets. -/
structure ComponentPieces (G : SimpleGraph V) (T : Finset V) (blocks : Finset (Finset V)) : Prop where
  subset : ∀ P ∈ blocks, P ⊆ T
  cover : ∀ x ∈ T, ∃ P ∈ blocks, x ∈ P
  disjoint : (blocks : Set (Finset V)).PairwiseDisjoint id
  closed : ∀ P ∈ blocks, ∀ x ∈ P, ∀ y ∈ T, G.Adj x y → y ∈ P
  connected : ∀ P ∈ blocks, (G.induce (P : Set V)).Connected

/-- Every nonempty induced subgraph has a square-root separator whose remaining
components have size at most two thirds of the original size. -/
def BalancedSeparators (G : SimpleGraph V) (S : Finset V) (c : ℝ) : Prop :=
  ∀ T ⊆ S, T.Nonempty → ∃ D ⊆ T, ∃ blocks, ComponentPieces G (T \ D) blocks ∧
    (D.card : ℝ) ≤ c * Real.sqrt T.card ∧ ∀ P ∈ blocks, 3 * P.card ≤ 2 * T.card

/-- Decompose a finite induced graph into its connected vertex sets. -/
theorem componentPieces_exists (G : SimpleGraph V) (T : Finset V) :
    ∃ blocks, ComponentPieces G T blocks := by
  classical
  let H := G.induce (T : Set V)
  let part (c : H.ConnectedComponent) := T.filter (fun x => ∃ h : x ∈ T, H.connectedComponentMk ⟨x, h⟩ = c)
  have hpart (c : H.ConnectedComponent) (x : V) : x ∈ part c ↔ ∃ h : x ∈ T, H.connectedComponentMk ⟨x, h⟩ = c := by
    simp only [part, Finset.mem_filter, and_iff_right_iff_imp]
    exact fun ⟨hx, _⟩ => hx
  let blocks := T.attach.image (fun x => part (H.connectedComponentMk x))
  have get {P} (hP : P ∈ blocks) : ∃ c, P = part c := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨_, rfl⟩
  refine ⟨blocks, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro P hP x hx
    obtain ⟨c, rfl⟩ := get hP
    exact ((hpart c x).mp hx).choose
  · intro x hx
    let v : T := ⟨x, hx⟩
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ v), (hpart _ x).mpr ⟨hx, rfl⟩⟩
  · intro P hP Q hQ hne
    obtain ⟨c, rfl⟩ := get hP
    obtain ⟨d, rfl⟩ := get hQ
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨_, hc⟩ := (hpart c x).mp hx
    obtain ⟨_, hd⟩ := (hpart d x).mp hy
    exact hne (congrArg part (hc.symm.trans hd))
  · intro P hP x hx y hy hxy
    obtain ⟨c, rfl⟩ := get hP
    obtain ⟨ht, hc⟩ := (hpart c x).mp hx
    exact (hpart c y).mpr ⟨hy, (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show H.Adj ⟨x, ht⟩ ⟨y, hy⟩ from hxy)).symm.trans hc⟩
  · intro P hP
    obtain ⟨c, rfl⟩ := get hP
    let e : c.toSimpleGraph ≃g G.induce (part c : Set V) := {
      toFun := fun x => ⟨x.1.1, (hpart _ _).mpr ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, ((hpart _ _).mp x.2).choose⟩, ((hpart _ _).mp x.2).choose_spec⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
    exact e.connected_iff.mp c.connected_toSimpleGraph

private theorem ComponentPieces.sum_card_le {G : SimpleGraph V} {T : Finset V} {B : Finset (Finset V)}
    (h : ComponentPieces G T B) : ∑ P ∈ B, P.card ≤ T.card := by
  classical
  calc
    ∑ P ∈ B, P.card = (B.biUnion id).card := (Finset.card_biUnion h.disjoint).symm
    _ ≤ T.card := Finset.card_le_card (by simpa [Finset.biUnion_subset_iff_forall_subset] using h.subset)

/-- Independent deletions in separated components can be performed together. -/
private theorem ComponentPieces.glue {G : SimpleGraph V} {S A : Finset V} {B : Finset (Finset V)}
    (hB : ComponentPieces G (S \ A) B) (d : Finset V → Finset V)
    (p : Finset V → Finset (Finset V)) (hd : ∀ Q ∈ B, d Q ⊆ Q)
    (hp : ∀ Q ∈ B, ComponentPieces G (Q \ d Q) (p Q)) :
    ComponentPieces G (S \ (A ∪ B.biUnion d)) (B.biUnion p) := by
  classical
  have uniq {Q R : Finset V} (hQ : Q ∈ B) (hR : R ∈ B) {x} (hx : x ∈ Q) (hy : x ∈ R) : Q = R := by
    by_contra hne
    exact Finset.disjoint_left.mp (hB.disjoint hQ hR hne) hx hy
  have local_mem {Q : Finset V} (hQ : Q ∈ B) {x} (hx : x ∈ Q) :
      x ∈ S \ (A ∪ B.biUnion d) ↔ x ∈ Q \ d Q := by
    constructor
    · intro h
      exact Finset.mem_sdiff.mpr ⟨hx, fun hxd => (Finset.mem_sdiff.mp h).2
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨Q, hQ, hxd⟩))⟩
    · intro h
      obtain ⟨hS, hA⟩ := Finset.mem_sdiff.mp (hB.subset Q hQ hx)
      refine Finset.mem_sdiff.mpr ⟨hS, ?_⟩
      intro ha
      rcases Finset.mem_union.mp ha with ha | hD
      · exact hA ha
      · obtain ⟨R, hR, hxR⟩ := Finset.mem_biUnion.mp hD
        obtain rfl := uniq hQ hR hx (hd R hR hxR)
        exact (Finset.mem_sdiff.mp h).2 hxR
  have survivor {x} (hx : x ∈ S \ (A ∪ B.biUnion d)) : x ∈ S \ A :=
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, fun h =>
      (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P hP x hx
    obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
    have h := (hp Q hQ).subset P hPQ hx
    exact (local_mem hQ (Finset.mem_sdiff.mp h).1).mpr h
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := hB.cover x (survivor hx)
    obtain ⟨P, hP, hxP⟩ := (hp Q hQ).cover x ((local_mem hQ hxQ).mp hx)
    exact ⟨P, Finset.mem_biUnion.mpr ⟨Q, hQ, hP⟩, hxP⟩
  · intro P hP R hR hne
    obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨U, hU, hRU⟩ := Finset.mem_biUnion.mp hR
    apply Finset.disjoint_left.mpr
    intro x hxP hxR
    obtain rfl := uniq hQ hU (Finset.mem_sdiff.mp ((hp Q hQ).subset P hPQ hxP)).1
      (Finset.mem_sdiff.mp ((hp U hU).subset R hRU hxR)).1
    exact Finset.disjoint_left.mp ((hp Q hQ).disjoint hPQ hRU hne) hxP hxR
  · intro P hP x hx y hy hxy
    obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
    have hxQ := (Finset.mem_sdiff.mp ((hp Q hQ).subset P hPQ hx)).1
    have hyQ := hB.closed Q hQ x hxQ y (survivor hy) hxy
    exact (hp Q hQ).closed P hPQ x hx y ((local_mem hQ hyQ).mp hy) hxy
  · intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
    exact (hp Q hQ).connected P hPQ

/-- A bound of `c √m` on balanced separators suffices to delete an arbitrarily
small fraction of the vertices and leave components of bounded size. The cutoff
depends only on `c` and `ε`, uniformly in the graph and its vertex set. -/
theorem exists_smallPieces_of_balancedSeparators (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (V : Type u) [DecidableEq V] (G : SimpleGraph V) (S : Finset V), BalancedSeparators G S c →
      ∃ D ⊆ S, ∃ blocks, ComponentPieces G (S \ D) blocks ∧ (∀ P ∈ blocks, P.card ≤ K) ∧
        (D.card : ℝ) ≤ ε * S.card := by
  classical
  obtain ⟨b, hb⟩ := exists_nat_gt (max 1 (6 * c / ε))
  have hb1 : (1 : ℝ) ≤ b := (le_max_left _ _).trans hb.le
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans_le hb1
  have hbound : 6 * c / b ≤ ε := by
    apply (div_le_iff₀ hb0).mpr
    have := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hb.le)
    linarith
  refine ⟨b ^ 2, fun V _ G S hsep => ?_⟩
  -- At level `r`, the largest set has size `t r ^ 2`. The charge to one
  -- vertex from splitting a set above the preceding level is at most `c / t r`.
  let t (r : ℕ) := (b : ℝ) * (6 / 5 : ℝ) ^ r
  let charge (r : ℕ) := 6 * c / b - 6 * c / t r
  have tpos (r) : 0 < t r := by dsimp [t]; positivity
  have tnext (r) : t (r + 1) = t r * (6 / 5) := by simp [t, pow_succ, mul_assoc]
  have hstep (r) : charge (r + 1) = charge r + c / t r := by
    simp only [charge, tnext]
    field_simp
    ring
  have cpos (r) : 0 ≤ charge r := by
    induction r with
    | zero => simp [charge, t]
    | succ r ih => rw [hstep]; exact add_nonneg ih (div_nonneg hc (tpos r).le)
  have aux (r : ℕ) : ∀ T ⊆ S, (T.card : ℝ) ≤ t r ^ 2 →
      ∃ D ⊆ T, ∃ blocks, ComponentPieces G (T \ D) blocks ∧ (∀ P ∈ blocks, P.card ≤ b ^ 2) ∧
        (D.card : ℝ) ≤ charge r * T.card := by
    induction r with
    | zero =>
      intro T hTS ht
      obtain ⟨blocks, hp⟩ := componentPieces_exists G T
      have ht' : T.card ≤ b ^ 2 := by
        simp [t] at ht
        exact_mod_cast ht
      exact ⟨∅, Finset.empty_subset _, blocks, by simpa using hp,
        fun P hP => (Finset.card_le_card (hp.subset P hP)).trans ht', by simp [charge, t]⟩
    | succ r ih =>
      intro T hTS ht
      by_cases hsmall : (T.card : ℝ) ≤ t r ^ 2
      · obtain ⟨D, hd, blocks, hp, hsz, hcost⟩ := ih T hTS hsmall
        refine ⟨D, hd, blocks, hp, hsz, hcost.trans ?_⟩
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hstep]
        exact le_add_of_nonneg_right (div_nonneg hc (tpos r).le)
      have hlarge := lt_of_not_ge hsmall
      have hnonempty : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast (lt_of_le_of_lt (sq_nonneg _) hlarge))
      obtain ⟨A, hAT, B, hB, hA, hsize⟩ := hsep T hTS hnonempty
      have sub (Q) (hQ : Q ∈ B) : Q ⊆ T := (hB.subset Q hQ).trans Finset.sdiff_subset
      have child (Q) (hQ : Q ∈ B) : (Q.card : ℝ) ≤ t r ^ 2 := by
        have hs : 3 * (Q.card : ℝ) ≤ 2 * T.card := by exact_mod_cast hsize Q hQ
        rw [tnext] at ht
        nlinarith [sq_nonneg (t r)]
      choose d hd p hp hsz hcost using fun Q hQ => ih Q ((sub Q hQ).trans hTS) (child Q hQ)
      -- Extend the choices over `B` to functions of unrestricted finite subsets.
      let d' (Q : Finset V) := if h : Q ∈ B then d Q h else ∅
      let p' (Q : Finset V) := if h : Q ∈ B then p Q h else ∅
      have hd' (Q) (hQ : Q ∈ B) : d' Q ⊆ Q := by simpa [d', hQ] using hd Q hQ
      have hp' (Q) (hQ : Q ∈ B) : ComponentPieces G (Q \ d' Q) (p' Q) := by
        simpa [d', p', hQ] using hp Q hQ
      have hsum : (∑ Q ∈ B, ((d' Q).card : ℝ)) ≤ charge r * T.card := by
        calc
          _ ≤ ∑ Q ∈ B, charge r * Q.card := Finset.sum_le_sum fun Q hQ => by
            simpa [d', hQ] using hcost Q hQ
          _ = charge r * ∑ Q ∈ B, (Q.card : ℝ) := (Finset.mul_sum ..).symm
          _ ≤ charge r * T.card := by
            apply mul_le_mul_of_nonneg_left _ (cpos r)
            exact_mod_cast hB.sum_card_le.trans (Finset.card_le_card Finset.sdiff_subset)
      have hsqrt := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T.card)
      have hroot : t r ≤ Real.sqrt T.card := by nlinarith [Real.sqrt_nonneg T.card, tpos r]
      have hsepCost : (A.card : ℝ) ≤ (c / t r) * T.card := by
        apply hA.trans
        calc
          c * Real.sqrt T.card = (c / t r) * (t r * Real.sqrt T.card) := by field_simp [(tpos r).ne']
          _ ≤ (c / t r) * T.card := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hc (tpos r).le)
            nlinarith [mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg T.card)]
      refine ⟨A ∪ B.biUnion d', Finset.union_subset hAT ?_, B.biUnion p', hB.glue d' p' hd' hp', ?_, ?_⟩
      · exact Finset.biUnion_subset_iff_forall_subset.mpr (fun Q hQ => (hd' Q hQ).trans (sub Q hQ))
      · intro P hP
        obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
        exact hsz Q hQ P (by simpa [p', hQ] using hPQ)
      · calc
          ((A ∪ B.biUnion d').card : ℝ) ≤ A.card + ∑ Q ∈ B, ((d' Q).card : ℝ) := by
            exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
          _ ≤ (c / t r) * T.card + charge r * T.card := add_le_add hsepCost hsum
          _ = charge (r + 1) * T.card := by rw [hstep]; ring
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (S.card : ℝ) (by norm_num : (1 : ℝ) < 6 / 5)
  have hone : (1 : ℝ) ≤ (6 / 5 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have ht1 : 1 ≤ t r := one_le_mul_of_one_le_of_one_le hb1 hone
  have ht : (S.card : ℝ) ≤ t r ^ 2 := by
    have := mul_le_mul_of_nonneg_right hb1 (le_trans zero_le_one hone)
    change (1 : ℝ) * _ ≤ t r at this
    nlinarith
  obtain ⟨D, hd, blocks, hp, hsz, hcost⟩ := aux r S (Finset.Subset.refl _) ht
  refine ⟨D, hd, blocks, hp, hsz, hcost.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))⟩
  exact (sub_le_self _ (div_nonneg (by positivity) (tpos r).le)).trans hbound

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
