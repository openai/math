import OAI.Computability.VPVNP.LiveCutAssignments
import OAI.Computability.VPVNP.LiveEvaluatorTail

/-! # Contracting the evaluation mode of the live chain

For a fixed first-half cut assignment, each pair reads the exterior bits at
its two adjacent cuts and checks its outgoing counters. Each tail group then
reads two adjacent configuration fields and checks one transition. Summing
the products of these local counts eliminates the forced counter fields and
configuration strings, leaving the actual evaluator path multiplicity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open CutSchedule ExponentTrace LiveChain UniversalMachine LiveEvaluatorEncoding
open scoped Classical

variable {h Δ t Z M w : ℕ}

private def outgoing (fit : 1 + t * Z ≤ Δ) (fst : LiveBits h Δ) (i : Fin (2^h)) :=
  firstHalfLayout h Δ (i.val+1) t Z (by omega) i.isLt fit (fst i)

/-- Exterior primed bits are read from the first-half cuts. The initial cut
has width zero. -/
def exteriorOf (fit : 1 + t * Z ≤ Δ) (fst : LiveBits h Δ) : Exterior h Δ :=
  Fin.cons (fun _ => false) (fun i => (outgoing fit fst i).2.1)

private theorem exterior_eq {fit : 1 + t * Z ≤ Δ} {fst : LiveBits h Δ} {ξ : Exterior h Δ}
    (same : ∀ i, (outgoing fit fst i).2.1 = ξ i.succ) : exteriorOf fit fst = ξ := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · funext k
    exact Fin.elim0 (k.cast (by simp))
  · exact same i

/-- One pair checks the canonical outgoing fields and the increment over
its incoming counters. Both sides of each counter comparison are natural
numbers, so overflow cannot create additional paths. -/
def firstCheck (fit : 1 + t * Z ≤ Δ) (fst : LiveBits h Δ) (ξ : Exterior h Δ)
    (i : Fin (2^h)) (inc : Fin t → ℕ) : Prop :=
  outgoing fit fst i = (true, ξ i.succ, counters fit fst i.succ, fun _ => false) ∧
    ∀ a, (counters fit fst i.succ a).val = (counters fit fst i.castSucc a).val + inc a

private theorem allFirstChecks (fit : 1 + t * Z ≤ Δ) (fst : LiveBits h Δ) (ξ : Exterior h Δ)
    (inc : Fin (2^h) → Fin t → ℕ) :
    (∀ i, firstCheck fit fst ξ i (inc i)) ↔ ExponentTrace.Valid fit ξ inc fst := by
  exact forall_and

private theorem exteriorOf_valid (fit : 1 + t * Z ≤ Δ) (fst : LiveBits h Δ) (ξ : Exterior h Δ)
    (inc : Fin (2^h) → Fin t → ℕ) (ok : ExponentTrace.Valid fit ξ inc fst) : exteriorOf fit fst = ξ :=
  exterior_eq fun i => congrArg (fun a => a.2.1) (ok.1 i)

variable {Nom : Type*} [Fintype Nom]
variable {Path : Exterior h Δ → Fin (2^h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]

/-- The local count of evaluation-mode paths through a first-half group. -/
noncomputable def pairCount (fit : 1 + t * Z ≤ Δ)
    (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ) (fst : LiveBits h Δ) (i : Fin (2^h)) : ℕ :=
  let ξ := exteriorOf fit fst
  ∑ μ, ∑ q : Path ξ i μ, if firstCheck fit fst ξ i (inc ξ i μ q) then 1 else 0

/-- Number of branch bits yielding exactly the two specified adjacent tail
states. Distinct choices count separately even at coincident successors. -/
noncomputable def tailCount (p : Program) (layout : LiveEvaluatorTail.Layout p.extra M w Δ)
    (init : Code p.extra M) (lst : TailBits h Δ) (i : Fin (2^h)) : ℕ :=
  ∑ bit : Bool, if ∃ a b, LiveEvaluatorTail.boundary layout init lst i.castSucc = some a ∧
      LiveEvaluatorTail.boundary layout init lst i.succ = some b ∧
      LiveEvaluatorStep.nextCode p a bit = some b ∧ b ≠ .rejected then 1 else 0

private theorem tailProduct (p : Program) (layout : LiveEvaluatorTail.Layout p.extra M w Δ)
    (init : Code p.extra M) :
    (∑ lst : TailBits h Δ, ∏ i : Fin (2^h), tailCount p layout init lst i) =
      Nat.card (LiveEvaluatorTail.Runs (h := h) layout init) := by
  unfold tailCount LiveEvaluatorTail.Runs
  simp_rw [Fintype.prod_sum, Fintype.prod_ite_zero, Finset.prod_const_one]
  rw [Finset.sum_comm, Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro choices _
  simp only [Finset.sum_boole, LiveEvaluatorTail.Valid]
  symm
  convert! Fintype.card_subtype (LiveEvaluatorTail.Valid layout init choices) using 1
  apply congrArg Finset.card
  ext b
  simp [LiveEvaluatorTail.Valid]

private theorem pairProduct (fit : 1 + t * Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (fst : LiveBits h Δ) :
    (∏ i, pairCount fit inc fst i) = ∑ ξ : Exterior h Δ, ∑ μ : Fin (2^h) → Nom,
      ∑ q : (i : Fin (2^h)) → Path ξ i (μ i),
      if ExponentTrace.Valid fit ξ (fun i => inc ξ i (μ i) (q i)) fst then 1 else 0 := by
  rw [Finset.sum_eq_single (exteriorOf fit fst)]
  · unfold pairCount
    dsimp only
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro μ _
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [Fintype.prod_ite_zero, Finset.prod_const_one, allFirstChecks]
  · intro ξ _ hne
    apply Finset.sum_eq_zero
    intro μ _
    apply Finset.sum_eq_zero
    intro q _
    exact ite_eq_right (fun ok => hne (exteriorOf_valid fit fst ξ _ ok).symm)
  · simp

/-- The evaluation mode contracts to the sum over exterior assignments,
nomination vectors and local pair paths, followed by a single evaluator on
the componentwise sum of their increments. -/
theorem evaluation_contraction (fit : 1 + t * Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (bound : ∀ ξ (μ : Fin (2^h) → Nom) (q : (i : Fin (2^h)) → Path ξ i (μ i)) (i : Fin (2^h)) a,
      partialSum (fun j => inc ξ j (μ j) (q j)) i.succ a < 2^Z)
    (p : Program) (layout : LiveEvaluatorTail.Layout p.extra M w Δ)
    (initial : (Fin t → ℕ) → Config p.extra) (init : (Fin t → ℕ) → Code p.extra M)
    (hi : ∀ e, (init e).toState = EvaluatorTail.canonical (initial e))
    (space : ∀ e, LiveEvaluatorTail.HistoriesFit p M (2^h) (initial e)) :
    (∑ fst : LiveBits h Δ, ∑ lst : TailBits h Δ, (∏ i, pairCount fit inc fst i) *
      ∏ i, tailCount p layout (init (fun a => (counters fit fst (Fin.last _) a).val)) lst i) =
    ∑ ξ : Exterior h Δ, ∑ μ : Fin (2^h) → Nom, ∑ q : (i : Fin (2^h)) → Path ξ i (μ i),
      paths p (2^h) (initial (fun a => ∑ i, inc ξ i (μ i) (q i) a)) := by
  let endCounts (fst : LiveBits h Δ) (a : Fin t) := (counters fit fst (Fin.last _) a).val
  have tail (fst : LiveBits h Δ) : (∑ lst : TailBits h Δ, ∏ i : Fin (2^h),
      tailCount p layout (init (endCounts fst)) lst i) = paths p (2^h) (initial (endCounts fst)) :=
    (tailProduct p layout _).trans (LiveEvaluatorTail.card_runs layout _ _ (hi _) (space _))
  change (∑ fst, ∑ lst, (∏ i, pairCount fit inc fst i) * ∏ i, tailCount p layout (init (endCounts fst)) lst i) = _
  simp_rw [← Finset.mul_sum, tail, pairProduct, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  obtain ⟨fst, ok, uniq⟩ := existsUnique_live fit ξ (fun i => inc ξ i (μ i) (q i)) (bound ξ μ q)
  rw [Finset.sum_eq_single fst, ite_eq_left ok]
  · congr 2
    exact funext (middle_counters fit ξ _ fst ok)
  · exact fun other _ hne => ite_eq_right fun ho => hne (uniq _ ho)
  · simp

/-- A successful first-half group sets the literal first bit of its outgoing cut. -/
theorem pairCount_mode (fit : 1 + t * Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (fst : LiveBits h Δ) (i : Fin (2^h)) (ok : pairCount fit inc fst i ≠ 0) :
    distributedBit (fst i) 0 = true := by
  have hw : 0 < width (h+1) Δ (i.val+1) := by rw [width_double h Δ _ (by omega) i.isLt]; omega
  have raw : (outgoing fit fst i).1 = fst i ⟨0, hw⟩ := rfl
  simp only [distributedBit, hw, ↓reduceDIte, ← raw]
  by_contra no
  apply ok
  unfold pairCount
  apply Finset.sum_eq_zero
  intro μ _
  apply Finset.sum_eq_zero
  intro q _
  exact ite_eq_right fun hv => no (congrArg Prod.fst hv.1)

/-- A successful tail group with an outgoing cut sets its literal first bit. -/
theorem tailCount_mode (p : Program) (layout : LiveEvaluatorTail.Layout p.extra M w Δ)
    (init : Code p.extra M) (lst : TailBits h Δ) (j : Fin (2^h-1))
    (ok : tailCount p layout init lst ⟨j.val, by have := j.isLt; omega⟩ ≠ 0) :
    distributedBit (lst j) 0 = true := by
  let i : Fin (2^h) := ⟨j.val, by have := j.isLt; omega⟩
  have hj : j.val+1 ≠ 2^h := by have := j.isLt; omega
  have hb : LiveEvaluatorTail.boundary layout init lst i.succ = LiveEvaluatorTail.readCut layout j (lst j) := by
    simp [LiveEvaluatorTail.boundary, i, hj]
  have hlt : 2^h+(j.val+1) < 2^(h+1) := by rw [pow_succ]; have := j.isLt; omega
  have hw : 0 < width (h+1) Δ (2^h+(j.val+1)) := by rw [width_tail h Δ _ (by omega) hlt]; have := layout.cutWidth; omega
  by_contra no
  apply ok
  unfold tailCount
  apply Finset.sum_eq_zero
  intro bit _
  apply ite_eq_right
  rintro ⟨a,b,_,hout,_,_⟩
  change LiveEvaluatorTail.boundary layout init lst i.succ = some b at hout
  rw [hb, LiveEvaluatorTail.readCut_iff] at hout
  apply no
  rw [hout]
  let e := tailLayout h Δ (2^h+(j.val+1)) (fieldWords M*w) (by omega) hlt layout.cutWidth
  have raw (bits : Bits (width (h+1) Δ (2^h+(j.val+1)))) : (e bits).1 = distributedBit bits 0 := by
    simp only [distributedBit, hw, ↓reduceDIte]; rfl
  rw [← raw]
  exact congrArg Prod.fst (e.apply_symm_apply _)

/-- The two contiguous halves, in order of their physical group indices. -/
def halves (h : ℕ) : Fin (2^h) ⊕ Fin (2^h) ≃ Fin (2^(h+1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ]; omega))

/-- Product and sum reindexing for a per-group evaluation-mode count on raw cuts. -/
theorem contract_halves (ev : AllCuts h Δ → Fin (2^(h+1)) → ℕ)
    (f : LiveBits h Δ → Fin (2^h) → ℕ) (g : LiveBits h Δ → TailBits h Δ → Fin (2^h) → ℕ)
    (left : ∀ c i, ev c (halves h (.inl i)) = f (liveCutEquiv h Δ c).1 i)
    (right : ∀ c i, ev c (halves h (.inr i)) = g (liveCutEquiv h Δ c).1 (liveCutEquiv h Δ c).2 i) :
    (∑ c : AllCuts h Δ, ∏ j, ev c j) = ∑ fst, ∑ lst, (∏ i, f fst i) * ∏ i, g fst lst i := by
  rw [← (liveCutEquiv h Δ).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro fst _
  apply Finset.sum_congr rfl
  intro lst _
  rw [← (halves h).prod_comp, Fintype.prod_sum_type]
  simp only [left, right, Equiv.apply_symm_apply]

end ChainAssignments

end VPVNP
end Computability
end OAI
