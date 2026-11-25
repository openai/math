import OAI.Computability.NearSquareRoot.InterchangeLabelBudget

/-!
# Recursive calls for the shared sum-of-swaps stage

An endpoint conversion is prepared once per occupied label-rectangle incidence
and input row. Inside a query, each selected matrix row uses its singleton and
its incident destination rectangles; each selected column uses its singleton
and its incident source rectangles. The rectangle sizes themselves do not
multiply the number of paid conversions in a query.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.StageLedger

variable {L B S : Type*} [DecidableEq L] [Fintype B]

/-- Rectangles incident to one specified label on the given side. -/
abbrev Incident (r : B → Rectangle L) (side : Bool) (v : L) :=
  {b : B // v ∈ if side then (r b).destinations else (r b).sources}

/-- Once-per-stage prepared source copies or destination accumulators. -/
abbrev Endpoint (r : B → Rectangle L) (side : Bool) :=
  (v : L) × Incident r side v

/-- A selected matrix index contributes a singleton and one term per incident
rectangle. Row gathering uses the destination side; column distribution uses
the source side. -/
abbrev RankTerm (r : B → Rectangle L) (side : Bool) (sel : S → L) :=
  (s : S) × Option (Incident r side (sel s))

variable [Fintype L] [Fintype S]

theorem card_endpoint (r : B → Rectangle L) (side : Bool) :
    Fintype.card (Endpoint r side) = ∑ v : L, Fintype.card (Incident r side v) :=
  Fintype.card_sigma

omit [Fintype L] in
theorem card_rankTerm (r : B → Rectangle L) (side : Bool) (sel : S → L) :
    Fintype.card (RankTerm r side sel) = ∑ s : S, (Fintype.card (Incident r side (sel s)) + 1) := by
  simp [RankTerm, Fintype.card_sigma, Fintype.card_option]

theorem card_endpoint_le (r : B → Rectangle L) (side : Bool) {inc : ℕ}
    (h : ∀ v, Fintype.card (Incident r side v) ≤ inc) :
    Fintype.card (Endpoint r side) ≤ Fintype.card L * inc := by
  rw [card_endpoint]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun v _ => h v)

omit [Fintype L] in
theorem card_rankTerm_le (r : B → Rectangle L) (side : Bool) (sel : S → L) {inc : ℕ}
    (h : ∀ v, Fintype.card (Incident r side v) ≤ inc) :
    Fintype.card (RankTerm r side sel) ≤ Fintype.card S * (1+inc) := by
  rw [card_rankTerm]
  simpa [Nat.add_comm] using Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => Nat.add_le_add_right (h (sel s)) 1)

variable {Row Query : Type*} [Fintype Row] [Fintype Query]

/-- Sum of the four operation families over their exact occupied indices. -/
def stageCalls (r : B → Rectangle L) (I J : S → L)
    (prepare : Row × Endpoint r false → ℕ) (restore : Row × Endpoint r true → ℕ)
    (gather : Query × Row × RankTerm r true I → ℕ)
    (distribute : Query × Row × RankTerm r false J → ℕ) : ℕ :=
  ((∑ a, prepare a) + ∑ a, restore a) + ((∑ a, gather a) + ∑ a, distribute a)

private theorem sum_price {T : Type*} [Fintype T] (price : T → ℕ) {k : ℕ}
    (h : ∀ a, price a ≤ k) : ∑ a, price a ≤ Fintype.card T * k := by
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => h a)

/-- The prepared reserves are charged only at stage entry/exit. The possibly
different price cap for per-query changes multiplies just the selected rank. -/
theorem stageCalls_le (r : B → Rectangle L) (I J : S → L) {inc K₁ K₂ : ℕ}
    (hinc : ∀ side v, Fintype.card (Incident r side v) ≤ inc)
    (prepare : Row × Endpoint r false → ℕ) (restore : Row × Endpoint r true → ℕ)
    (gather : Query × Row × RankTerm r true I → ℕ)
    (distribute : Query × Row × RankTerm r false J → ℕ)
    (hp : ∀ a, prepare a ≤ K₁) (ht : ∀ a, restore a ≤ K₁)
    (hg : ∀ a, gather a ≤ K₂) (hd : ∀ a, distribute a ≤ K₂) :
    stageCalls r I J prepare restore gather distribute ≤
      2 * Fintype.card Row * Fintype.card L * inc * K₁ +
      2 * Fintype.card Query * Fintype.card Row * Fintype.card S * (1+inc) * K₂ := by
  have h₁ := card_endpoint_le r false (hinc false)
  have h₂ := card_endpoint_le r true (hinc true)
  have h₃ := card_rankTerm_le r true I (hinc true)
  have h₄ := card_rankTerm_le r false J (hinc false)
  have hs := add_le_add (add_le_add (sum_price prepare hp) (sum_price restore ht))
    (add_le_add (sum_price gather hg) (sum_price distribute hd))
  simp only [Fintype.card_prod] at hs
  refine hs.trans ?_
  calc
    _ ≤ (_ * (Fintype.card L * inc) * K₁ + _ * (Fintype.card L * inc) * K₁) +
        (_ * (_ * (Fintype.card S * (1+inc))) * K₂ + _ * (_ * (Fintype.card S * (1+inc))) * K₂) :=
      add_le_add (add_le_add (by gcongr) (by gcongr)) (add_le_add (by gcongr) (by gcongr))
    _ = _ := by ring

/-- Budget in the factored form used by the batch recurrence. -/
theorem stageCalls_le_factored (r : B → Rectangle L) (I J : S → L) {inc K : ℕ}
    (hinc : ∀ side v, Fintype.card (Incident r side v) ≤ inc)
    (prepare : Row × Endpoint r false → ℕ) (restore : Row × Endpoint r true → ℕ)
    (gather : Query × Row × RankTerm r true I → ℕ)
    (distribute : Query × Row × RankTerm r false J → ℕ)
    (hp : ∀ a, prepare a ≤ K) (ht : ∀ a, restore a ≤ K)
    (hg : ∀ a, gather a ≤ K) (hd : ∀ a, distribute a ≤ K) :
    stageCalls r I J prepare restore gather distribute ≤
      2*K*Fintype.card Row*(1+inc)*(Fintype.card L + Fintype.card Query * Fintype.card S) := by
  apply (stageCalls_le r I J hinc prepare restore gather distribute hp ht hg hd).trans
  calc
    _ ≤ 2 * Fintype.card Row * Fintype.card L * (1+inc) * K +
        2 * Fintype.card Query * Fintype.card Row * Fintype.card S * (1+inc) * K := by gcongr; omega
    _ = _ := by ring

/-- The explicit Hamming rectangles meet the ledger's incidence premise with
the same `labelIncidence` used in the analytic batch budget. -/
theorem hamming_incident_le (p k : ℕ) (hp : 0 < p) (side : Bool) (v : Label p (2^k)) :
    Fintype.card (Incident (hammingRectangle (hp := hp)) side v) ≤ labelIncidence p k hp := by
  cases side <;> exact le_labelIncidence p k hp _ v

/-- The four price tables for a single stage, including the selected original
labels. They can vary with the stage. -/
structure Charges (r : B → Rectangle L) (Row Query S : Type*) where
  rows : S → L
  cols : S → L
  prepare : Row × Endpoint r false → ℕ
  restore : Row × Endpoint r true → ℕ
  gather : Query × Row × RankTerm r true rows → ℕ
  distribute : Query × Row × RankTerm r false cols → ℕ

namespace Charges

def count {r : B → Rectangle L} (x : Charges r Row Query S) : ℕ :=
  stageCalls r x.rows x.cols x.prepare x.restore x.gather x.distribute

/-- Cap on the number of recursive calls in each individual layout conversion. -/
def Bounded {r : B → Rectangle L} (x : Charges r Row Query S) (cap : ℕ) : Prop :=
  (∀ a, x.prepare a ≤ cap) ∧ (∀ a, x.restore a ≤ cap) ∧
    (∀ a, x.gather a ≤ cap) ∧ ∀ a, x.distribute a ≤ cap

theorem count_le {r : B → Rectangle L} (x : Charges r Row Query S) {cap inc : ℕ}
    (hb : x.Bounded cap) (hi : ∀ side v, Fintype.card (Incident r side v) ≤ inc) :
    x.count ≤ 2*cap*Fintype.card Row*(1+inc)*(Fintype.card L + Fintype.card Query * Fintype.card S) :=
  stageCalls_le_factored r x.rows x.cols hi _ _ _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

end Charges

open Filter

/-- Sum the calls for the actual charged families over all stages and include
the exceptional-row repair. The label parameter is chosen before the stages
or their finite price tables. -/
theorem eventually_hamming_stageLedger (p : ℕ) [Fact p.Prime] (γ C : ℝ) (K : ℕ)
    (hγ : 1/2 + (3*p-1)/(p : ℝ)^2 < γ) :
    ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      let q := 2^k
      let N := Fintype.card (Label p q)
      let rank := (hammingLabelMatrix p q).rank
      let D := Fintype.card (GramIndex (2*p-1) (Word p q))
      let r := hammingRectangle (p := p) (k := k) (hp := (Fact.out : p.Prime).pos)
      (m : ℝ) ≤ (q : ℝ) ^ (p^2) ∧ (q : ℝ) ≤ 2 * (m : ℝ)^((p^2 : ℕ) : ℝ)⁻¹ ∧
      ∀ stages R defect : ℕ, 0 < R → (stages : ℝ) ≤ C * Real.sqrt (m * (1+Real.log m)) →
        2*m^3*defect ≤ R →
        ∀ alg : Fin stages → Charges r (Fin R) (Fin m) (Fin rank),
          (∀ s, (alg s).Bounded (K*D)) →
          ((∑ s, (alg s).count : ℕ) : ℝ) + 4*(m : ℝ)*defect*N ≤ (R : ℝ)*N*(m : ℝ)^γ := by
  let A : ℝ := max C (2 * K)
  filter_upwards [eventually_hamming_batch_budget p γ A hγ] with m hm
  obtain ⟨k, hlo, hup, hbudget⟩ := hm
  refine ⟨k, hlo, hup, ?_⟩
  intro stages R defect hR hs hd alg hb
  let D := Fintype.card (GramIndex (2*p-1) (Word p (2^k)))
  let inc := labelIncidence p k (Fact.out : p.Prime).pos
  let N := Fintype.card (Label p (2^k))
  let rank := (hammingLabelMatrix p (2^k)).rank
  have hstage (s : Fin stages) :
      (alg s).count ≤ 2*K*R*D*(1+inc)*(N + m*rank) := by
    simpa only [D, inc, N, rank, Fintype.card_fin, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (alg s).count_le (hb s) (hamming_incident_le p k (Fact.out : p.Prime).pos)
  have total : ((∑ s, (alg s).count : ℕ) : ℝ) ≤
      (stages : ℝ) * (2 * (K : ℝ) * R * D * (1+inc) * (N+(m : ℝ)*rank)) := by
    have hn := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hstage s)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hn
    exact_mod_cast hn
  have hs' : (stages : ℝ) ≤ A * Real.sqrt (m * (1+Real.log m)) :=
    hs.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.sqrt_nonneg _))
  refine (add_le_add total (le_refl (4*(m : ℝ)*defect*N))).trans ?_
  refine le_trans ?_ (hbudget stages R defect hR hs' hd)
  change (stages : ℝ) * (2 * (K : ℝ) * R * D * (1+inc) * (N+(m : ℝ)*rank)) + _ ≤
    (stages : ℝ) * (A * R * D * (1+inc) * (N+(m : ℝ)*rank)) + _
  gcongr
  exact le_max_right ..

end Interchange.StageLedger

end NearSquareRoot
end Computability
end OAI
