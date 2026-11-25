import OAI.Computability.NearSquareRoot.InterchangeStageRoute
import OAI.Computability.NearSquareRoot.InterchangeStageScript

/-!
# Recursive-call counts for the concrete shared stage

The endpoint moves occur once per occupied incidence. Only the rank-sized
gather and distribution depend on the query. All unchanged backing registers
and the query-dependent triangular endpoint maps have zero recursive price.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.StageRoute

open StageLedger

variable {L B H Q : Type} [DecidableEq L] [Fintype L] [Fintype B] [Fintype H] [Fintype Q]
    {r : B → Rectangle L} {I J : H → L}

/-- Convert physical address-move prices to the four actual paid collections
per stage, retaining multiplicity for every scalar payload row. -/
def moveCharges (Row : Type) (price : Move r Q I J → ℕ) : Charges r Row Q H where
  rows := I
  cols := J
  prepare a := price (.prepare a.2)
  restore a := price (.restore a.2)
  gather a := price (.gather a.1 a.2.2)
  distribute a := price (.distribute a.1 a.2.2)

omit [DecidableEq L] [Fintype L] [Fintype B] [Fintype H] in
private theorem repeat_query (Row : Type) [Fintype Row] {T : Type} [Fintype T]
    (f : Q × T → ℕ) :
    (∑ a : Q × Row × T, f (a.1,a.2.2)) = Fintype.card Row * ∑ a, f a := by
  rw [Fintype.sum_prod_type (fun a : Q × Row × T => f (a.1,a.2.2)), Fintype.sum_prod_type f,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.sum_prod_type (fun a : Row × T => f (q,a.2))]
  simp

theorem moveCharges_count (Row : Type) [Fintype Row] (price : Move r Q I J → ℕ) :
    (moveCharges Row price).count = Fintype.card Row *
      (((∑ e, price (.prepare e)) + ∑ e, price (.restore e)) +
      ((∑ t : Q × RankTerm r true I, price (.gather t.1 t.2)) +
       ∑ t : Q × RankTerm r false J, price (.distribute t.1 t.2))) := by
  change ((∑ a : Row × Endpoint r false, price (.prepare a.2)) +
      ∑ a : Row × Endpoint r true, price (.restore a.2)) +
      ((∑ a : Q × Row × RankTerm r true I, price (.gather a.1 a.2.2)) +
      ∑ a : Q × Row × RankTerm r false J, price (.distribute a.1 a.2.2)) = _
  rw [repeat_query Row (fun a : Q × RankTerm r true I => price (.gather a.1 a.2)),
    repeat_query Row (fun a : Q × RankTerm r false J => price (.distribute a.1 a.2))]
  simp [Fintype.sum_prod_type, Nat.mul_add]

omit [DecidableEq L] [Fintype L] [Fintype B] [Fintype H] [Fintype Q] in
theorem moveCharges_bounded (Row : Type) (price : Move r Q I J → ℕ) {K : ℕ}
    (hp : ∀ e, price (.prepare e) ≤ K) (ht : ∀ e, price (.restore e) ≤ K)
    (hg : ∀ j t, price (.gather j t) ≤ K) (hd : ∀ j t, price (.distribute j t) ≤ K) :
    (moveCharges Row price).Bounded K :=
  ⟨fun a => hp a.2, fun a => ht a.2, fun a => hg a.1 a.2.2, fun a => hd a.1 a.2.2⟩

variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]

/-- Exact price of executing the literal stage on each of the scalar rows.
The only free-move assumptions concern the identity and the two triangular
endpoint maps; the other four prices are the supplied layout prices. -/
theorem scalar_stage_cost (Row : Type) [Fintype Row] (M : Matrix H H K)
    (A₀ : E →+ E) (A : Q → E →+ E) (quote : Move r Q I J → ℕ)
    (hi : quote .idle = 0) (ha : ∀ j e, quote (.align j e) = 0)
    (hu : ∀ j e, quote (.unalign j e) = 0) :
    Fintype.card Row * StageScript.cost quote (stage r I J M A₀ A) = (moveCharges Row quote).count := by
  let pre e := quote (.prepare e)
  let post e := quote (.restore e)
  let g (t : Q × RankTerm r true I) := quote (.gather t.1 t.2)
  let d (t : Q × RankTerm r false J) := quote (.distribute t.1 t.2)
  have heq : quote = price r I J pre post g d := by
    funext x
    cases x <;> first | rfl | exact hi | apply ha | apply hu
  calc
    _ = Fintype.card Row * StageScript.cost (price r I J pre post g d) (stage r I J M A₀ A) :=
      congrArg (fun f => Fintype.card Row * StageScript.cost f (stage r I J M A₀ A)) heq
    _ = _ := by rw [stage_cost, moveCharges_count]

/-- The actual bank script fits the stage estimate used in the recursion. -/
theorem scalar_stage_cost_le (Row : Type) [Fintype Row] (M : Matrix H H K)
    (A₀ : E →+ E) (A : Q → E →+ E) (quote : Move r Q I J → ℕ)
    (hi : quote .idle = 0) (ha : ∀ j e, quote (.align j e) = 0)
    (hu : ∀ j e, quote (.unalign j e) = 0) {cap inc : ℕ}
    (hp : ∀ e, quote (.prepare e) ≤ cap) (ht : ∀ e, quote (.restore e) ≤ cap)
    (hg : ∀ j t, quote (.gather j t) ≤ cap) (hd : ∀ j t, quote (.distribute j t) ≤ cap)
    (hinc : ∀ side v, Fintype.card (Incident r side v) ≤ inc) :
    Fintype.card Row * StageScript.cost quote (stage r I J M A₀ A) ≤
      2*cap*Fintype.card Row*(1+inc)*(Fintype.card L+Fintype.card Q*Fintype.card H) := by
  rw [scalar_stage_cost Row M A₀ A quote hi ha hu]
  exact (moveCharges Row quote).count_le (moveCharges_bounded Row quote hp ht hg hd) hinc

open Filter

/-- Combine the actual scalar-row prices of all finite stage scripts with the
full-row spectral repair. The large-`m` choice of label radix is uniform over
the price tables, stage operators, and input rows. -/
theorem eventually_hamming_script_cost (p : ℕ) [Fact p.Prime] (E : Type)
    [AddCommGroup E] [Module (ZMod p) E] (γ C : ℝ) (unitCost : ℕ)
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
        ∀ (I J : Fin rank → Label p q) (M : Matrix (Fin rank) (Fin rank) (ZMod p))
          (A₀ : Fin stages → (Fin R → E) →+ (Fin R → E))
          (A : Fin stages → Fin m → (Fin R → E) →+ (Fin R → E))
          (quote : Fin stages → Move r (Fin m) I J → ℕ),
          (∀ s, quote s .idle = 0) →
          (∀ s j e, quote s (.align j e) = 0) →
          (∀ s j e, quote s (.unalign j e) = 0) →
          (∀ s e, quote s (.prepare e) ≤ unitCost*D) →
          (∀ s e, quote s (.restore e) ≤ unitCost*D) →
          (∀ s j t, quote s (.gather j t) ≤ unitCost*D) →
          (∀ s j t, quote s (.distribute j t) ≤ unitCost*D) →
          ((∑ s, R * StageScript.cost (quote s) (stage r I J M (A₀ s) (A s)) : ℕ) : ℝ) +
            4*(m : ℝ)*defect*N ≤ (R : ℝ)*N*(m : ℝ)^γ := by
  filter_upwards [eventually_hamming_stageLedger p γ C unitCost hγ] with m hm
  obtain ⟨k,hlo,hup,hcost⟩ := hm
  refine ⟨k,hlo,hup,?_⟩
  intro stages R defect hR hst hdf I J M A₀ A quote hi ha hu hp ht hg hd
  have heq (s : Fin stages) := scalar_stage_cost (Fin R) M (A₀ s) (A s) (quote s)
    (hi s) (ha s) (hu s)
  simp only [Fintype.card_fin] at heq
  simp_rw [heq]
  exact hcost stages R defect hR hst hdf (fun s => moveCharges (Fin R) (quote s)) fun s =>
    moveCharges_bounded (Fin R) (quote s) (hp s) (ht s) (hg s) (hd s)

end Interchange.StageRoute

end NearSquareRoot
end Computability
end OAI
