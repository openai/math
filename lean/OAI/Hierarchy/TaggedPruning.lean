import OAI.Hierarchy.TaggedPruneOpen
import OAI.Hierarchy.TaggedPruneBudget
import OAI.Hierarchy.ProbePlacedTerm
import OAI.Hierarchy.CorrectionFrame
import OAI.Hierarchy.CorrectionProducts
import OAI.Hierarchy.GridSum

namespace OAI
/-! # Pruning exposed tagged routing identities

The same physical catalyst and tagged data ports are used for every selector
and every permutation. A product of local tag indicators restricts each term
to its permutation's tag assignment. Pruning then discards an ordinary sum on
this common output format.
-/

noncomputable section
namespace Hierarchy.TaggedPrune

open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open AdaptiveProbe Catalyst Tagged CorrectionFrame
open Computability.VPVNP.RAMSerialization (wordBits)
open scoped Classical BigOperators

variable {F : Type*} [Field F] {h w k : ℕ} {b : Fin k → ℕ}

/-- Fixed protocol layer assignment, with each open physical bit attached to its site. -/
structure Layout (h w : ℕ) {k : ℕ} (b : Fin k → ℕ) where
  last : ℕ
  layer : Fin (last+1) → Location k
  port : OpenPins h w b → Fin (last+1)
  located : ∀ i, layer (port i) = location i

/-- Declared communication links of an individual selector. Distances use the
unit catalyst frame, so multiplying by M recovers the unscaled layer distance. -/
structure Links (D : Layout h w b) (M : ℕ) where
  number : ℕ
  ends : Fin number → Chord (D.last+1)
  bits : Fin number → ℕ
  len : Fin number → ℝ
  scale : Fin number → ℝ
  len_nonneg : ∀ i, 0 ≤ len i
  scale_nonneg : ∀ i, 0 ≤ scale i
  different_zero : ∀ i, D.layer (ends i).1.1 ≠ D.layer (ends i).1.2 → scale i = 0
  distance : ∀ i, D.layer (ends i).1.1 ≠ D.layer (ends i).1.2 →
    (M:ℝ)*dist (point (D.layer (ends i).1.1)) (point (D.layer (ends i).1.2)) ≤ len i

namespace Links
variable {D : Layout h w b} {M : ℕ} (L : Links D M)

def cross := Finset.univ.filter fun i => D.layer (L.ends i).1.1 ≠ D.layer (L.ends i).1.2
def widthRatio (i : Fin L.number) : ℝ := (L.bits i:ℝ)/w
def charge : ℝ := ∑ i ∈ L.cross, L.len i * L.widthRatio i
def Keep (n : ℕ) : Prop := 2*(M:ℝ)*(∑ j, (b j:ℝ))/w-n ≤ L.charge

/-- A common denominator for the fixed nonnegative rational link charges
turns the pruning test into one integer multiply-add per cross-layer link
and one final comparison. -/
theorem keep_iff_integer {n den : ℕ} (hw : 0<w) (hd : 0<den)
    (weight : Fin L.number → ℕ)
    (rational : ∀ i, L.len i = (weight i:ℝ)/den) :
    L.Keep n ↔ 2*M*(∑ j, b j)*den ≤
      (∑ i ∈ L.cross, weight i*L.bits i) + n*w*den := by
  have hw' : 0<(w:ℝ) := Nat.cast_pos.mpr hw
  have hd' : 0<(den:ℝ) := Nat.cast_pos.mpr hd
  have total : L.charge*((w:ℝ)*den) = ((∑ i ∈ L.cross, weight i*L.bits i:ℕ):ℝ) := by
    simp only [charge,widthRatio,Finset.sum_mul,Nat.cast_sum,Nat.cast_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [rational i]
    field_simp
  unfold Keep
  rw [←mul_le_mul_iff_left₀ (mul_pos hw' hd'),total]
  have convertBound : (2*(M:ℝ)*(∑ j, (b j:ℝ))/w-n)*(w*den) =
      2*M*(∑ j, (b j:ℝ))*den-n*w*den := by field_simp
  rw [convertBound,sub_le_iff_le_add]
  exact_mod_cast Iff.rfl

theorem retained_budget {p q Q Λ : ℝ} {n : ℕ} (hΛ : 0 ≤ Λ)
    (budget : TermBudget p q Q Λ n w M (∑ j, b j) L.scale L.len L.widthRatio)
    (kept : L.Keep n) :
    (∑ i ∈ Finset.univ.filter (fun i => 0 < L.scale i),
      (L.len i * L.widthRatio i + Λ*capacity p q Q (L.scale i) (L.len i))) ≤ 11*(n:ℝ) := by
  apply positive_budget (cross:=L.cross) hΛ L.scale_nonneg L.len_nonneg
    (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun i hi => L.different_zero i (Finset.mem_filter.mp hi).2) budget
  simpa [widthRatio,Keep,charge,Nat.cast_sum] using kept

theorem discarded {n : ℕ} (hM : 0<M) (hw : 0<w) (perm : Equiv.Perm (Row h))
    (f : Table F h w b) (rejected : ¬ L.Keep n)
    (localTables : ((CorrectionProducts.raw f).group D.port).Restricts
      (ChordGraph.raw F (installedWidths L.ends L.bits)))
    (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k))) :
    P.price (CorrectionProducts.raw (exposed perm f)) (sites b) <
      2*(∑ j, (b j : ℝ)) - (n:ℝ)*w/M := by
  let site := point ∘ D.layer
  have loc : sites (p:=pins h w) b = site ∘ D.port := by
    rw [sites_eq]
    funext i
    exact congrArg point (D.located i).symm
  have placed := placed_term_le P site L.ends L.bits _
    (exposed_restricts D.port perm f localTables)
  rw [loc, P.group]
  apply placed.trans_lt
  have hmr : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  have hwr : 0<(w:ℝ) := Nat.cast_pos.mpr hw
  have reject : L.charge < 2*(M:ℝ)*(↑(∑ j, b j) : ℝ)/w-n := by
    simpa only [Keep,not_le,Nat.cast_sum] using rejected
  have total : (∑ i, (L.bits i:ℝ)*dist (site (L.ends i).1.1) (site (L.ends i).1.2)) ≤
      (w:ℝ)/M*L.charge := by
    unfold charge cross
    rw [Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases ne : D.layer (L.ends i).1.1 ≠ D.layer (L.ends i).1.2
    · rw [ite_eq_left ne]
      have le : dist (site (L.ends i).1.1) (site (L.ends i).1.2) ≤ L.len i/M :=
        (le_div_iff₀ hmr).2 (by simpa only [site,Function.comp_apply,mul_comm] using L.distance i ne)
      apply (mul_le_mul_of_nonneg_left le (Nat.cast_nonneg (L.bits i))).trans_eq
      dsimp only [widthRatio]
      field_simp

    · have eqn := not_not.mp ne
      simp [site,eqn]
  simpa only [Nat.cast_sum] using discarded_price (Nc:=∑ j, b j) hw hM total reject

end Links

/-- The finite network may use any implementation of the retained contraction.
Its approximation gap is measured on all exposed tag, payload, and catalyst pins. -/
theorem pruning_gap {M B : ℕ} (hM : 0<M) (hw : 0<w) (hk : 0<k)
    (X : Approximation F k (pins h w)) (D : Layout h w X.width)
    {count : Equiv.Perm (Row h) → ℕ} (enc : ∀ perm, count perm ≤ 2^B)
    (route : Index count → Table F h w X.width) (links : Index count → Links D M)
    (routing : ∀ perm, (∑ i : Fin (count perm), route ⟨perm,i⟩) = perTag perm)
    (tables : ∀ a, ((CorrectionProducts.raw (route a)).group D.port).Restricts
      (ChordGraph.raw F (installedWidths (links a).ends (links a).bits)))
    (realized : X.coeff = ∑ a : {a // (links a).Keep (2^h)}, exposed a.val.1 (route a.val)) :
    X.Gap (coeff F h w) ((2:ℝ)^h*w/M - 2*(k:ℝ)*((h:ℝ)*2^h+B)) := by
  let : NeZero k := ⟨hk.ne'⟩
  let keep (a : Index count) := (links a).Keep (2^h)
  let term (a : Index count) := exposed a.1 (route a)
  let lost (a : {a // ¬keep a}) := term a.val
  let omitted := ∑ a, lost a
  have split := Fintype.sum_subtype_add_sum_subtype keep term
  have err : (X.error (coeff F h w)).coeff = -omitted := by
    change X.coeff - ideal X.width (coeff F h w) = -omitted
    rw [realized, ←exposed_sum route routing]
    change (∑ a : {a // keep a}, term a.val) - ∑ a, term a = -omitted
    rw [←split]
    abel
  intro P
  by_cases nz : omitted = 0
  · left
    rw [err,nz,neg_zero]
    rfl
  right
  let y := frame k
  let σ := location (p:=pins h w) (b:=X.width)
  let c := P.price (Raw.diagonal (Location k) F (Fin 2)) y
  obtain ⟨φ,hc,prices⟩ := P.normalized_group y
  have signed : P.price (X.error (coeff F h w)) (sites X.width) =
      P.price (CorrectionProducts.raw omitted) (y ∘ σ) := by
    change P.price (CorrectionProducts.raw ((X.error (coeff F h w)).coeff)) _ = _
    rw [sites_eq,err,prices σ (CorrectionProducts.raw (-omitted)) (neg_ne_zero.mpr nz),
      prices σ (CorrectionProducts.raw omitted) nz]
    change c*Real.logb 2 (CorrectionProducts.value φ σ (-omitted)) =
      c*Real.logb 2 (CorrectionProducts.value φ σ omitted)
    rw [CorrectionProducts.value_neg]
  rw [signed]
  obtain ⟨a,ha,sumPrice⟩ := GridSum.price_sum (A:=fun _ => Bool) P y σ lost nz
  apply sumPrice.trans
  have discarded := (links a.val).discarded (n:=2^h) hM hw a.val.1 (route a.val)
    a.property (tables a.val) P
  rw [sites_eq] at discarded
  have logbound := discarded_entropy count enc keep
  have cost : c*Real.logb 2 (Fintype.card {a // ¬keep a}) ≤ 2*(k:ℝ)*((h:ℝ)*2^h+B) := calc
    _ ≤ c*((h:ℝ)*2^h+B) := mul_le_mul_of_nonneg_left logbound hc.le
    _ ≤ _ := mul_le_mul_of_nonneg_right (CorrectionFrame.scale_le P) (by positivity)
  change P.price (CorrectionProducts.raw (lost a)) (y ∘ σ) +
    c*Real.logb 2 (Fintype.card {a // ¬keep a}) ≤ _
  change P.price (CorrectionProducts.raw (lost a)) (y ∘ σ) <
      2*(∑ j, (X.width j:ℝ))-((2^h:ℕ):ℝ)*w/M at discarded
  push_cast at discarded
  linarith


end Hierarchy.TaggedPrune

end
end OAI
