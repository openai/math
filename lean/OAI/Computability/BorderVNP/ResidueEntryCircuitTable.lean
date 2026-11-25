import OAI.Computability.BorderVNP.BranchSliceTable
import OAI.Computability.BorderVNP.ModelHomogenizeGate
import OAI.Computability.VPVNP.CircuitSize

/-! # Circuits for a weighted homogeneous parse table

The query in §9 evaluates the universal table on a fixed vector of field
scalars. Its production weights are the original parameter variables.
The circuit keeps every degree/state entry for subsequent layers, so
fan-out never duplicates a lower-degree computation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open VPVNP Homogenize MvPolynomial
open scoped Classical

variable {K τ : Type*} [CommRing K] {k h n : ℕ}

private theorem append_triples {m : ℕ} {ι : Type*} (p : Program K τ m) (s : Finset ι)
    (a b c : ι → MvPolynomial τ K) (ha : ∀ i ∈ s, HasWire p (a i))
    (hb : ∀ i ∈ s, HasWire p (b i)) (hc : ∀ i ∈ s, HasWire p (c i)) :
    ∃ l ≤ m+3*s.card, ∃ r : Program K τ l, Preserves p r ∧
      HasWire r (∑ i ∈ s, a i*b i*c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨m, by simp, p, fun _ x => x, by simpa using hasWire_const p (0 : K)⟩
  | insert i s hi ih =>
    obtain ⟨l, hl, r, hr, hs⟩ := ih (fun j hj => ha j (by simp [hj]))
      (fun j hj => hb j (by simp [hj])) (fun j hj => hc j (by simp [hj]))
    obtain ⟨u, hu, hab⟩ := append_binary r .mul (hr _ (ha i (by simp))) (hr _ (hb i (by simp)))
    obtain ⟨v, hv, habc⟩ := append_binary u .mul hab (hu _ (hr _ (hc i (by simp))))
    obtain ⟨z, hz, hsum⟩ := append_binary v .add habc (hv _ (hu _ hs))
    refine ⟨l+1+1+1, ?_, z, fun f hf => hz f (hv f (hu f (hr f hf))), ?_⟩
    · rw [Finset.card_insert_of_notMem hi, Nat.mul_succ]
      omega
    · simpa [Finset.sum_insert hi, BinOp.apply] using hsum

/-- Scalar cost of building the shared table, uniformly in the grammar weights and
in the field elements substituted for the original polynomial's variables. -/
def tableGateBudget (k h n : ℕ) := n*h*(2*k+3*(n*h*h))

/-- A joint circuit produces every weighted state at every degree, starting with
already available terminals, production weights and variable substitutions. -/
theorem weightedTable_wires {m : ℕ} (p : Program K τ m)
    (G : ParseGrammar (MvPolynomial τ K) (Fin k) (Fin h) n) (z : Fin k → MvPolynomial τ K)
    (hter : ∀ s i, HasWire p (G.terminal s i))
    (hbin : ∀ d s j u v, HasWire p (G.binary d s j u v)) (hz : ∀ i, HasWire p (z i)) :
    ∃ l ≤ m+tableGateBudget k h n, ∃ r : Program K τ l, Preserves p r ∧
      ∀ d s, HasWire r (eval z (G.eval d s)) := by
  let B := 2*k+3*(n*h*h)
  let value := fun d s => eval z (G.eval d s)
  have layers (v : ℕ) (hv : v ≤ n) : ∃ l ≤ m+v*h*B, ∃ r : Program K τ l, Preserves p r ∧
      ∀ (d : Fin n), d.val < v → ∀ s, HasWire r (value d s) := by
    induction v with
    | zero => exact ⟨m, by simp, p, fun _ hf => hf, fun _ hlt => (Nat.not_lt_zero _ hlt).elim⟩
    | succ v ih =>
      obtain ⟨l,hl,r,hr,hprev⟩ := ih (by omega)
      let d : Fin n := ⟨v,hv⟩
      let states (j : ℕ) : MvPolynomial τ K := if hj : j < h then value d ⟨j,hj⟩ else 0
      have one {t : ℕ} (u : Program K τ t) (hu : Preserves r u) (i : Fin h) :
          ∃ l' ≤ t+B, ∃ u' : Program K τ l', Preserves u u' ∧ HasWire u' (value d i) := by
        by_cases hd : d.val = 0
        · obtain ⟨l',hh,u',hu',hs⟩ := append_sum_products u Finset.univ (G.terminal i) z
            (fun j _ => hu _ (hr _ (hter i j))) (fun j _ => hu _ (hr _ (hz j)))
          refine ⟨l', ?_, u', hu', ?_⟩
          · simp only [Finset.card_univ, Fintype.card_fin] at hh
            dsimp [B]
            omega
          · simpa only [value, G.eval_terminal hd, map_sum, map_mul, eval_C, eval_X] using hs
        · let I := Fin d.val × Fin h × Fin h
          obtain ⟨l',hh,u',hu',hs⟩ := append_triples u (Finset.univ : Finset I)
            (fun (j,a,b) => G.binary d i j a b)
            (fun (j,a,_) => value (ParseGrammar.leftDegree d j) a)
            (fun (j,_,b) => value (ParseGrammar.rightDegree d j) b)
            (fun (j,a,b) _ => hu _ (hr _ (hbin d i j a b)))
            (fun (j,a,_) _ => hu _ (hprev _ (ParseGrammar.leftDegree_lt d j) a))
            (fun (j,_,b) _ => hu _ (hprev _ (ParseGrammar.rightDegree_lt d j) b))
          refine ⟨l', ?_, u', hu', ?_⟩
          · simp only [I, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hh
            dsimp [B]
            have hle : d.val*(h*h) ≤ n*h*h := by rw [Nat.mul_assoc]; gcongr; exact d.isLt.le
            omega
          · simpa only [I, value, G.eval_binary hd, map_sum, map_mul, eval_C,
              Fintype.sum_prod_type] using hs
      obtain ⟨t, ht, u, hu, hs⟩ := extend_fin r h B states (by
        intro t u hu j hj
        simpa [states, hj] using one u hu ⟨j,hj⟩)
      refine ⟨t, ?_, u, fun f hf => hu f (hr f hf), ?_⟩
      · rw [Nat.succ_mul, Nat.add_mul]
        omega
      · intro d' hd' s
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd') with hx | hx
        · exact hu _ (hprev d' hx s)
        · have heq : d' = d := Fin.ext hx
          subst d'
          simpa [states, s.isLt] using hs s.val s.isLt
  obtain ⟨l,hl,r,hr,hs⟩ := layers n le_rfl
  exact ⟨l,hl,r,hr,fun d => hs d d.isLt⟩

/-- Weighted output of the universal grammar in the ring of the chart's parameter
polynomials. `label` permits any numbering of the terminal and binary parameters. -/
noncomputable def weightedTable {K τ : Type*} [CommRing K] (k h n : ℕ)
    (label : GrammarLabel (Fin k) (Fin h) n → τ) (z : Fin k → K) (d : Fin n) (s : Fin h) :
    MvPolynomial τ K :=
  let G : ParseGrammar (MvPolynomial τ K) (Fin k) (Fin h) n :=
    ⟨fun a i => X (label (.inl (a,i))), fun j a b u v => X (label (.inr ⟨j,a,b,u,v⟩))⟩
  eval (C ∘ z) (G.eval d s)

/-- Scalar input weights can be precomputed in the chart advice; an ordinary
straight-line circuit evaluates the whole table at polynomial gate cost. -/
theorem circuitSize_weightedTable (label : GrammarLabel (Fin k) (Fin h) n → τ)
    (z : Fin k → K) (d : Fin n) (s : Fin h) :
    circuitSize (weightedTable k h n label z d s) ≤ tableGateBudget k h n := by
  let p := (Program.nil : Program K τ 0)
  let G : ParseGrammar (MvPolynomial τ K) (Fin k) (Fin h) n :=
    ⟨fun a i => X (label (.inl (a,i))), fun j a b u v => X (label (.inr ⟨j,a,b,u,v⟩))⟩
  obtain ⟨l, hl, r, _, hs⟩ := weightedTable_wires p G (C ∘ z)
    (fun _ _ => hasWire_var p _) (fun _ _ _ _ _ => hasWire_var p _) (fun _ => hasWire_const p _)
  obtain ⟨v, hv⟩ := hs d s
  exact circuitSize_le_iff.mpr ⟨l, by simpa using hl, ⟨r,v⟩, hv⟩

/-- The same shared table is the weighted sum of the original integral coordinate
polynomials, after renumbering the parameter variables and changing scalars. -/
theorem weightedTable_eq_coordinateSum (label : GrammarLabel (Fin k) (Fin h) n → τ)
    (base : ℕ) (a : K) (d : Fin n) (s : Fin h) :
    let P := (universalGrammar (Fin k) (Fin h) n).eval d s
    weightedTable k h n label (fun i => a^(base^i.val)) d s =
      ∑ ν ∈ P.support, rename label (map (Int.castRingHom K) (P.coeff ν)) *
        C (a^(digitExponent base ν)) := by
  let G : ParseGrammar (MvPolynomial τ K) (Fin k) (Fin h) n :=
    ⟨fun i j => X (label (.inl (i,j))), fun j i b u v => X (label (.inr ⟨j,i,b,u,v⟩))⟩
  have hs : G.specializeLabels =
      (rename label).toRingHom.comp (map (Int.castRingHom K)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ParseGrammar.specializeLabels]
    · intro i
      rcases i with ⟨i,j⟩ | ⟨d,i,j,u,v⟩ <;> simp [ParseGrammar.specializeLabels,
        ParseGrammar.labelValue, G]
  have htable := tableRows_weighted G base (C a) d s
  rw [tableRows_correct] at htable
  simpa only [weightedTable, Function.comp_def, map_pow,
    hs, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using htable

end Branch

end BorderVNP
end Computability
end OAI
