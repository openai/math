import OAI.Computability.VPVNP.HardnessQuery
import OAI.Computability.VPVNP.HardnessWeights
import OAI.Computability.BorderVNP.SignedFamily

/-!
# Signed universal projections of weighted Boolean query programs

The CNF interpreter leaves the work tape untouched, hence all its accepting
paths have sign plus one. Its literal table fits the shorter signed clock
at every length large enough to hold the prefix and the assignment bits.
Negative path weights can be supplied by projecting a transcript bit to `-1`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open VPVNP MvPolynomial
open VPVNP.UniversalMachine
open VPVNP.TableCompiler

private theorem quietBranch {Q : Type*} [Fintype Q] (start : Q) (f : Q → Symbol → Step Q)
    (c : Config (Fintype.card Q)) (h : 2 ≤ c.state.val) :
    ∃ a, branches (compile start f) c = .one a ∧ a.secondSymbol = c.secondTape.head ∧
      a.secondMove = 0 := by
  let j := (c.state.val - 2) * 9 + c.firstTape.head.val * 3 + c.secondTape.head.val
  have hj : j < Fintype.card Q * 9 := by
    have := c.state.isLt
    have := c.firstTape.head.isLt
    have := c.secondTape.head.isLt
    dsimp [j]; omega
  have hj3 : j % 3 = c.secondTape.head.val := by
    have := c.secondTape.head.isLt
    dsimp [j]; omega
  unfold branches compile
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hj)]
  simp only [List.getElem_ofFn, Option.getD_some]
  refine ⟨_, rfl, ?_⟩
  generalize f _ _ = action
  cases action <;> exact ⟨Fin.ext hj3, rfl⟩

/-- A read-only compiled query control has the same signed and unsigned path counts
whenever its work head is clear of the negative-output marker. -/
theorem signedPaths_compile {Q : Type*} [Fintype Q] (start : Q) (f : Q → Symbol → Step Q)
    (fuel : ℕ) (c : Config (Fintype.card Q)) (hw : c.secondTape.head ≠ 2) :
    signedPaths (compile start f) fuel c = (paths (compile start f) fuel c : ℤ) := by
  induction fuel generalizing c with
  | zero =>
    by_cases ha : c.state.val = 1 <;> simp [signedPaths, haltOutput, paths, ha, hw]
  | succ fuel ih =>
    by_cases ha : c.state.val = 1
    · simp [signedPaths, paths, ha, haltOutput, hw]
    by_cases hr : c.state.val = 0
    · simp [signedPaths, paths, hr]
    obtain ⟨instr, hrow, hsymbol, hmove⟩ := quietBranch start f c (by omega)
    simp only [signedPaths, paths, ha, hr, ite_false, hrow]
    exact ih (advance c instr) (by simpa [advance, updateTape, hsymbol, hmove] using hw)

private theorem querySteps_le_signedClock {t k ℓ : ℕ} (ht : t + 2 ≤ ℓ) :
    t * (ℓ + k + k + 1) + 1 ≤ (ℓ + k) ^ 100 := by
  let n := ℓ + k
  have h2 : 2 ≤ n := by dsimp [n]; omega
  change t * (n + k + 1) + 1 ≤ n ^ 100
  calc
    _ ≤ (t + 1) * (n + k + 1) := by rw [Nat.succ_mul]; omega
    _ ≤ n * (2 * n) := Nat.mul_le_mul (by dsimp [n]; omega) (by dsimp [n]; omega)
    _ ≤ n * (n * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]
    _ ≤ n ^ 100 := Nat.pow_le_pow_right (by omega) (by decide)

/-- At any length holding the table and its payload, one literal projection from
the signed universal family gives the weighted formal polynomial of a query program. -/
theorem weightedQuery_projection_at_length {R V Q : Type*} [CommRing R] [Fintype Q]
    {k : ℕ} (p : QueryProgram k Q) (t : ℕ) (weight : Projection R (Fin k) V)
    (n : ℕ) (hsize : (programPrefix (QueryMachine.machine p t)).length + k ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) V,
      φ.hom (MvPolynomial.map (Int.castRingHom R) (Pstar n)) =
        weightedPredicate (fun x => p.eval x t p.start) weight := by
  let q := QueryMachine.machine p t
  let pre := programPrefix q
  let padded := pre ++ List.replicate (n - (pre.length + k)) false
  have hn : n = padded.length + k := by
    have hs : pre.length + k ≤ n := hsize
    simp [padded]
    omega
  have hstates : t + 1 ≤ q.extra := by
    have hQ : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨p.start⟩
    change t + 1 ≤ Fintype.card (QueryMachine.Control t k Q)
    simp only [QueryMachine.Control, Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc]
    exact (Nat.le_mul_of_pos_right _ hQ).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hpre : t + 2 ≤ padded.length := by
    have h := queryPrefix_lower hstates
    simpa only [padded, List.length_append] using h.trans (Nat.le_add_right _ _)
  have hp : (pinVariables (R := R) padded.get (Equiv.refl (Fin k))).hom
      (MvPolynomial.map (Int.castRingHom R) (Pstar (padded.length+k))) =
      booleanPolynomial fun x => ((p.eval x t p.start).toNat : R) := by
    rw [map_Pstar]
    apply pairedPolynomial_pin
    intro x
    have hd : decode (padded ++ List.ofFn x) = some q := by
      simp [padded, pre, List.append_assoc, decode_programPrefix]
    change (signedCount (Fin.append padded.get x) : R) = _
    simp only [signedCount, List.ofFn_fin_append, List.ofFn_get, hd]
    let ticks := (padded.length + k) ^ 100
    let initialConfig := initial q (padded ++ List.ofFn x)
    have hs : signedPaths q ticks initialConfig = (paths q ticks initialConfig : ℤ) :=
      signedPaths_compile (QueryMachine.start p t) (QueryMachine.command p t) ticks initialConfig
        (by change (0 : Symbol) ≠ 2; decide)
    have hu : paths q ticks initialConfig = (p.eval x t p.start).toNat :=
      QueryMachine.correct p t padded x _ (querySteps_le_signedClock hpre)
    change ((signedPaths q ticks initialConfig : ℤ) : R) = _
    rw [hs, hu]
    simp

  rw [hn]
  refine ⟨weight.comp (pinVariables padded.get (Equiv.refl (Fin k))), ?_⟩
  rw [Projection.hom_comp, RingHom.comp_apply, hp, weightedPredicate_eq_projection]

/-- Specializing the weighted query theorem to the CNF interpreter realizes a weighted
sum over satisfying assignments. The source length is bounded in the literal count and
the number of transcript bits. -/
theorem weightedCNF_projection_at_length {R V : Type*} [CommRing R] {k : ℕ}
    (c : HardnessCNF.CNF k) (weight : Projection R (Fin k) V) (n : ℕ)
    (hn : 1000 * ((HardnessCNF.literalCount c + 1) * (2 + HardnessCNF.literalCount c) *
      (k + 1) + 1) ^ 2 + k ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) V,
      φ.hom (MvPolynomial.map (Int.castRingHom R) (Pstar n)) =
        HardnessCNF.weightedCNF c (fun i => (weight i).elim X C) := by
  rw [HardnessCNF.weightedCNF_eq_query]
  apply weightedQuery_projection_at_length
  refine le_trans (Nat.add_le_add_right (programPrefix_length_le _) k) ?_
  have hstates : HardnessCNF.stateCount c = 2 + HardnessCNF.literalCount c := by
    simpa only [HardnessCNF.State, Fintype.card_fin] using HardnessCNF.card_state c
  simpa only [QueryMachine.machine, TableCompiler.compile, QueryMachine.Control, Fintype.card_prod,
    Fintype.card_fin, hstates, Nat.mul_assoc] using hn

end Crossing

end BorderVNP
end Computability
end OAI
