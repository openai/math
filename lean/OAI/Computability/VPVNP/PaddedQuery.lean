import OAI.Computability.VPVNP.HardnessQuery

/-! # Projections at every length above the table size

The query interpreter addresses the payload from the right end of its input.
A pinned run of zero bits between its self-delimiting table and the payload
therefore leaves all its queries unchanged. This gives the projection at a
specified source length, as needed for tensor powers along an infinite set of
lengths with small circuits.
-/

namespace OAI
namespace Computability
namespace VPVNP

open UniversalMachine

theorem weightedQuery_projection_at_length {R V Q : Type*} [CommRing R] [Fintype Q]
    {k : ℕ} (p : QueryProgram k Q) (t : ℕ) (weight : Projection R (Fin k) V)
    (n : ℕ) (hsize : (programPrefix (QueryMachine.machine p t)).length + k ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) V,
      φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) =
        weightedPredicate (fun x => p.eval x t p.start) weight := by
  let q := QueryMachine.machine p t
  let pre := programPrefix q
  let padded := pre ++ List.replicate (n - (pre.length + k)) false
  have hn : n = padded.length + k := by
    have hs : pre.length + k ≤ n := hsize
    simp [padded]
    omega
  have hc : q.extra = (t + 1) * Fintype.card Q * (k + 1) := by
    simp [q, QueryMachine.machine, TableCompiler.compile, QueryMachine.Control, Nat.mul_assoc]
  have hstates : t + 1 ≤ q.extra := by
    have hQ : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨p.start⟩
    rw [hc]
    exact (Nat.le_mul_of_pos_right _ hQ).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hpre : t + 2 ≤ padded.length := by
    have h := queryPrefix_lower hstates
    simpa only [padded, List.length_append] using h.trans (Nat.le_add_right _ _)
  have hp : (pinVariables (R := R) padded.get (Equiv.refl (Fin k))).hom
      (MvPolynomial.map (Int.castRingHom R) (P (padded.length+k))) =
      booleanPolynomial fun x => ((p.eval x t p.start).toNat : R) := by
    rw [map_P]
    apply pairedPolynomial_pin
    intro x
    have hd : decode (padded ++ List.ofFn x) = some q := by
      simp [padded, pre, List.append_assoc, decode_programPrefix]
    apply congrArg (fun j : ℕ => (j : R))
    change acceptingCount (Fin.append padded.get x) = _
    simp only [acceptingCount, List.ofFn_fin_append, List.ofFn_get, hd]
    exact QueryMachine.correct p t padded x _ (querySteps_le_clock rfl hpre)
  rw [hn]
  refine ⟨weight.comp (pinVariables padded.get (Equiv.refl (Fin k))), ?_⟩
  rw [Projection.hom_comp, RingHom.comp_apply, hp, weightedPredicate_eq_projection]

end VPVNP
end Computability
end OAI
