import OAI.Computability.VPVNP.Valiant.ProjectModel
import OAI.Computability.VPVNP.CircuitSize

/-! # Exact circuit correspondence for the project permanent-completeness statement -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Valiant.Project

open MvPolynomial (C X)

variable {F σ : Type*} [Field F] {s k : ℕ}

private abbrev available (v : Fin s → MvPolynomial σ F) (k : ℕ) (x : MvPolynomial σ F) : Prop :=
  (∃ j : σ, X j = x) ∨ (∃ a : F, C a = x) ∨ ∃ j : Fin s, j.val < k ∧ v j = x

private abbrev prefixValues (v : Fin s → MvPolynomial σ F) (hk : k ≤ s) (i : Fin k) :=
  v (i.castLE hk)

private abbrev gateValue (allowed : MvPolynomial σ F → Prop) (x : MvPolynomial σ F) : Prop :=
  ∃ a b, allowed a ∧ allowed b ∧ (x = a + b ∨ x = a - b ∨ x = a * b)

private theorem available_iff_ref (v : Fin s → MvPolynomial σ F) (hk : k ≤ s)
    (x : MvPolynomial σ F) :
    available v k x ↔ ∃ r : Ref F σ k, r.read C X (prefixValues v hk) = x := by
  constructor
  · rintro (⟨j, rfl⟩ | ⟨c, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨.var j, rfl⟩
    · exact ⟨.const c, rfl⟩
    · exact ⟨.gate ⟨j, hj⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    cases r with
    | var j => exact Or.inl ⟨j, rfl⟩
    | const c => exact Or.inr (Or.inl ⟨c, rfl⟩)
    | gate j => exact Or.inr (Or.inr ⟨j.castLE hk, j.isLt, rfl⟩)

private theorem gateValue_iff (v : Fin s → MvPolynomial σ F) (hk : k ≤ s)
    (x : MvPolynomial σ F) :
    gateValue (available v k) x ↔ ∃ op : BinOp, ∃ a b : Ref F σ k,
      op.apply (a.read C X (prefixValues v hk)) (b.read C X (prefixValues v hk)) = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hx⟩
    obtain ⟨ra, rfl⟩ := (available_iff_ref v hk a).mp ha
    obtain ⟨rb, rfl⟩ := (available_iff_ref v hk b).mp hb
    rcases hx with rfl | rfl | rfl
    · exact ⟨.add, ra, rb, rfl⟩
    · exact ⟨.sub, ra, rb, rfl⟩
    · exact ⟨.mul, ra, rb, rfl⟩
  · rintro ⟨op, a, b, rfl⟩
    refine ⟨_, _, (available_iff_ref v hk _).mpr ⟨a, rfl⟩,
      (available_iff_ref v hk _).mpr ⟨b, rfl⟩, ?_⟩
    cases op with
    | add => exact Or.inl rfl
    | sub => exact Or.inr (Or.inl rfl)
    | mul => exact Or.inr (Or.inr rfl)

private theorem run_snoc_last (q : Program F σ s) (op : BinOp) (a b : Ref F σ s) :
    (q.snoc op a b).run C X (Fin.last s) =
      op.apply (a.read C X (q.run C X)) (b.read C X (q.run C X)) := by
  simp only [Program.run, Fin.lastCases_last]

private theorem run_snoc_castSucc (q : Program F σ s) (op : BinOp) (a b : Ref F σ s)
    (i : Fin s) : (q.snoc op a b).run C X i.castSucc = q.run C X i := by
  simp only [Program.run, Fin.lastCases_castSucc]

/-- Build a program for a prefix without duplicating any of its referenced gates. -/
private theorem realize_prefix (v : Fin s → MvPolynomial σ F)
    (h : ∀ i : Fin s, gateValue (available v i.val) (v i)) (k : ℕ) (hk : k ≤ s) :
    ∃ q : Program F σ k, q.run C X = prefixValues v hk := by
  induction k with
  | zero => exact ⟨.nil, Subsingleton.elim _ _⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih (Nat.le_of_succ_le hk)
    let i : Fin s := ⟨k, hk⟩
    obtain ⟨op, a, b, hop⟩ := (gateValue_iff v (Nat.le_of_succ_le hk) (v i)).mp (h i)
    refine ⟨q.snoc op a b, ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [run_snoc_last, hq]
      exact hop
    · rw [run_snoc_castSucc]
      exact congrFun hq j

/-- Reading a program as a table recovers legal operands at every position. -/
private theorem program_gate (q : Program F σ s) (i : Fin s) :
    gateValue (available (q.run C X) i.val) (q.run C X i) := by
  induction q with
  | nil => exact i.elim0
  | @snoc s q op a b ih =>
    let v := q.run C X
    let v' := (q.snoc op a b).run C X
    have previous (k : ℕ) (hk : k ≤ s) :
        prefixValues v' (Nat.le_succ_of_le hk) = prefixValues v hk := by
      funext j
      exact run_snoc_castSucc q op a b (j.castLE hk)
    cases i using Fin.lastCases with
    | last =>
      apply (gateValue_iff v' (Nat.le_succ s) _).mpr
      refine ⟨op, a, b, ?_⟩
      rw [previous s le_rfl]
      exact (run_snoc_last q op a b).symm
    | cast j =>
      obtain ⟨op', a', b', hj⟩ := (gateValue_iff v j.isLt.le _).mp (ih j)
      apply (gateValue_iff v' (Nat.le_succ_of_le j.isLt.le) _).mpr
      refine ⟨op', a', b', ?_⟩
      rw [previous j.val j.isLt.le]
      exact hj.trans (run_snoc_castSucc q op a b j).symm

/-- The self-contained table model and the project's exact circuits compute precisely
the same formal polynomials with exactly the same number of binary gates. -/
theorem computes_iff {s : ℕ} {p : MvPolynomial σ F} :
    Computes s p ↔ ∃ c : VPVNP.Circuit F σ s, c.polynomial = p := by
  constructor
  · rintro ⟨v, hout, h⟩
    obtain ⟨q, hq⟩ := realize_prefix v h s le_rfl
    obtain ⟨r, hr⟩ := (available_iff_ref v le_rfl p).mp hout
    refine ⟨⟨q, r⟩, ?_⟩
    change r.read C X (q.run C X) = p
    rwa [hq]
  · rintro ⟨c, rfl⟩
    exact ⟨c.program.run C X, (available_iff_ref _ le_rfl _).mpr ⟨c.output, rfl⟩,
      program_gate c.program⟩

end Valiant.Project

end VPVNP
end Computability
end OAI
