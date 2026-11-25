import OAI.Optimization.LinearProgramming.Geometry.BorderWire
import OAI.Optimization.LinearProgramming.Geometry.Pivot
import OAI.Optimization.LinearProgramming.Geometry.CanonicalMinorQuery

/-! Every successful or restarting request in the physical prefix loop refers to a
canonical nonzero minor of the original matrix. This holds for arbitrary answer values. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

namespace MinorQuery

variable {κ α β : Type*}

/-- An adaptive query uses only keys satisfying `ok`, on every possible reply path. -/
def AllKeys (ok : κ → Prop) : MinorQuery κ α → Prop
  | .done _ => True
  | .query x next => ok x ∧ ∀ q, AllKeys ok (next q)

protected theorem AllKeys.bind {ok : κ → Prop} {tree : MinorQuery κ α} {next : α → MinorQuery κ β}
    (ht : AllKeys ok tree) (hn : ∀ a, AllKeys ok (next a)) : AllKeys ok (tree.bind next) := by
  induction tree with
  | done a => exact hn a
  | query k children ih => exact ⟨ht.1, fun q => ih q (ht.2 q)⟩

theorem allKeys_readColumns {n : ℕ} (ok : κ → Prop) (key : Fin n → κ) (js : List (Fin n))
    (v : Fin n → ℚ) (good : ∀ j ∈ js, ok (key j)) : AllKeys ok (readColumns key js v) := by
  induction js generalizing v with
  | nil => trivial
  | cons j rest ih =>
    exact ⟨good j (by simp),fun q => ih _ (fun x h => good x (by simp [h]))⟩

/-- No additional key is submitted at a successful return. -/
def StopKey (ok : κ → Prop) : Sum κ α → Prop
  | .inl k => ok k
  | .inr _ => True

theorem Run.all_keys {ok : κ → Prop} {tree : MinorQuery κ α} {xs out}
    (hr : Run tree xs out) (ht : AllKeys ok tree) :
    (∀ e ∈ xs, ok e.1) ∧ StopKey ok out := by
  induction hr with
  | done => exact ⟨by simp, trivial⟩
  | restart => exact ⟨by simp, ht.1⟩
  | answer key next v tail ih =>
    obtain ⟨known,last⟩ := ih (ht.2 v)
    refine ⟨?_,last⟩
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact ht.1
    · exact known e he

end MinorQuery

variable {r s n : ℕ}

/-- The key decoder succeeds on all pivot requests. Zero minors are skipped by the
actual filtered column scan before control reaches the compression service. -/
theorem pivotPrefix_named (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (p : Fin n → ℚ) (a : ℕ) (ha : a≤r) :
    MinorQuery.AllKeys (fun x => ∃ u, Canonical.checkedPrimalMinor D E x=some u) (pivotPrefix D p a ha) := by
  induction a with
  | zero => trivial
  | succ a ih =>
    unfold pivotPrefix
    apply MinorQuery.AllKeys.bind (ih (by omega))
    rintro (_|rows)
    · trivial
    apply MinorQuery.AllKeys.bind
    · unfold pivotStep
      apply MinorQuery.AllKeys.bind
      · apply MinorQuery.allKeys_readColumns
        intro j hj
        let A := D.submatrix (Fin.castLE ha) id
        let J := fun x => (rows x).pivot
        have atj : (Vector.ofFn (borderedMinor A J)).get j = circuitMinor A J j :=
          (Vector.getElem_ofFn (f := borderedMinor A J) j.isLt).trans (borderedMinor_eq A J j)
        change j ∈ (List.finRange n).filter (fun b => decide ((Vector.ofFn (borderedMinor A J)).get b ≠ 0)) at hj
        have nz : (Vector.ofFn (borderedMinor A J)).get j ≠ 0 := of_decide_eq_true (List.mem_filter.mp hj).2
        obtain ⟨u,hu,_⟩ := BorderBatch.prefixWords_spec D E ha J j (atj ▸ nz)
        exact ⟨u,hu⟩
      · intro _; trivial
    · intro _; trivial

/-- Both the answered transcript and the possible final restart call have genuine
indices in the comparator's universe of square nonzero minors. -/
theorem prefix_run_named (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (p : Fin n → ℚ) {a : ℕ} (ha : a≤r) {xs out} (hr : MinorQuery.Run (pivotPrefix D p a ha) xs out) :
    (∀ e ∈ xs, ∃ u, Canonical.checkedPrimalMinor D E e.1 = some u) ∧
      MinorQuery.StopKey (fun k => ∃ u, Canonical.checkedPrimalMinor D E k=some u) out :=
  hr.all_keys (pivotPrefix_named D E p a ha)

end Geometry
end LinearProgramming
end Optimization
end OAI
