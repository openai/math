import OAI.Hierarchy.ProbeBatchReplacement
import OAI.Hierarchy.ProbeDiscrepancy

namespace OAI
/-! # A uniformly saving finite catalogue at a fixed discrepancy threshold -/

noncomputable section
namespace Hierarchy.Probe

open scoped Classical BigOperators
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms

variable {k : ℕ} {F E A : Type*} [Field F] [Nonempty (Fin k)]
  [Fintype E] [Nonempty E] [Fintype A]

/-- Exactly the positive demand occurrences. Distinct occurrences of the
same commodity or catalyst are retained. -/
abbrev PositiveDemand (req : A → E) (p : E → ℝ) := {a : A // 0 < p (req a)}

/-- For one connected format and a compact box of legal prices, a finite
catalogue works on every ball failing the fixed discrepancy tolerance. For
every admitted histogram of every batch size, the estimate charges both the
actual installed widths and the full selector broadcast. -/
theorem discrepancy_catalogue (edge : E → Chord k) (req : A → E) (conn : Connected edge)
    (P : Set (E → ℝ)) (compact : IsCompact P) (nonneg : ∀ p ∈ P, ∀ e, 0 ≤ p e)
    {ε : ℝ} (hε : 0 < ε) (tree : ℝ) (htree : 0 ≤ tree) (N : ℕ) :
    let X := {p : E → ℝ // p ∈ P ∧ ε ≤ discrepancy F edge req p}
    ∃ (S : Finset X) (packet : (j : S) → Packet F edge
        (fun a : PositiveDemand req j.val.val => req a.val)) (γ : ℝ), 0 < γ ∧
      (∀ j, N < (packet j).width) ∧ ∀ p : X, ∃ j : S,
        (∀ a : PositiveDemand req j.val.val, γ ≤ p.val (req a.val)) ∧
        ∀ t (h : Histogram (Fin (packet j).terms) t),
          (∑ e, (histWidth (packet j).count h e : ℝ)*p.val e) + t*(tree*(packet j).selectorBits) ≤
            t*((packet j).width*((∑ a : PositiveDemand req j.val.val, p.val (req a.val))-γ)) := by
  classical
  let X := {p : E → ℝ // p ∈ P ∧ ε ≤ discrepancy F edge req p}
  let R (p : X) (a : PositiveDemand req p.val) := req a.val
  have compactX : IsCompact (P ∩ {p | ε ≤ discrepancy F edge req p}) :=
    compact_failed_tests F edge req conn compact ε
  let : CompactSpace X := isCompact_iff_compactSpace.mp compactX
  cases isEmpty_or_nonempty X with
  | inl empty =>
    let S : Finset X := ∅
    let impossible (j : S) : False := empty.false j.val
    exact ⟨S,fun j => (impossible j).elim,1,zero_lt_one,fun j => (impossible j).elim,
      fun p => (empty.false p).elim⟩
  | inr inhabited =>
    let : Nonempty X := inhabited
    have failed (p : X) : Failed F edge (R p) p.val :=
      (failed_positive_demands edge req p.val (nonneg p.val p.property.1)).mp
        ((failed_iff_discrepancy_pos F edge req conn p.val).mpr (hε.trans_le p.property.2))
    exact exists_packet_catalogue edge R (fun p : X => p.val)
      (fun p => nonneg p.val p.property.1)
      (fun e => (continuous_apply e).comp continuous_subtype_val)
      (fun _ a => a.property) conn failed tree htree N


end Hierarchy.Probe
end

end OAI
