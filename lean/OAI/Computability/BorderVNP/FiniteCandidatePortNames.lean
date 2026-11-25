import OAI.Computability.BorderVNP.PackedNamedPortHeaders

/-! # Original private incidence rows in the finite candidate's flattened terminal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Shortening.Adaptive Packing Inherited EnrichedOuter

private theorem nestedPort_val {P : Type} {np : ℕ} (leaf : P ↪ Fin np) (k j : ℕ) (p : Port k P j) :
    let z := portEquiv k P j p
    (Parallel.nestedPorts k leaf j p).val = z.1.val*np+(leaf z.2).val := by
  induction j with
  | zero =>
    change (leaf p).val = 0 * np + (leaf p).val
    simp
  | succ j ih =>
    obtain ⟨a,p⟩ := p
    change (Parallel.nestedPorts k leaf j p).val + Parallel.nestedCapacity k np j * a.val = _
    rw [ih,WorkWords.nested_count,portEquiv_succ,copyIndex_val]
    ring

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

private theorem privatePort_val {P : Type} {np : ℕ} (leaf : P ↪ Fin np) (t : ℕ) (p : Port (fan S) P t) :
    let z := portEquiv (fan S) P t p
    (privatePorts S leaf t p).val = z.1.val*np+(leaf z.2).val := by
  induction t with
  | zero =>
    change (leaf p).val = 0 * np + (leaf p).val
    simp
  | succ t ih =>
    obtain ⟨i,p⟩ := p
    let a := (portEquiv S.fanIn (Port (fan S) P t) S.rounds).symm (i,p)
    have h := nestedPort_val (privatePorts S leaf t) S.fanIn S.rounds a
    rw [show portEquiv S.fanIn (Port (fan S) P t) S.rounds a = (i,p) from Equiv.apply_symm_apply _ _] at h
    have cap : portCapacity S np t = (fan S)^t*np := by
      simpa only [Parallel.nestedCapacity,pow_zero,one_mul] using WorkWords.path_count (np := np) S t 0
    refine h.trans ?_
    rw [ih,cap,portEquiv_succ,copyIndex_val]
    ring

/-- The physical port directory used by the inherited private evaluator
of the selected program on its true flattened terminal. -/
def fieldIncomingPorts (tiles t : ℕ) :=
  Flat.portRows t (privatePorts S (Function.Embedding.refl (Fin tiles)) t)

/-- The numerical input ordinals of the inherited evaluator agree with
the row-major port IDs used by the native geometry exporter. -/
theorem fieldIncomingPorts_val (tiles t : ℕ) (z : Fin ((fan S)^t) × Fin tiles) :
    (fieldIncomingPorts S tiles t z).val = (finProdFinEquiv z).val := by
  have h := privatePort_val S (Function.Embedding.refl (Fin tiles)) t ((portEquiv (fan S) (Fin tiles) t).symm z)
  rw [Equiv.apply_symm_apply] at h
  exact h.trans (by change z.1.val * tiles + z.2.val = z.2.val + tiles * z.1.val; ac_rfl)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
