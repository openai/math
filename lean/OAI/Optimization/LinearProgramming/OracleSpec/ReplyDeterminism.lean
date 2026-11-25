import OAI.Optimization.LinearProgramming.OracleSpec.Compression

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace MinorLog

private def atStep (p : RAM.Program) (s : RAM.State ℚ) : ℕ → Option (RAM.State ℚ)
  | 0 => some s
  | n + 1 => (atStep p s n).bind (RAM.step p)

private theorem trace_atStep {p : RAM.Program} {s : RAM.State ℚ} {k : ℕ}
    {t : Fin (k + 1) → RAM.State ℚ} (h : RAM.Trace p s k t) (i : Fin (k + 1)) :
    atStep p s i.val = some (t i) := by
  induction i using Fin.induction with
  | zero => exact congrArg some h.1.symm
  | succ i ih =>
    change (atStep p s i.val).bind (RAM.step p) = some (t i.succ)
    rw [show atStep p s i.val = some (t i.castSucc) from ih]
    exact h.2 i

private theorem halted_step {p : RAM.Program} {s : RAM.State ℚ} {tag : ℕ}
    (h : s.output = some tag) : RAM.step p s = none := by
  simp [RAM.step, h]

private theorem call_unique_le {p : RAM.Program} {s t₁ t₂ : RAM.State ℚ} {k₁ k₂ : ℕ}
    {t : Fin (k₁ + 1) → RAM.State ℚ} {u : Fin (k₂ + 1) → RAM.State ℚ}
    {tag : ℕ} (h₁ : RAM.Trace p s k₁ t) (e₁ : t (Fin.last k₁) = t₁)
    (h₂ : RAM.Trace p s k₂ u) (e₂ : u (Fin.last k₂) = t₂)
    (stop : t₁.output = some tag) (hk : k₁ ≤ k₂) : t₁ = t₂ := by
  let i : Fin (k₂ + 1) := ⟨k₁, by omega⟩
  have eq₁ : atStep p s k₁ = some t₁ := (trace_atStep h₁ (Fin.last k₁)).trans (congrArg some e₁)
  have eq₂ : atStep p s k₁ = some (u i) := trace_atStep h₂ i
  have eqState : u i = t₁ := Option.some.inj (eq₂.symm.trans eq₁)
  rcases lt_or_eq_of_le hk with hlt | rfl
  · let j : Fin k₂ := ⟨k₁, hlt⟩
    have bad := h₂.2 j
    change RAM.step p (u i) = some (u j.succ) at bad
    rw [eqState, halted_step stop] at bad
    contradiction
  · exact eqState.symm.trans e₂

/-- A request cannot have two different halting results for the same incoming state. -/
theorem call_terminal_unique {p : RAM.Program} {s t u : RAM.State ℚ}
    {c d b e i j : ℕ} (ht : call p c b s t) (hu : call p d e s u)
    (hi : t.output = some i) (hj : u.output = some j) : t = u := by
  obtain ⟨k, _, x, hx, hr, _⟩ := ht
  obtain ⟨l, _, y, hy, hs, _⟩ := hu
  rcases le_total k l with h | h
  · exact call_unique_le hx hr hy hs hi h
  · exact (call_unique_le hy hs hx hr hj h).symm

private theorem emits_halts {s : RAM.State ℚ} {r : Option ℚ} (h : emits s r) :
    ∃ tag, s.output = some tag := by
  cases r with
  | none => exact ⟨1, h⟩
  | some q => exact ⟨0, h.1⟩

private theorem emits_unique {s : RAM.State ℚ} {q r : Option ℚ}
    (h : emits s q) (g : emits s r) : q = r := by
  cases q with
  | none =>
    cases r with
    | none => rfl
    | some r => exact False.elim (by have := h.symm.trans g.1; contradiction)
  | some q =>
    cases r with
    | none => exact False.elim (by have := h.1.symm.trans g; contradiction)
    | some r => exact congrArg some (h.2.1.symm.trans g.2.1)

/-- Existence of a bounded RAM trace for each finite request list in the
contract uniquely determines its replies, including all restart positions. -/
theorem Processes.replies_unique {ι : Type} {encode : ι → List ℕ} {p : RAM.Program}
    {c b o : ℕ} {s : RAM.State ℚ} {us : List ι} {rs rs' : List (ι × Option ℚ)}
    (h : Processes encode p c b o s us rs) (g : Processes encode p c b o s us rs') :
    rs = rs' := by
  induction h generalizing rs' with
  | nil => cases g; rfl
  | cons hu _ hr _ _ ih =>
    cases g with
    | cons hv _ hs _ _ =>
      obtain ⟨i, hi⟩ := emits_halts hr
      obtain ⟨j, hj⟩ := emits_halts hs
      have st := call_terminal_unique hu hv hi hj
      cases st
      have eqr := emits_unique hr hs
      cases eqr
      exact congrArg (List.cons _) (ih (by assumption))

theorem Processes.take {ι : Type} {encode : ι → List ℕ} {p : RAM.Program}
    {c b o : ℕ} {s : RAM.State ℚ} {us : List ι} {rs : List (ι × Option ℚ)}
    (h : Processes encode p c b o s us rs) (j : ℕ) :
    Processes encode p c b o s (us.take j) (rs.take j) := by
  induction h generalizing j with
  | nil => simpa using (Processes.nil (encode := encode) (program := p)
      (clock := c) (height := b) (outputBits := o) _)
  | cons hu hlen hr hsize _ ih =>
    cases j with
    | zero => exact Processes.nil _
    | succ j => exact Processes.cons hu hlen hr hsize (ih j)

/-- Any two streams sharing a request prefix also share its values and
restart positions, independent of their future requests. -/
theorem Processes.agree_on_prefix {ι : Type} {encode : ι → List ℕ} {p : RAM.Program}
    {c b o : ℕ} {s : RAM.State ℚ} {us vs : List ι} {rs ts : List (ι × Option ℚ)}
    (h : Processes encode p c b o s us rs) (g : Processes encode p c b o s vs ts)
    (j : ℕ) (same : us.take j = vs.take j) : rs.take j = ts.take j := by
  have accepted := h.take j
  rw [same] at accepted
  exact accepted.replies_unique (g.take j)

end MinorLog
end OracleSpec
end LinearProgramming
end Optimization
end OAI
