import OAI.Computability.VPVNP.BooleanTranscript
import OAI.Computability.VPVNP.HardnessWeights
import OAI.Computability.VPVNP.MatchClauses

/-! # Clause constraints for the signed path transcript

The unsigned tabular verifier reads a proposed transcript. Each gate contributes
at most seven literals. The two constant slots are pinned to their Boolean values
by the caller. Thus the proof applies even when a gate references a constant.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TranscriptCNF

open VPVNP VPVNP.BooleanTranscript VPVNP.HardnessCNF

variable {k g : ℕ} {σ : Type*}

/-- The payload slot supplying a constant, input, or earlier gate. -/
def address (constant : Bool → Fin k) (input : σ → Fin k) (wire : Fin g → Fin k) :
    Ref Bool σ g → Fin k
  | .const b => constant b
  | .var i => input i
  | .gate j => wire j

/-- Reading the slot agrees with reading the reference after the constants have been pinned. -/
theorem address_read (constant : Bool → Fin k) (input : σ → Fin k) (wire : Fin g → Fin k)
    (x : Fin k → Bool) (hc : ∀ b, x (constant b) = b) (r : Ref Bool σ g) :
    x (address constant input wire r) = r.read id (x ∘ input) (x ∘ wire) := by
  cases r with
  | const b => exact hc b
  | var | gate => rfl

private noncomputable def gateClauses (a : Ref Bool σ g → Fin k) (o : Fin k) : Gate σ g → CNF k
  | .and u v => matchClauses o (fun b : Bool => if b then a v else a u) (fun _ => true)
  | .not u => matchClauses o (fun _ : Unit => a u) (fun _ => false)

private theorem gateClauses_correct (c : Bool → Fin k) (i : σ → Fin k) (w : Fin g → Fin k)
    (o : Fin k) (h : Gate σ g) (x : Fin k → Bool) (hc : ∀ b, x (c b) = b) :
    Satisfies (gateClauses (address c i w) o h) x ↔ x o = h.eval (x ∘ i) (x ∘ w) := by
  cases h with
  | and a b =>
    rw [gateClauses, satisfies_matchClauses]
    rw [Bool.eq_iff_iff (a := x o) (b := (Gate.and a b).eval (x ∘ i) (x ∘ w))]
    simp [Gate.eval, address_read _ _ _ _ hc]
  | not a =>
    rw [gateClauses, satisfies_matchClauses]
    rw [Bool.eq_iff_iff (a := x o) (b := (Gate.not a).eval (x ∘ i) (x ∘ w))]
    simp [Gate.eval, address_read _ _ _ _ hc]

/-- Clause conjunction has additive literal count. -/
theorem literalCount_append (a b : CNF k) : literalCount (a ++ b) = literalCount a + literalCount b := by
  simp [literalCount]

/-- Conjunction of the gate clauses splits at a list concatenation. -/
theorem satisfies_append (a b : CNF k) (x : Fin k → Bool) :
    Satisfies (a ++ b) x ↔ Satisfies a x ∧ Satisfies b x := by
  exact List.forall_mem_append

/-- The local truth-table clauses of a shared Boolean program. -/
noncomputable def programClauses (constant : Bool → Fin k) (input : σ → Fin k) :
    {g : ℕ} → Program σ g → (Fin g → Fin k) → CNF k
  | _, .nil, _ => []
  | j+1, .snoc p h, w =>
    programClauses constant input p (w ∘ Fin.castSucc) ++
      gateClauses (address constant input (w ∘ Fin.castSucc)) (w (Fin.last j)) h

/-- The only satisfying assignment to the gate slots is the computed transcript. -/
theorem satisfies_programClauses (constant : Bool → Fin k) (input : σ → Fin k)
    (p : Program σ g) (wire : Fin g → Fin k) (x : Fin k → Bool) (hc : ∀ b, x (constant b) = b) :
    Satisfies (programClauses constant input p wire) x ↔ x ∘ wire = p.run (x ∘ input) := by
  induction p with
  | nil => simpa [programClauses, Satisfies] using (Subsingleton.elim (x ∘ wire) (Program.nil.run (x ∘ input)))
  | @snoc j p h ih =>
    rw [programClauses, satisfies_append, ih, gateClauses_correct _ _ _ _ _ _ hc]
    change (Fin.init (x ∘ wire) = p.run (x ∘ input) ∧
      x (wire (Fin.last j)) = h.eval (x ∘ input) (Fin.init (x ∘ wire))) ↔
      x ∘ wire = Fin.snoc (p.run (x ∘ input)) (h.eval (x ∘ input) (p.run (x ∘ input)))
    constructor
    · rintro ⟨hw,hl⟩
      rw [← hw, ← hl]
      exact (Fin.snoc_init_self (x ∘ wire)).symm
    · intro e
      have hw := congrArg Fin.init e
      have hl := congrFun e (Fin.last j)
      simp only [Fin.init_snoc] at hw
      exact ⟨hw, by simpa only [hw, Fin.snoc_last, Function.comp_apply] using hl⟩

/-- The conjunction uses at most seven literal occurrences per gate. -/
theorem literalCount_programClauses_le (constant : Bool → Fin k) (input : σ → Fin k)
    (p : Program σ g) (wire : Fin g → Fin k) :
    literalCount (programClauses constant input p wire) ≤ 7 * g := by
  induction p with
  | nil => simp [programClauses, literalCount]
  | @snoc j p h ih =>
    rw [programClauses, literalCount_append, Nat.mul_succ]
    apply Nat.add_le_add (ih _)
    cases h <;> simp [gateClauses, literalCount_matchClauses]

end TranscriptCNF

end BorderVNP
end Computability
end OAI
