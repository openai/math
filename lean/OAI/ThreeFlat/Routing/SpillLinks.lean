import OAI.ThreeFlat.Routing.LocalChecks

namespace OAI
/-! # Fixed candidate links for spill compaction

Each right port reads the reported selections and the corresponding data bit
from its public neighbors. Unassigned words and flags are canonically zero.
-/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.Spill

variable {L R F : Type*} [Fintype L] [Fintype R] [DecidableEq R]

abbrev Candidate (N : L → Finset R) := Σ x, N x
abbrev Contenders (N : L → Finset R) (r : R) := {x : L // r ∈ N x}
abbrev LinkPin (N : L → Finset R) (u : ℕ) :=
  Candidate N ⊕ ((L × Fin u) ⊕ (R × Option (Fin u)))

private abbrev LinkGate (R : Type*) (u : ℕ) := R × Option (Fin u)
private abbrev LinkPort (N : L → Finset R) (u : ℕ) (g : LinkGate R u) :=
  Option (Bool × Contenders N g.1)

private def linkWire (N : L → Finset R) (u : ℕ) (g : LinkGate R u) :
    LinkPort N u g → LinkPin N u ⊕ Empty
  | none => .inl (.inr (.inr g))
  | some (false,x) => .inl (.inl ⟨x.val,⟨g.1,x.property⟩⟩)
  | some (true,x) =>
    match g.2 with
    | none => .inl (.inl ⟨x.val,⟨g.1,x.property⟩⟩)
    | some k => .inl (.inr (.inl (x.val,k)))

private def linkTest (N : L → Finset R) (u : ℕ) (g : LinkGate R u)
    (bits : LinkPort N u g → Bool) : Prop :=
  bits none = decide (∃ x : Contenders N g.1,
    bits (some (false,x)) = true ∧ bits (some (true,x)) = true)

/-- The pins consist of selector bits, source words, and destination flags and words. -/
def linkNetwork [Zero F] [One F] (N : L → Finset R) (u : ℕ) :
    BitNetwork F (Fintype.card (LinkPin N u)) :=
  LocalChecks.network (LinkPort N u) (linkWire N u) (linkTest N u)

def linkPins {N : L → Finset R} {u : ℕ} (pick : Candidate N → Bool)
    (input : L → Fin u → Bool) (out : R → Option (Fin u) → Bool) : LinkPin N u → Bool :=
  Sum.elim pick (Sum.elim (Function.uncurry input) (Function.uncurry out))

/-- For an injective assignment, this is exactly its transported bit, and it
pins inactive output words to zero. The flag occupies coordinate `none`. -/
def packed {N : L → Finset R} {u : ℕ} (pick : Candidate N → Bool)
    (input : L → Fin u → Bool) (r : R) (k : Option (Fin u)) : Bool :=
  decide (∃ x : Contenders N r, pick ⟨x.val,⟨r,x.property⟩⟩ = true ∧
    k.elim true (input x.val) = true)

/-- Selector pins for an injection of an activity mask into its public neighbors. -/
def injectionPins {N : L → Finset R} (A : Finset L) (f : A ↪ R) :
    Candidate N → Bool :=
  fun e => decide (∃ hx : e.1 ∈ A, f ⟨e.1,hx⟩ = e.2.val)

omit [Fintype R] in
theorem packed_at {N : L → Finset R} {u : ℕ} (A : Finset L) (f : A ↪ R)
    (adjacent : ∀ x, f x ∈ N x.val) (input : L → Fin u → Bool) (x : A) (k : Option (Fin u)) :
    packed (injectionPins (N := N) A f) input (f x) k = k.elim true (input x.val) := by
  apply Bool.eq_iff_iff.mpr
  rw [packed,decide_eq_true_eq]
  constructor
  · rintro ⟨e,hh,hbit⟩
    obtain ⟨he,hr⟩ := of_decide_eq_true hh
    have hx := f.injective hr
    exact congrArg (fun z : A => k.elim true (input z.val)) hx ▸ hbit
  · intro hbit
    exact ⟨⟨x.val,adjacent x⟩,decide_eq_true ⟨x.property,rfl⟩,hbit⟩

omit [Fintype R] in
theorem packed_unused {N : L → Finset R} {u : ℕ} (A : Finset L) (f : A ↪ R)
    (input : L → Fin u → Bool) (r : R) (hr : ∀ x, f x ≠ r) (k : Option (Fin u)) :
    packed (injectionPins (N := N) A f) input r k = false := by
  apply decide_eq_false
  rintro ⟨e,hh,_⟩
  obtain ⟨ha,hr'⟩ := of_decide_eq_true hh
  exact hr ⟨e.val,ha⟩ hr'

theorem linkNetwork_eval [CommSemiring F] (N : L → Finset R) (u : ℕ)
    (pick : Candidate N → Bool) (input : L → Fin u → Bool) (out : R → Option (Fin u) → Bool) :
    TypedWiring.value (linkNetwork (F := F) N u) (linkPins pick input out) =
      if out = packed pick input then 1 else 0 := by
  rw [linkNetwork,LocalChecks.eval,Fintype.sum_unique]
  congr 1
  apply propext
  change (∀ g, linkTest N u g _) ↔ _
  constructor
  · intro h
    funext r k
    have hh := h (r,k)
    cases k <;> simpa [linkTest,linkWire,linkPins,packed,Function.comp_def] using hh
  · rintro rfl ⟨r,k⟩
    cases k <;> simp [linkTest,linkWire,linkPins,packed]

/-- The public right degree bounds the per-bit cost independently of the size
of the left bank and of the selected links. -/
theorem linkNetwork_cells [Zero F] [One F] (N : L → Finset R) (u D : ℕ)
    (right : ∀ r, Fintype.card (Contenders N r) ≤ D) :
    (linkNetwork (F := F) N u).cells ≤ Fintype.card R * (u+1) *
      (2^(2*D+1)*(2*D+3)) := by
  have arity (g : LinkGate R u) : Fintype.card (LinkPort N u g) ≤ 2*D+1 := by
    simp only [LinkPort,Fintype.card_option,Fintype.card_prod,Fintype.card_bool]
    have := right g.1
    omega
  simpa [linkNetwork, LinkGate,Fintype.card_prod,Nat.add_assoc] using
    LocalChecks.cells_le (F := F) (LinkPort N u) (linkWire N u) (linkTest N u) arity

end ThreeFlat.Routing.Spill

end
end OAI
