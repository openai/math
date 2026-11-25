import OAI.Computability.BorderVNP.PackedHistoryEpoch

/-! # Numeric port-arity transport of a finite history circuit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open VPVNP.VerifierNetwork

/-- Transport a public state family to an equal numeric port arity. The original
circuit still reads its native guess pins and produces the same acceptance flag. -/
def resizeSteps {k b a c : ℕ} (h : a=c) (W : ℕ → ℕ → Type) (G : ℕ → Type)
    [∀ p i, Fintype (W p i)] [∀ i, Fintype (G i)] (f : Steps k b (W a) G) : Steps k b (W c) G :=
  h ▸ f

/-- A change of arity along numerical equality adds no Boolean gates. -/
theorem resizeSteps_size {k b a c : ℕ} (h : a=c) (W : ℕ → ℕ → Type) (G : ℕ → Type)
    [∀ p i, Fintype (W p i)] [∀ i, Fintype (G i)] (f : Steps k b (W a) G) (i : Fin b) :
    (resizeSteps h W G f i.val i.isLt).size = (f i.val i.isLt).size := by subst c; rfl

/-- Read a transported flat history on the original native port and guess pins.
The two casts only rename the physical state wires at the leaves and root. -/
theorem resizeSteps_flat_read {k b a c : ℕ} (h : a=c) (W : ℕ → ℕ → Type) (G : ℕ → Type)
    [∀ p i, Fintype (W p i)] [∀ i, Fintype (G i)] (f : Steps k b (W a) G)
    (x : Fin (k^b) → W c 0 → Bool) (g : Slot k G b → Bool) (o : Result (W a b)) :
    (flatEpoch (resizeSteps h W G f)).eval (Sum.elim (fun z => x z.1 z.2) g)
        (Sum.map (cast (congrArg (fun p => W p b) h)) id o) =
      (flatEpoch f).eval (Sum.elim (fun z => x z.1 (cast (congrArg (fun p => W p 0) h) z.2)) g) o := by
  subst c
  cases o <;> rfl

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
