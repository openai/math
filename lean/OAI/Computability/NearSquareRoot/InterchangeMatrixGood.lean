import OAI.Computability.NearSquareRoot.InterchangeCalls
import OAI.Computability.NearSquareRoot.InterchangeStarPhysical

/-!
# Compiled matrix calls with an invariant on recursive payloads

The physical permutation of the selected fields is fixed before choosing a
payload invariant. Each child of the charged program satisfies the invariant
record by record whenever the input stream does.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.Interchange Matrix

variable {X I J : Type} [Fintype I] {b n : ℕ} [NeZero b]

/-- The matrix acts on whole records and every requested child carries
records satisfying the caller's predicate. -/
def ExecutesMatrixGood (slot : I → Spot J) (M : (f : ℕ) → Matrix I I (Tower b f))
    (r : Regime X) (l : X → ℕ) (ord : J ≃ Fin n) (P G B : X → Dims.Tape)
    (f : X → ℕ) (price : ℕ) : Prop :=
  ∃ perm : (x : X) → Equiv.Perm (domain (J:=J) (b:=b) P G B f x),
    (∀ x a, watcher (perm x a) = watcher a ∧
      (∀ i, hear (chase (perm x a)) (slot i) =
        (M (f x) *ᵥ (fun j => hear (chase a) (slot j))) i) ∧
      (∀ s, (∀ i, s ≠ slot i) → hear (chase (perm x a)) s = hear (chase a) s)) ∧
    ∀ (good : X → Tree → Prop) (v : (x : X) → domain (J:=J) (b:=b) P G B f x → Tree),
      Manifest _ l v → (∀ x k, good x (v x k)) →
      ChargedGood (r:=r) (l:=l) ord P G B f (b:=b) good price
        (stackRun (layoutRows ord P G B f) v)
        (stackRun (layoutRows ord P G B f) (fun x => v x ∘ (perm x).symm))

/-- Use one compiled matrix program for every admissible record stream and
every proof-level restriction on the alphabet or encoding of child records. -/
theorem execute_matrix_good [DecidableEq J] (slot : I → Spot J)
    (M : (f : ℕ) → Matrix I I (Tower b f)) (r : Regime X) (l : X → ℕ)
    (ord : J ≃ Fin n) (P G B : X → Dims.Tape) (f : X → ℕ) (price : ℕ)
    (hc : CompilesOn slot (ranking ord) price M) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) :
    ExecutesMatrixGood slot M r l ord P G B f price := by
  obtain ⟨ops,hlegal,hprice,hphysical⟩ := CompilesOn.physical ord hc
  refine ⟨fun x => recreation ord (P x) (G x) (B x) (f x) ops hlegal,
    fun x => hphysical (P x) (G x) (B x) (f x), fun good v hv hgood => ?_⟩
  apply (execute_charged_good ord P G B f good hb hf hp hg hs ops hlegal v hv hgood).monotone
  exact_mod_cast hprice

end InterchangeAddress

end NearSquareRoot
end Computability
end OAI
