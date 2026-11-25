import OAI.Computability.BorderVNP.DiagonalResidueRAMInputs

/-!
# Separate public query and private guess tapes for a named residue verifier

The gate record compiler absorbs the input numbering into the advice. Public
query pins and private guess pins occupy their own contiguous banks even
when the joint circuit's original numbering interleaves them.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BooleanTranscript VPVNP.BurstRAM RoutingISA
open scoped Classical

variable {Q G : Type*} [Fintype Q] [Fintype G] {w k : ℕ}

/-- The original joint numbering, followed by independent ordinal numbering of each input bank. -/
noncomputable def splitNumbering (Q G : Type*) [Fintype Q] [Fintype G] :
    Fin (Fintype.card (Q ⊕ G)) ≃ Fin (Fintype.card Q) ⊕ Fin (Fintype.card G) :=
  (Fintype.equivFin (Q ⊕ G)).symm.trans ((Fintype.equivFin Q).sumCongr (Fintype.equivFin G))

/-- Gate records specialized to the query and guess memory banks of the native machine. -/
noncomputable def typedCircuit (Q G : Type*) [Fintype Q] [Fintype G]
    (c : Circuit (Fin (Fintype.card (Q ⊕ G))) k) :
    Circuit (Fin (Fintype.card Q) ⊕ Fin (Fintype.card G)) k :=
  relabelCircuit (splitNumbering Q G) c

/-- Independent pin numberings compute the original verifier on the original named pins. -/
theorem typedCircuit_eval (c : Circuit (Fin (Fintype.card (Q ⊕ G))) k)
    (x : Q → Bool) (y : G → Bool) :
    (typedCircuit Q G c).eval (Sum.elim (x ∘ (Fintype.equivFin Q).symm) (y ∘ (Fintype.equivFin G).symm)) =
      c.eval ((Sum.elim x y) ∘ (Fintype.equivFin (Q ⊕ G)).symm) := by
  rw [typedCircuit, relabelCircuit_eval]
  congr 1
  funext i
  obtain ⟨j,rfl⟩ := (Fintype.equivFin (Q ⊕ G)).surjective i
  cases j <;> simp [splitNumbering, Function.comp_def]

/-- Native event paths with the loaded query and three-word gate advice. -/
noncomputable def typedPaths (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (base advice : ℕ) (c : Circuit (Fin (Fintype.card (Q ⊕ G))) k) (x : Q → Bool)
    (s : Bank w) (m : Memory w) :=
  let C := typedCircuit Q G c
  Paths pub macros (initialBank s (frame base advice C))
    (initialMemory m base advice C (x ∘ (Fintype.equivFin Q).symm))

/-- Native paths count the accepting assignments to the original private
input bits; no permutation of their names changes the multiplicity. -/
theorem typed_count (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (base advice : ℕ) (c : Circuit (Fin (Fintype.card (Q ⊕ G))) k) (x : Q → Bool)
    (s : Bank w) (m : Memory w)
    (hfit : gateBase base (Fintype.card Q) (Fintype.card G) + k ≤ advice ∧ advice + 3*k < 2^w) :
    (Nat.card (typedPaths pub macros base advice c x s m) : ℤ) =
      ∑ y : G → Bool, if c.eval (Sum.elim x y ∘ (Fintype.equivFin (Q ⊕ G)).symm) then (1 : ℤ) else 0 := by
  classical
  let C := typedCircuit Q G c
  let x' := x ∘ (Fintype.equivFin Q).symm
  rw [typedPaths, native_count pub macros base advice C x' _ _ hfit (initialBank_loaded ..)
    (initialMemory_query m base advice C x' (by unfold gateBase at hfit; omega))
    (initialMemory_advice m base advice C x')]
  let e := (Fintype.equivFin G).arrowCongr (Equiv.refl Bool)
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [C, x', show e y = y ∘ (Fintype.equivFin G).symm from rfl, typedCircuit_eval]

/-- Once gate, input and word widths are polynomial in the parameter, the
complete reader cost (including serialization of all advice words as bits)
is polynomial with a fixed quadratic bound in their common majorant. -/
theorem polynomial_budget {k v w B : ℕ} (hg : k ≤ B) (hv : v ≤ B) (hw : w ≤ B) :
    ticks k v + adviceWords k * w ≤ 40*(B+1)^2 := by
  unfold ticks adviceWords
  have h₀ := Nat.mul_le_mul (show 3*k+6 ≤ 3*B+6 by omega) hw
  nlinarith

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
