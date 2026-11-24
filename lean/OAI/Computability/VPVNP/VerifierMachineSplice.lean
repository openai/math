import OAI.Computability.VPVNP.VerifierMachineNetwork

/-!
# Substitution of compiled Boolean networks

Feeding all outputs of one circuit block into another takes the disjoint union of their
gate lists. Wires of the second block either select an output of the first block or
reference a gate in the appended list. This allows a verifier to use a compiled subroutine
more than once while sharing intermediate wires within each invocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierNetwork

open BinPackingGames.Foundations.Complexity.CookLevin

private def renameGate (wire : ℕ → ℕ) : Gate → Gate
  | .const b => .const b
  | .not i => .not (wire i)
  | .and i j => .and (wire i) (wire j)
  | .or i j => .or (wire i) (wire j)

private theorem renameGate_eval (wire : ℕ → ℕ) (g : Gate) (A : ℕ → Bool) :
    (renameGate wire g).eval A = g.eval (A ∘ wire) := by
  cases g <;> rfl

private theorem renameGate_bounded (wire : ℕ → ℕ) (g : Gate) {a b : ℕ}
    (h : g.Bounded a) (hw : ∀ j < a, wire j < b) : (renameGate wire g).Bounded b := by
  cases g with
  | const => trivial
  | not i => exact hw i h
  | and i j => exact ⟨hw i h.1, hw j h.2⟩
  | or i j => exact ⟨hw i h.1, hw j h.2⟩

private def relocate {p n : ℕ} (g : CircuitBatch.Frame p n) (j : ℕ) : ℕ :=
  if h : j < n then g.wires ⟨j, h⟩ else p + g.fragment.gates.length + (j - n)

private theorem relocate_lt {p n : ℕ} (g : CircuitBatch.Frame p n) {i j : ℕ}
    (hj : j < n + i) : relocate g j < p + g.fragment.gates.length + i := by
  unfold relocate
  split
  · next h => exact lt_of_lt_of_le (g.wires ⟨j, h⟩).isLt (Nat.le_add_right _ _)
  · omega

private theorem relocate_ordered {p n : ℕ} (g : CircuitBatch.Frame p n)
    (f : CircuitBatch.Fragment n) :
    Ordered (p + g.fragment.gates.length) (f.gates.map (renameGate (relocate g))) := by
  intro i hi
  have hi' : i < f.gates.length := by simpa using hi
  rw [List.getElem_map]
  exact renameGate_bounded _ _ (f.ordered i hi') (fun _ hj => relocate_lt g hj)

private def spliceCore {p n m : ℕ} (f : CircuitBatch.Frame n m)
    (g : CircuitBatch.Frame p n) : CircuitBatch.Frame p m where
  fragment := g.fragment.append (f.fragment.gates.map (renameGate (relocate g)))
    (relocate_ordered g f.fragment)
  wires := fun i => ⟨relocate g (f.wires i), by
    simpa [CircuitBatch.Fragment.append, Nat.add_assoc] using relocate_lt g (f.wires i).isLt⟩

private theorem spliceCore_eval {p n m : ℕ} (f : CircuitBatch.Frame n m)
    (g : CircuitBatch.Frame p n) (x : Fin p → Bool) (i : Fin m) :
    (spliceCore f g).eval x i = f.eval (g.eval x) i := by
  let A := (spliceCore f g).fragment.evalWires x
  let gs := f.fragment.gates.map (renameGate (relocate g))
  have hc : Consistent (p + g.fragment.gates.length) gs A :=
    ((consistent_append p g.fragment.gates gs A).mp
      ((spliceCore f g).fragment.evalWires_consistent x)).2
  have hf : Consistent n f.fragment.gates (A ∘ relocate g) := by
    intro k hk
    have h := hc k (by simpa [gs] using hk)
    simp only [gs, List.getElem_map, renameGate_eval] at h
    simpa [Function.comp_apply, relocate] using h
  have hx : ∀ j < n, inputEnv (g.eval x) j = (A ∘ relocate g) j := by
    intro j hj
    simp only [inputEnv, dite_eq_left hj, Function.comp_apply, relocate]
    exact (g.fragment.evalWires_append_old gs (relocate_ordered g f.fragment) x
      (g.wires ⟨j, hj⟩) (g.wires ⟨j, hj⟩).isLt).symm
  exact (run_unique n f.fragment.gates _ _ f.fragment.ordered hf hx _ (f.wires i).isLt).symm

namespace Frame

variable {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]

/-- Substitute a compiled network for the free inputs of another. -/
def subst (f : Frame σ τ) (g : Frame ρ σ) : Frame ρ τ :=
  ⟨spliceCore f.core g.core⟩

@[simp] theorem subst_size (f : Frame σ τ) (g : Frame ρ σ) :
    (f.subst g).size = g.size + f.size := by
  simp [subst, size, spliceCore, CircuitBatch.Fragment.append]

@[simp] theorem subst_eval (f : Frame σ τ) (g : Frame ρ σ) (x : ρ → Bool) (i : τ) :
    (f.subst g).eval x i = f.eval (g.eval x) i := by
  simp [subst, eval, spliceCore_eval, Function.comp_def]

end Frame
end VerifierNetwork

end VPVNP
end Computability
end OAI
