import OAI.Computability.IntegerMultiplication.Carry.Figure
import OAI.Computability.NearSquareRoot.BoundedProgram

/-! # Expanding binary descriptor parameters to unary tape headers

Short binary arithmetic costs a polynomial in the descriptor scale. Each
large unary field is materialized for a separate linear charge in its size.
Pairs preserve this accounting, so a prefix and a suffix can both be large.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Strip Carry

variable {I A B : Type} [Codec A] [Codec B] {r : Regime I}

/-- Computing `f` from the descriptor using its serialized result size plus
polynomial setup. This definition also encompasses mixed binary/unary headers. -/
def Mint (r : Regime I) (f : I → A) : Prop :=
  ∃ t, Dom r.scale t ∧ Task (fun i => t i + size (f i)) r.header (send ∘ f)

namespace Mint

/-- Small fields can be emitted directly. -/
theorem of_has {f : I → A} (hf : r.Has f) : Mint r f := by
  obtain ⟨b,db,cmd⟩ := hf
  exact ⟨b, db, cmd.mono (fun _ => Nat.le_add_right ..)⟩

/-- Read the short binary result and emit exactly that many unary units. -/
theorem tally {f : I → ℕ} (hf : Figure r f) : Mint r (Code.tally ∘ f) := by
  obtain ⟨words,built,correct⟩ := hf
  have ds : Dom r.scale (fun i => size (words i)) := Regime.Small.extent built
  obtain ⟨b,db,cmd⟩ := built
  have run := cmd.compose (rice.on words)
  simp only [correct] at run
  refine ⟨_,db.add ds, run.mono ?_⟩
  intro i
  change b i + (size (words i) + f i) ≤ b i + size (words i) + size (Code.tally (f i))
  rw [size_tally, tally_length]
  omega

/-- Emit two computed fields in order. Only linear rescans of the emitted
fields are needed to place the pair in its specified order. -/
theorem pair {f : I → A} {g : I → B} (hf : Mint r f) (hg : Mint r g) : Mint r (fun i => (f i,g i)) := by
  obtain ⟨a,da,ca⟩ := hf
  obtain ⟨b,db,cb⟩ := hg
  refine ⟨_,(r.gauge.add da).add db, ?_⟩
  have left := (Task.copy r.header).compose (ca.left r.header)
  have cmd := left.compose (cb.right (send ∘ f))
  apply cmd.bound 2
  intro i
  change (r.header i).count + (a i + size (f i)) + (size (f i) + (b i + size (g i))) + 1 ≤
    2 * ((r.header i).count + a i + b i + size (f i,g i) + 1)
  simp only [size_prod]; omega

/-- One degree and one coefficient suffice uniformly. Time and space include
reading the initial descriptor, constructing its fields, and the entire output. -/
theorem bounded {f : I → A} (h : Mint r f) : ∃ d C : ℕ,
    let cost i := C*(r.scale i+1)^d + size (f i)
    Space.BoundedTask cost cost r.header (send ∘ f) := by
  obtain ⟨t,dt,cmd⟩ := h
  obtain ⟨d,C,hC⟩ := r.gauge.add dt
  refine ⟨d,C,?_⟩
  apply (Space.BoundedTask.of_time cmd).mono <;> intro i <;> have := hC i <;> dsimp only at * <;> omega

end Mint
end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
