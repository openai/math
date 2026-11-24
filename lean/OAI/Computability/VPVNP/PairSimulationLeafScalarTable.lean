import OAI.Computability.VPVNP.PairSimulationLeafLoadedBank
import OAI.Computability.VPVNP.PairSimulationStackSpace

/-! # Finite scalar-startup template and its virtual-leaf clock -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafPortTable

open BurstRAM PrivateRAM RAMTape LeafStartup LeafRegisterBank StackMachine Filter

variable {K : Type} [Fintype K] [DecidableEq K] {k w : ℕ}

/-- The instruction labels of the scalar startup table together with one additional return
label. -/
abbrev PC (K : Type) := Label K ⊕ Unit

/-- The numbered program counter of a labeled allocation, staging or fill instruction in the
scalar startup template. -/
noncomputable def rowPC (a : Label K) : Fin (Fintype.card (PC K)) := Fintype.equivFin _ (.inl a)
/-- The numbered return label reached after the final scalar port in the standalone startup
template. -/
noncomputable def returnPC (K : Type) [Fintype K] : Fin (Fintype.card (PC K)) := Fintype.equivFin _ (.inr ())
/-- Assign the scalar-loader registers consecutive indices in the standalone startup template. -/
noncomputable def registers (K : Type) [Fintype K] (k : ℕ) :
    Reg K k ↪ Fin (Fintype.card (Reg K k)) := (Fintype.equivFin _).toEmbedding

/-- The code depends only on the static port set and assignment. Its inputs
are the caller's source words, the arena cursor and its runtime stride. -/
noncomputable def template (tag : K → Field k) (todo : List K) :
    Template (Fintype.card (PC K)) (Fintype.card (Reg K k)) 0 where
  literalWidth := 1
  entry := LeafPointers.next todo (fun a i => rowPC (.pointer a i)) (rowPC (.finish 0))
  code i := match (Fintype.equivFin (PC K)).symm i with
    | .inl l => instruction tag rowPC (registers K k) (returnPC K) todo l
    | .inr _ => .accept

theorem template_rows (tag : K → Field k) (todo : List K) (pub : Fin 0 → Word w) (l : Label K) :
    ((template tag todo).instantiate w pub).code (rowPC l) =
      instruction tag rowPC (registers K k) (returnPC K) todo l := by
  simpa [Template.instantiate,template,rowPC] using
    resize_instruction (w := w) (pubs := 0) tag rowPC (registers K k) (returnPC K) todo l

/-- The total instruction count for allocating three rows per port, finishing allocation in two
steps, and staging and writing every requested field. -/
def cost {d e : ℕ} (tag : K → Field k) (x : VirtualSite.Input d e w) (args : Fin k → Word w)
    (todo : List K) := 3*todo.length+2+(todo.map (ticks tag x args)).sum

omit [Fintype K] [DecidableEq K] in
theorem cost_le {d e B : ℕ} (tag : K → Field k) (x : VirtualSite.Input d e w) (args : Fin k → Word w)
    (todo : List K) (bound : ∀ a, (fieldBits x args (tag a)).length ≤ B) :
    cost tag x args todo ≤ 2+todo.length*(8+6*B) := by
  have per (a : K) : ticks tag x args a ≤ 5+6*B := by
    have h := Staging.length_le (scalarField (tag a))
    have hb : (scalarBank tag x args a).length ≤ B := by
      by_cases hi : tag a = .incident
      · simp [scalarBank,scalarField,hi,fieldBits]
      · simpa [scalarBank,scalarField,hi] using bound a
    unfold ticks
    omega
  have sum (ls : List K) : (ls.map (ticks tag x args)).sum ≤ ls.length*(5+6*B) := by
    induction ls with
    | nil => simp
    | cons a ls ih =>
      change ticks tag x args a + (ls.map (ticks tag x args)).sum ≤ (ls.length+1)*(5+6*B)
      rw [Nat.add_mul,Nat.one_mul,Nat.add_comm (ls.length*(5+6*B))]
      exact Nat.add_le_add (per a) ih
  unfold cost
  have h := sum todo
  rw [Nat.mul_add todo.length 8, Nat.mul_add todo.length 5] at *
  omega

theorem eventually_auxiliary_cost (r k : ℕ) (todo : List (LeafStartup.Port r k)) :
    ∀ᶠ n : ℕ in atTop, ∀ d e w (x : VirtualSite.Input d e w), ProcessorBudget n d e w →
      x.fuel ≤ n^10 → ∀ args : Fin k → Word w, cost LeafStartup.field x args todo ≤ n^14 := by
  filter_upwards [eventually_ge_atTop (max 128 todo.length)] with n hn
  intro d e w x bud hf args
  have h₁ : 1 ≤ n := by omega
  have h₁₂ := Nat.one_le_pow 12 n h₁
  have h₁₃ := Nat.one_le_pow 13 n h₁
  have h := cost_le LeafStartup.field x args todo (bank_length_le x r (by omega) bud hf args)
  have small : 8+6*n^12 ≤ 14*n^12 := by omega
  have big := Nat.mul_le_mul (show todo.length ≤ n by omega) small
  have heq : n*(14*n^12)=14*n^13 := by rw [pow_succ' n 12]; ring
  have hfinal : 16*n^13 ≤ n^14 := by rw [pow_succ' n 13]; exact Nat.mul_le_mul_right _ (by omega)
  omega

end PairSimulation.LeafPortTable

end VPVNP
end Computability
end OAI
