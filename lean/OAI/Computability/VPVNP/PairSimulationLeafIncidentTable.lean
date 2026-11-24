import OAI.Computability.VPVNP.PairSimulationLeafIncidentMachine

/-!
# The fixed instruction image and virtual clock of the incident loader
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentMachine

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout

variable {W D H w n : ℕ}

/-- Standalone machine states, including the return location. -/
abbrev PC := Option Stage

/-- Numerical instruction address for an incident-loader label. -/
noncomputable def rowPC (s : Stage) : Fin (Fintype.card PC) := Fintype.equivFin PC (some s)
/-- Numerical address of the standalone accepting return. -/
noncomputable def returnPC : Fin (Fintype.card PC) := Fintype.equivFin PC none

/-- The same opcode image is instantiated at every host word width. -/
noncomputable def template : Template (Fintype.card PC) 30 0 where
  literalWidth := 5
  entry := rowPC (.inl 0)
  code i := match (Fintype.equivFin PC).symm i with
    | some s => instruction rowPC (Function.Embedding.refl _) returnPC s
    | none => .accept

theorem template_linked (pub : Fin 0 → Word W) :
    Linked (template.instantiate W pub) rowPC (Function.Embedding.refl _) returnPC := by
  intro s
  simpa only [Template.instantiate, template, rowPC, Equiv.symm_apply_apply] using
    resize_instruction (k := 0) (W := W) rowPC (Function.Embedding.refl _) returnPC s

/-- A numerical bound on the actual native instruction count that is
independent of the four supplied half-wire strings. -/
theorem ticks_le (v : Site D) (H w : ℕ) :
    ticks v H w ≤ 80*w+6*D+53+layerCount D*(10*blockBits H w+14) := by
  have ha (l : Layer D) : LeafSortFields.advanceTicks l ≤ 5 := by
    unfold LeafSortFields.advanceTicks
    split_ifs <;> decide
  have sum : LeafSortFields.streamTicks D H w 0 (layerCount D) (by simp) ≤
      layerCount D*(10*blockBits H w+14) := by
    unfold LeafSortFields.streamTicks
    rw [List.sum_ofFn]
    calc
      _ ≤ ∑ _ : Fin (layerCount D), (10*blockBits H w+14) :=
        Finset.sum_le_sum fun i _ => by have := ha ((layerEquiv D).symm i); simpa only [Nat.zero_add] using
          (Nat.add_le_add_left this (10*blockBits H w+9))
      _ = _ := by simp
  have := LeafSuccessorFields.ticks_le v w
  unfold ticks LeafIncidentCore.ticks
  omega

/-- The loader occupies at most a fifth-power portion of the live private
clock for the parameters of the virtual auxiliary processor. -/
theorem ticks_le_of_budget {e : ℕ} (v : Site D) (bud : ProcessorBudget n D e w) (hn : 1024 ≤ n) :
    ticks v (2^e) w ≤ n^5 := by
  have hD : D+1 ≤ n := by have := bud.phase_le; omega
  have lc : layerCount D ≤ n^2 := by
    rw [layerCount,Nat.choose_two_right,pow_two]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul hD (by omega))
  have hb : blockBits (2^e) w ≤ 40*n^2 := calc
    _ ≤ 4*(2*n)*5*n := by unfold blockBits; gcongr <;> first | exact bud.word_le | exact bud.bucket_le
    _ = _ := by ring
  have n2 := Nat.one_le_pow 2 n (show 1 ≤ n by omega)
  have p := Nat.mul_le_mul lc (show 10*blockBits (2^e) w+14 ≤ 414*n^2 by omega)
  have hn4 : n ≤ n^4 := Nat.le_self_pow (by decide) n
  have he : n^2*(414*n^2) = 414*n^4 := by ring
  have hw := bud.word_le
  have hd : D ≤ n := by omega
  have final : 553*n^4 ≤ n^5 := by rw [pow_succ' n 4]; exact Nat.mul_le_mul_right _ (by omega)
  have bound := ticks_le v (2^e) w
  omega

end PairSimulation.LeafIncidentMachine

end VPVNP
end Computability
end OAI
