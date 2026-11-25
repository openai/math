import OAI.Computability.BorderVNP.TeamContractionLayout
import OAI.Computability.BorderVNP.TeamContractionReplay

/-! # Signed team values as finite sums over actual replay leaves

One fixed table is compiled once, before the input length is chosen. Each copy of the
universal processor observes its own actual program prefix and data. At any sufficiently
large common length the signed team value is the finite sum of products of terminal
weights over one interior assignment and one exact physical replay leaf per processor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP RAMTape UniversalMachine Filter
open scoped BigOperators Classical

variable {R r t d link inner n : ℕ} {Edge : Type} {K Q : Type}
variable [DecidableEq K] [Fintype K] [Fintype Q]

private theorem list_input (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Edge → Bool) (u : Fin (R+1)) (j : Fin r) :
    List.ofFn (G.word pin ext int u j) = G.input pin ext int u j :=
  G.read_bits pin ext (fun _ => int) u j

/-- The literal code in all sufficiently long physical slots has precisely the signed
stack value of its own input, including that code and its complete public literal. -/
theorem eventually_site_value (input : K) (u : ℕ) (hu : 1 ≤ u) (clock : 2*(u+2)+1 ≤ 100)
    (C : StackCode K Q) (negative : Q → Bool) (start : Q) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r t d link inner : ℕ) (Edge : Type)
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix (TeamClocked.machine input u C negative start) →
      ∀ pin ext int team j, signedCount (G.word pin ext int team j) =
        TeamStack.paths C negative (n^u) start
          (StackCompiler.labeledInput input (G.input pin ext int team j)) := by
  filter_upwards [TeamClocked.eventually_prefix_value input u hu clock C negative start] with n compiled
  intro R r t d link inner Edge G hg pin ext int team j
  let word := G.word pin ext int team j
  let raw := G.input pin ext int team j
  let payload := raw.drop G.program.length
  have heq : raw = G.program ++ payload := by simp [payload,raw,Wiring.input,List.append_assoc]
  have hraw : List.ofFn word = G.program ++ payload := (list_input ..).trans heq
  have hlen : (G.program ++ payload).length = n := by rw [← hraw,List.length_ofFn]
  have hc := compiled payload (by simpa only [← hg] using hlen)
  rw [← hg, ← hraw] at hc
  have hout : raw = List.ofFn word := (list_input ..).symm
  change signedCount word = TeamStack.paths C negative (n^u) start (StackCompiler.labeledInput input raw)
  rw [hout]
  simpa only [signedCount, List.ofFn_get, List.length_ofFn, List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self]
    using hc

/-- Finite family of local replay leaves, indexed by each processor's own consumed
choices and terminal sign for the specified interior links. -/
def physicalLeaves (G : Wiring R r t d link inner n Edge) (input : K) (C : StackCode K Q)
    (negative : Q → Bool) (start : Q) (u : ℕ) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Edge → Bool) (team : Fin (R+1)) (j : Fin r) :=
  Replay.leaves C negative (n^u) start (StackCompiler.labeledInput input (G.input pin ext int team j))

/-- Reindex the team's actual universal coefficients by independent local accepting
replays. The one common length threshold works for all numbers of processors, shared
wire types, assigned links, and live pins. -/
theorem eventually_replay_value (input : K) (u : ℕ) (hu : 1 ≤ u) (clock : 2*(u+2)+1 ≤ 100)
    (C : StackCode K Q) (negative : Q → Bool) (start : Q) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix (TeamClocked.machine input u C negative start) →
      ∀ pin ext team, G.value pin ext team =
        ∑ int : Edge → Bool,
          ∑ leaves : (j : Fin r) → ↥(physicalLeaves G input C negative start u pin ext int team j),
            ∏ j, TeamTape.haltWeight true (leaves j).val.2 := by
  filter_upwards [eventually_site_value input u hu clock C negative start] with n atLength
  intro R r t d link inner Edge _ G hG pin ext team
  unfold Wiring.value
  apply Finset.sum_congr rfl
  intro int _
  refine Eq.trans ?_ (Fintype.prod_sum (fun j (z : ↥(physicalLeaves G input C negative start u pin ext int team j)) =>
    TeamTape.haltWeight true z.val.2))
  apply Finset.prod_congr rfl
  intro j _
  rw [atLength _ _ _ _ _ _ _ G hG,Replay.paths_eq_sum]
  exact (Finset.sum_coe_sort (physicalLeaves ..) (fun x => TeamTape.haltWeight true x.2)).symm

end TeamContraction

end BorderVNP
end Computability
end OAI
