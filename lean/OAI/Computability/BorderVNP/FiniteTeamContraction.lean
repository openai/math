import OAI.Computability.BorderVNP.FiniteContraction
import OAI.Computability.BorderVNP.TeamContractionLayout
import OAI.Computability.BorderVNP.TeamContractionHistory

/-! # Field-valued processor teams with the physical diagonal wiring

The live contraction uses the manuscript's literal prefix, private and shared
link positions, and its zero-clamped slots. The same physical assignment can
be read as the ports of the repeated batch network. On each accepting native
trace, field weights also survive the unique extension to the checked team
history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldTeam

open TeamContraction VPVNP.RAMTape VPVNP.UniversalMachine Diagonal Crossing Packing Filter
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable {R r t d link inner n : ℕ} {Edge : Type}
variable (G : Wiring R r t d link inner n Edge)

/-- The value of the physical field processors in one team at fixed exterior data. -/
noncomputable def fieldValue [Fintype Edge] (F : Type*) [Field F] [Fintype F]
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (team : Fin (R+1)) : F :=
  ∑ int : Edge → Bool, ∏ j : Fin r, FPath.U F (G.word pin ext int team j)

/-- The actual physical contraction over all shared and interior bits. -/
noncomputable def fieldContraction [Fintype Edge] (F : Type*) [Field F] [Fintype F] (pin : Fin d → Bool) : F :=
  ∑ links : Layout.Wire R r link Edge → Bool, ∏ proc : Fin (R+1) × Fin r,
    FPath.U F (fun i => (G.slot proc i).read pin links)

/-- Reindex the physical assignments by shared bits and independent teams. -/
theorem fieldContraction_eq [Fintype Edge] (pin : Fin d → Bool) :
    fieldContraction G F pin = ∑ ext, ∏ team, fieldValue G F pin ext team := by
  let E := assignmentEquiv (R := R) (r := r) (link := link) (Edge := Edge)
  let total := fun links : Layout.Wire R r link Edge → Bool =>
    ∏ proc, FPath.U F (fun j => (G.slot proc j).read pin links)
  rw [show fieldContraction G F pin = ∑ p, total (E p) from (E.sum_comp total).symm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ext _
  rw [show (∏ u, fieldValue G F pin ext u) = ∑ ints : Fin (R+1) → Edge → Bool,
      ∏ u, ∏ j, FPath.U F (G.word pin ext (ints u) u j) from Fintype.prod_sum _]
  apply Finset.sum_congr rfl
  intro ints _
  dsimp only [total]
  rw [Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun j _ => congrArg (FPath.U F) (G.read_eq pin ext ints u j)

/-- Insert each physical processor word into the corresponding nested pack ports. -/
def packInputs {P : Type} {bits : P → ℕ} (b K : ℕ) : (h : ℕ) →
    (PackPorts Unit b K h → Ports bits) → Ports (packWidth bits b K h)
  | 0, word, p => word (p.1,()) p.2
  | h+1, word, p => packInputs b K h (fun i => word (p.1,i)) p.2

/-- Each original processor reads its own word after the nesting of parallel copies. -/
theorem copyPorts_packInputs {P : Type} {bits : P → ℕ} (b K h : ℕ)
    (words : PackPorts Unit b K h → Ports bits) (i : PackPorts Unit b K h) :
    FiniteDiagonal.copyPorts b K h (packInputs b K h words) i = words i := by
  induction h with
  | zero => rfl
  | succ h ih => exact ih (fun j => words (i.1,j)) i.2

/-- Reindex the actual live wiring into precisely the team copies of the packed
network. Subsequent substitution can now use its original terminal order. -/
theorem fieldContraction_eq_live [Fintype Edge] (b K h : ℕ) (e : PackPorts Unit b K h ≃ Fin (R+1))
    (pin : Fin d → Bool) :
    fieldContraction G F pin = FiniteDiagonal.live (F := F) (n := n) (r := r) (b := b) (K := K) h
      (fun links => packInputs b K h (fun team proc _ => (G.slot (e team,proc.1) proc.2).read pin links)) := by
  unfold fieldContraction FiniteDiagonal.live
  apply Finset.sum_congr (by ext z; simp)
  intro links _
  rw [Fintype.prod_prod_type]
  simp only [copyPorts_packInputs,FiniteDiagonal.tensorPower]
  exact (e.prod_comp (fun team => ∏ j, FPath.U F (fun i => (G.slot (team,j) i).read pin links))).symm

variable {K Q : Type} [Fintype K] [DecidableEq K] [Fintype Q]

/-- A fixed finite-field validator evaluated on each literal processor word. The
common threshold is independent of the team count, shared wires, and all bit values. -/
theorem eventually_site_value (input : K) (u : ℕ) (hu : 1 ≤ u) (clock : 2*(u+2)+1 ≤ 100)
    (C : StackCode K Q) (weight : Q → F) (start : Q) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r t d link inner : ℕ) (Edge : Type)
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix (FieldStack.clockedMachine input u C weight start) →
      ∀ pin ext int team j, FPath.U F (G.word pin ext int team j) =
        FieldStack.paths C weight (n^u) start (StackCompiler.labeledInput input (G.input pin ext int team j)) := by
  filter_upwards [FieldStack.eventually_prefix_value input u hu clock C weight start] with n compiled
  intro R r t d link inner Edge G hg pin ext int team j
  let word := G.word pin ext int team j
  let raw := G.input pin ext int team j
  let payload := raw.drop G.program.length
  have hl : List.ofFn word = raw := G.read_bits pin ext (fun _ => int) team j
  have heq : raw = G.program ++ payload := by simp [payload,raw,Wiring.input,List.append_assoc]
  have hraw := hl.trans heq
  have hlen : (G.program ++ payload).length = n := by rw [← hraw,List.length_ofFn]
  have hc := compiled payload (by simpa only [← hg] using hlen)
  rw [← hg,← hraw] at hc
  change FPath.U F word = FieldStack.paths C weight (n^u) start (StackCompiler.labeledInput input raw)
  rw [← hl]
  simpa only [FPath.U_eq_paths,List.ofFn_get,List.length_ofFn,List.get_ofFn,Fin.cast_cast,Fin.cast_eq_self] using hc

variable {w : ℕ} {S : Type*}

/-- The native field sum records a factor for each chronological processor event. -/
noncomputable def nativeValue (M : MachineInput w S) (b : Bounds r M.inputSize) (weight : TeamRAM.Event w → F) : F :=
  letI := Fintype.ofFinite (NativePath M b.ticks b.burst b.privateClock)
  ∑ p : NativePath M b.ticks b.burst b.privateClock, (p.val.map weight).prod

/-- Field sum over the independently checked histories, with the actual block boundaries. -/
noncomputable def historyValue (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w)
    (weight : TeamRAM.Event w → F) : F :=
  letI := Fintype.ofFinite (CheckedHistory M b place)
  ∑ t : CheckedHistory M b place, t.val.weight weight

omit [Fintype F] in
/-- Each path has exactly one checked history and preserves its field product. -/
theorem historyValue_eq_native (M : MachineInput w S) (b : Bounds r M.inputSize)
    (place : Placement b w) (weight : TeamRAM.Event w → F) :
    historyValue M b place weight = nativeValue M b weight := by
  unfold historyValue nativeValue
  apply Finset.sum_equiv (pathEquivHistory M b place).symm (by simp)
  intro t _
  exact t.property.1.weight_eq weight

end FieldTeam

end BorderVNP
end Computability
end OAI
