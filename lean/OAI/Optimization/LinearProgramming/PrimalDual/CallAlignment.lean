import OAI.Optimization.LinearProgramming.PrimalDual.TraceWindows

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace SubroutineCalls

open RAM CallSegments

def erase : Part → Phase
  | .embedded pc ret dims xs valid tag => .guest ⟨pc,ret⟩ dims xs valid tag
  | _ => .outside

def Separated (p : Program) (first second : Site) : Part → Prop
  | .fixed pc b => ∀ q, pc ≤ q → q < pc+b.size → ¬ first.Inside p q ∧ ¬ second.Inside p q
  | .terminal pc b _ => ∀ q, pc ≤ q → q < pc+b.size+1 → ¬ first.Inside p q ∧ ¬ second.Inside p q
  | .embedded pc ret _ _ _ tag => ret tag ≠ pc

/-- Re-index each consecutive block against the actual clock of the full trace.
Ordinary pieces prove exclusion from both sites. Guest pieces cover exactly
the slice bounded by the preceding and following pieces. -/
theorem aligned {host guest : Program} {first second : Site} {H U k n off : ℕ}
    {s x z : State ℚ} {tr : Fin (k+1) → State ℚ} {ps : List Part}
    (full : Trace host s k tr) (wide : H ≤ U) (joined : Joined host guest H ps x n z)
    (startEq : x = stateAt tr off) (fit : off+n ≤ k) (safe : ∀ a ∈ ps, Separated guest first second a) :
    OnTrace host guest first second U tr off (ps.map erase) (off+n) := by
  induction joined generalizing off with
  | nil _ =>
    exact OnTrace.nil fit
  | @cons part ps x y z m n one _ ih =>
    have fits : off+m ≤ k := by omega
    have middle := end_after full startEq fits one.execution
    have next := ih (off:=off+m) middle (by omega) (fun a ha => safe a (List.mem_cons_of_mem _ ha))
    have allowed := safe part List.mem_cons_self
    rw [← Nat.add_assoc]
    cases one with
    | fixed placed work =>
      have ranges := block_range_on full startEq fits placed work
      exact .outside fits (fun i => allowed _ (ranges i).1 (ranges i).2) next
    | embedded work => exact .guestRun (embedded_on full startEq fits wide allowed work) next
    | terminal placed work =>
      have ranges := terminal_range_on full startEq fits placed work
      exact .outside fits (fun i => allowed _ (ranges i).1 (ranges i).2) next

end SubroutineCalls
end PrimalDual
end LinearProgramming
end Optimization
end OAI
