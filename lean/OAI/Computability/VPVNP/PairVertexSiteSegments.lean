import OAI.Computability.VPVNP.PairVertexReturns
import OAI.Computability.VPVNP.PairSimulationTerminalSiteRun

/-! # Installing the actual ordinal guard and persistent return in the vertex image -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM TerminalSiteStart DFS
open scoped Fin.CommRing

/-- The entry guard, exit tests, and site bootstrap labels installed before the geometry
segment. -/
inductive BootstrapLabel where
  | pre (i : Fin 13) | equal | less | accept | reject | boot (i : Fin 29)
  deriving DecidableEq, Fintype

/-- Interpret a local bootstrap instruction label as its stage in the terminal site program. -/
def BootstrapLabel.stage : BootstrapLabel → Stage
  | .pre i => .pre i
  | .equal => .equal
  | .less => .less
  | .accept => .accept
  | .reject => .reject
  | .boot i => .boot i

/-- Map a terminal site stage into the bootstrap's program counters, using the supplied
fallback for stages outside this block. -/
def bootstrapPC {p : ℕ} (pc : BootstrapLabel → Fin p) (unused : Fin p) : Stage → Fin p
  | .pre i => pc (.pre i)
  | .equal => pc .equal
  | .less => pc .less
  | .accept => pc .accept
  | .reject => pc .reject
  | .boot i => pc (.boot i)
  | .increment | .unit | .add | .finish => unused

/-- Resolve bootstrap registers from the DFS, saved-operand, and local working banks. -/
def bootstrapReg {r : ℕ} (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r) (work : Fin 3 ↪ Fin r) :
    TerminalSiteStart.Reg → Fin r := Sum.elim dfs (Sum.elim saved work)

/-- Number the finite set of bootstrap labels to place the site-entry instructions in a
segment. -/
noncomputable abbrev bootLabels := Fintype.equivFin BootstrapLabel

/-- Install the terminal site guard and bootstrap instructions with three local working
registers before entering geometry. -/
noncomputable def bootstrapSegment : Segment where
  count := Fintype.card BootstrapLabel
  privateRegs := 3
  entry := bootLabels (.pre 0)
  row pc dfs saved work geometry i := TerminalSiteStart.instruction
    (bootstrapPC (pc ∘ bootLabels) geometry) (bootstrapReg dfs saved work) id geometry (bootLabels.symm i).stage

/-- The four return rows reload the genuine persistent ordinal, increment
it and return the resulting word. -/
def finishSegment : Segment where
  count := 4
  privateRegs := 3
  entry := 0
  row pc _ saved work _ :=
    ![.stateWord (saved ordinal) (pc 1),.constant (work 0) 1 (pc 2),
      .binary .add (saved ordinal) (saved ordinal) (work 0) (pc 3),.returnState (saved ordinal)]

/-- Assign concrete segments to all named vertex parts, including the fixed bootstrap and
finishing blocks. -/
noncomputable def segments (geometry rootFields leaf shrink refresh : Segment) : Part → Segment
  | .bootstrap => bootstrapSegment
  | .geometry => geometry
  | .rootFields => rootFields
  | .leaf => leaf
  | .shrink => shrink
  | .refresh => refresh
  | .finish => finishSegment

variable {geometry rootFields leaf shrink refresh : Segment} {p r W : ℕ}
  (A : Placement (segments geometry rootFields leaf shrink refresh) p r)
  (M : Machine W p r 11)

/-- Host program counter of a terminal site-bootstrap label in the assembled vertex. -/
noncomputable def sitePC (j : BootstrapLabel) := A.stage .bootstrap (bootLabels j)
/-- Host program counter of a local finishing instruction in the assembled vertex. -/
noncomputable def finishPC (i : Fin 4) := A.stage .finish i

theorem bootstrap_linked (linked : Contains A M) (j : BootstrapLabel) :
    M.code (sitePC A j) = TerminalSiteStart.instruction
      (bootstrapPC (sitePC A) (A.entry .geometry)) (bootstrapReg A.dfs A.saved (A.localRegs .bootstrap))
      id (A.entry .geometry) j.stage := by
  apply (stage_linked A M linked .bootstrap (bootLabels j)).trans
  change (TerminalSiteStart.instruction (bootstrapPC (sitePC A) (A.entry .geometry)) _
    id (A.entry .geometry) (bootLabels.symm (bootLabels j)).stage).resize W = _
  rw [Equiv.symm_apply_apply,TerminalSiteStart.resize_instruction]

theorem finish_linked (linked : Contains A M) (i : Fin 4) :
    M.code (finishPC A i) = ![Instr.stateWord (A.saved ordinal) (finishPC A 1),
      .constant (A.localRegs .finish (0 : Fin 3)) 1 (finishPC A 2),
      .binary .add (A.saved ordinal) (A.saved ordinal) (A.localRegs .finish (0 : Fin 3)) (finishPC A 3),
      .returnState (A.saved ordinal)] i := by
  apply (stage_linked A M linked .finish i).trans
  fin_cases i <;> rfl

/-- The bootstrap and return fragments use their own temporaries, alongside
the same DFS and stable register banks. -/
noncomputable def siteBank (part : Part)
    (localMap : Fin 3 ↪ Fin ((segments geometry rootFields leaf shrink refresh) part).privateRegs) :
    TerminalSiteStart.Reg ↪ Fin r :=
  let work := (localMap.trans (Function.Embedding.sigmaMk (β := fun j => Fin ((segments geometry rootFields leaf shrink refresh) j).privateRegs) part)).trans Function.Embedding.inr
  (Function.Embedding.sumMap (Function.Embedding.refl (Fin 9))
    (Function.Embedding.sumMap (Function.Embedding.refl Saved) work)).trans A.reg

/-- Register assignment for site-bootstrap instructions using the bootstrap segment's three
work registers. -/
noncomputable abbrev bootBank := siteBank A .bootstrap (Function.Embedding.refl (Fin 3))
/-- Register assignment for final site-return instructions using the finishing segment's three
work registers. -/
noncomputable abbrev finishBank := siteBank A .finish (Function.Embedding.refl (Fin 3))

/-- Resolve the terminal site's increment, unit, add, and return stages to the installed
finishing code. -/
noncomputable def returnPC : Stage → Fin p
  | .increment => finishPC A 0
  | .unit => finishPC A 1
  | .add => finishPC A 2
  | .finish => finishPC A 3
  | _ => A.core .accept

theorem boot_startLinked (linked : Contains A M) :
    TerminalSiteStart.StartLinked M (bootstrapPC (sitePC A) (A.entry .geometry)) (bootBank A) id (A.entry .geometry) := by
  have eqn : (bootBank A : TerminalSiteStart.Reg → Fin r) = bootstrapReg A.dfs A.saved (A.localRegs .bootstrap) := by
    funext j
    obtain x | s | w := j <;> rfl
  rw [eqn]
  intro j hj
  cases j <;> first | contradiction | (solve | apply bootstrap_linked A M linked (.pre _)) |
    (solve | apply bootstrap_linked A M linked .equal) | (solve | apply bootstrap_linked A M linked .less) |
    (solve | apply bootstrap_linked A M linked .accept) | (solve | apply bootstrap_linked A M linked .reject) |
    (solve | apply bootstrap_linked A M linked (.boot _))

theorem finish_finishLinked (linked : Contains A M) :
    TerminalSiteStart.FinishLinked M (returnPC A) (finishBank A) id (A.core .accept) := by
  intro j hj
  cases j <;> first | contradiction | exact finish_linked A M linked 0 | exact finish_linked A M linked 1 |
    exact finish_linked A M linked 2 | exact finish_linked A M linked 3

theorem finish_terminal (linked : Contains A M) (c : Config W p r) (m : Memory W) (bits : List Bool)
    (here : c.pc = A.entry .finish) : Returns M c m bits ↔ bits = [] :=
  TerminalSiteStart.finish_terminal (finish_finishLinked A M linked) m c here bits

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
