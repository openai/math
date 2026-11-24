import OAI.Computability.VPVNP.PairSimulationTerminalSiteLinear

/-!
# The final-site ordinal guard and DFS entry

The persistent word selects a final vertex. Its row address and the endpoint
array heads are read from the header in the pair workspace. The private
stack is initialized with just that vertex's descriptor before entering the
geometry initializer. The flush continuation returns the next ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalSiteStart

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Form the pair-workspace header, then fetch the final vertex count. -/
def pre : List Line :=
  [.lit (dfs 3) 1, .pub (saved 4) 2, .pub (work 0) 7,
   .bin .shiftLeft (work 0) (dfs 3) (work 0), .bin .mul (work 0) (work 0) (work 0),
   .bin .add (saved 4) (saved 4) (work 0), .lit (work 0) 16, .bin .add (work 0) (work 0) (work 0),
   .bin .sub (saved 4) (saved 4) (work 0), .state (saved 2),
   .lit (work 0) 7, .bin .add (work 0) (saved 4) (work 0), .read (saved 5) (work 0)]

private def field (i : Fin 32) (dst : Reg) : List Line :=
  [.lit (work 0) i, .bin .add (work 0) (saved 4) (work 0), .read dst (work 0)]

/-- Fetch the endpoint array heads, form the root row, and store its address
as the only pending DFS visit. -/
def boot : List Line :=
  field 6 (saved 3) ++ field 8 (saved 6) ++ field 9 (saved 7) ++ field 10 (saved 8) ++
  field 11 (saved 9) ++ field 13 (saved 10) ++ field 14 (saved 0) ++ field 15 (work 1) ++
  [.bin .mul (work 1) (work 1) (saved 2), .bin .add (saved 3) (saved 3) (work 1),
   .pub (dfs 6) 6, .bin .sub (dfs 5) (dfs 6) (dfs 3), .store (dfs 5) (saved 3)]

/-- Instruction labels for the site ordinal guard, initialization of its DFS root and the flush
continuation that returns the next ordinal. -/
inductive Stage where
  | pre (i : Fin 13) | equal | less | accept | reject | boot (i : Fin 29)
  | increment | unit | add | finish
  deriving DecidableEq, Fintype

/-- First instruction of the site guard, where the bootstrap begins preparing the header and
ordinal comparison. -/
abbrev entry : Stage := .pre 0

/-- Resolves the next position in a straight-line block to its instruction label, using the
supplied continuation at the position just past the block. -/
def target {n : ℕ} (label : Fin n → Fin p) (done : Fin p) (i : Fin (n+1)) : Fin p :=
  if hi : i.val < n then label ⟨i.val, hi⟩ else done

/-- Relocate the site entry and the flush continuation into the finite vertex table. -/
def instruction (pc : Stage → Fin p) (reg : Reg → Fin r) (pub : Fin 11 → Fin k) (geometry : Fin p) :
    Stage → Instr w p r k
  | .pre i => Line.emit reg pub (target (pc ∘ Stage.pre) (pc .equal) i.succ) pre[i]
  | .equal => .jumpEq (reg (saved 2)) (reg (saved 5)) (pc .accept) (pc .less)
  | .less => .jumpLt (reg (saved 2)) (reg (saved 5)) (pc (.boot 0)) (pc .reject)
  | .accept => .accept
  | .reject => .reject
  | .boot i => Line.emit reg pub (target (pc ∘ Stage.boot) geometry i.succ) boot[i]
  | .increment => .stateWord (reg (saved 2)) (pc .unit)
  | .unit => .constant (reg (work 0)) 1 (pc .add)
  | .add => .binary .add (reg (saved 2)) (reg (saved 2)) (reg (work 0)) (pc .finish)
  | .finish => .returnState (reg (saved 2))

theorem resize_instruction (pc : Stage → Fin p) (reg : Reg → Fin r) (pub : Fin 11 → Fin k)
    (geometry : Fin p) (i : Stage) :
    (instruction (w := 5) pc reg pub geometry i).resize w = instruction pc reg pub geometry i := by
  cases i <;> first | exact Line.resize_emit .. | rfl

/-- Requires all bootstrap and flush instructions to be installed at their stage labels with
the specified registers, public ports and geometry entry. -/
def Linked (M : Machine w p r k) (pc : Stage → Fin p) (reg : Reg → Fin r)
    (pub : Fin 11 → Fin k) (geometry : Fin p) : Prop :=
  ∀ j, M.code (pc j) = instruction pc reg pub geometry j

/-- Classifies guard and initialization labels as bootstrap rows and the four ordinal-return
instructions as flush rows, allowing each part to be linked separately. -/
def Stage.bootstrap : Stage → Bool
  | .increment | .unit | .add | .finish => false
  | _ => true

/-- Only entry and guard rows are required before transferring to the geometry code. -/
def StartLinked (M : Machine w p r k) (pc : Stage → Fin p) (reg : Reg → Fin r)
    (pub : Fin 11 → Fin k) (geometry : Fin p) : Prop :=
  ∀ j, j.bootstrap = true → M.code (pc j) = instruction pc reg pub geometry j

/-- The flush continuation uses exactly its four designated labels. -/
def FinishLinked (M : Machine w p r k) (pc : Stage → Fin p) (reg : Reg → Fin r)
    (pub : Fin 11 → Fin k) (geometry : Fin p) : Prop :=
  ∀ j, j.bootstrap = false → M.code (pc j) = instruction pc reg pub geometry j

/-- The numerical header address before interpreting its words. -/
def headerWord (pub : Fin 11 → Word w) : Word w :=
  let R := BinaryOp.shiftLeft.eval 1 (pub 7)
  pub 2 + R * R - (16 + 16)

/-- On well-sized words the computed header is the address allocated by the terminal calendar. -/
theorem headerWord_eq (pub : Fin 11 → Word w) (base r : ℕ) (hb : pub 2 = (base : Word w))
    (hr : (pub 7).val = r) (hrw : r < w) (h32 : 32 ≤ base + 2^r * 2^r) :
    headerWord pub = ((base + 2^r*2^r-32 : ℕ) : Word w) := by
  have one : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hp : BinaryOp.shiftLeft.eval (1 : Word w) (pub 7) = ((2^r : ℕ) : Word w) := by
    simp only [BinaryOp.eval,hr,ite_eq_left hrw,one,Nat.one_shiftLeft,Fin.ofNat_eq_cast]
  rw [headerWord, hp, hb, Nat.cast_sub h32,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

/-- Header-relative physical read and the preceding address instructions. -/
def fieldTrace (m : Memory w) (h : Word w) (i : ℕ) : List (Event w) :=
  [.tick, .tick, .read (h + (i : Word w)) (m (h + (i : Word w)).val)]

/-- Trace before the site ordinal comparison, with ten setup ticks followed by address
calculation and the external read of the final site count at header offset seven. -/
def guardTrace (m : Memory w) (h : Word w) : List (Event w) :=
  List.replicate 10 .tick ++ fieldTrace m h 7

/-- Trace for an active site's DFS initialization. Eight header field reads supply the root and
layout data, followed by five ticks that compute the root address and push it onto the
private stack. -/
def bootTrace (m : Memory w) (h : Word w) : List (Event w) :=
  [6,8,9,10,11,13,14,15].flatMap (fieldTrace m h) ++ List.replicate 5 .tick

/-- Bank before branching on the ordinal. -/
structure GuardReady (h st : Word w) (m : Memory w) (b : Reg → Word w) : Prop where
  one : b (dfs 3) = 1
  header : b (saved 4) = h
  ordinal : b (saved 2) = st
  sites : b (saved 5) = m (h+7).val

/-- The local bank passed to the private geometry initializer. -/
structure BootReady (n h st : Word w) (m : Memory w) (b : Reg → Word w) : Prop extends GuardReady h st m b where
  root : b (saved 3) = m (h+6).val + m (h+15).val * st
  slots : b (saved 6) = m (h+8).val
  widths : b (saved 7) = m (h+9).val
  incoming : b (saved 8) = m (h+10).val
  prefixPtr : b (saved 9) = m (h+11).val
  wires : b (saved 10) = m (h+13).val
  roleOffset : b (saved 0) = m (h+14).val
  top : b (dfs 5) = n-1
  stackEnd : b (dfs 6) = n

end PairSimulation.TerminalSiteStart

end VPVNP
end Computability
end OAI
