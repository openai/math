import OAI.ThreeFlat.Diagonal.TraceBankExecution
import OAI.ThreeFlat.Diagonal.TraceWordTests
import Mathlib.Tactic.DeriveFintype

namespace OAI
/-! # The local checks for one fetched RAM instruction -/

namespace ThreeFlat.Diagonal.TraceIssue

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceBanks TraceWords

variable {w p r k : ℕ}

inductive Tag where
  | tick | left | right | read | write | accept | result
  deriving DecidableEq

instance : Fintype Tag :=
  ⟨{.tick,.left,.right,.read,.write,.accept,.result}, by intro t; cases t <;> simp⟩

/-- A local proposal records either a transition and its successor, or its terminal word. -/
inductive Proposal (w : ℕ) (C : Type*) where
  | move (e : Event w) (after : C)
  | halt (result : Option (Word w))

def Proposal.tag {C : Type*} : Proposal w C → Tag
  | .move .tick _ => .tick
  | .move (.choice false) _ => .left
  | .move (.choice true) _ => .right
  | .move (.read ..) _ => .read
  | .move (.write ..) _ => .write
  | .halt none => .accept
  | .halt (some _) => .result

def Proposal.after {C : Type*} (s : C) : Proposal w C → C
  | .move _ t => t
  | .halt _ => s

def Proposal.address {C : Type*} : Proposal w C → Word w
  | .move (.read a _) _ | .move (.write a _) _ => a
  | _ => 0

def Proposal.data {C : Type*} : Proposal w C → Word w
  | .move (.read _ v) _ | .move (.write _ v) _ | .halt (some v) => v
  | _ => 0

/-- A legal instruction row follows a native opcode, including a read's continuation
applied to the actual word recorded at that row. -/
def Follows {C : Type*} (a : CallAction w C) (q : Proposal w C) : Prop :=
  match a with
  | .localStep s => q = .move .tick s
  | .branch next => ∃ b, q = .move (.choice b) (next b)
  | .read addr next => ∃ v, q = .move (.read addr v) (next v)
  | .write addr v next => q = .move (.write addr v) next
  | .finish res => q = .halt res
  | .reject => False

/-- Arithmetic and comparison outputs are addressed by instruction slot. Other
inputs come from the two adjacent snapshots and the proposed event. -/
inductive Port (w p r : ℕ) where
  | pc (i : Fin p) | nextPC (i : Fin p) | tag (t : Tag)
  | state (j : Fin w) | nextState (j : Fin w)
  | reg (i : Fin r) (j : Fin w) | nextReg (i : Fin r) (j : Fin w)
  | address (j : Fin (w+1)) | data (j : Fin (w+1))
  | alu (i : Fin p) (j : Fin w) | cmp (i : Fin p)
  deriving DecidableEq, Fintype

def aluWord (pub : Fin k → Word w) (s : Snapshot w p r) : Instr w p r k → Word w
  | .constant _ v _ => v
  | .publicWord _ j _ => pub j
  | .binary op _ x y _ => op.eval (s.reg x) (s.reg y)
  | _ => 0

def compareBit (s : Snapshot w p r) : Instr w p r k → Bool
  | .jumpEq x y .. => decide (s.reg x = s.reg y)
  | .jumpLt x y .. => decide (s.reg x < s.reg y)
  | _ => false

def valuation (M : Machine w p r k) (s : Snapshot w p r)
    (q : Proposal (w+1) (Snapshot w p r)) : Port w p r → Bool
  | .pc i => decide (s.pc = i)
  | .nextPC i => decide ((q.after s).pc = i)
  | .tag t => decide (q.tag = t)
  | .state j => bits s.persistent j
  | .nextState j => bits (q.after s).persistent j
  | .reg i j => bits (s.reg i) j
  | .nextReg i j => bits ((q.after s).reg i) j
  | .address j => bits q.address j
  | .data j => bits q.data j
  | .alu i j => bits (aluWord M.publicData s (M.code i)) j
  | .cmp i => compareBit s (M.code i)

abbrev E (w p r : ℕ) := Expr (Port w p r)

def vr (i : Fin r) (j : Fin w) : E w p r := .input (.reg i j)
def vpc (i : Fin p) : E w p r := .input (.nextPC i)
def tag (t : Tag) : E w p r := .input (.tag t)
def vst (j : Fin w) : E w p r := .input (.state j)
def stateOk : E w p r := sameWord (fun j => .input (.nextState j)) vst
def regOk (v : Fin r → Fin w → E w p r) : E w p r :=
  allBits fun i => sameWord (fun j => .input (.nextReg i j)) (v i)
def go (pc : E w p r) (regs : Fin r → Fin w → E w p r) : E w p r :=
  .and pc (.and stateOk (regOk regs))
def put (next : Fin p) (dst : Fin r) (v : Fin w → E w p r) : E w p r :=
  go (vpc next) (Function.update vr dst v)
def tick (next : Fin p) (dst : Fin r) (v : Fin w → E w p r) : E w p r :=
  .and (tag .tick) (put next dst v)
def addrOk (privateBank : Bool) (i : Fin r) : E w p r :=
  sameWord (fun j => .input (.address j)) (Fin.snoc (vr i) (.const privateBank))
def dataOk (i : Fin r) : E w p r :=
  sameWord (fun j => .input (.data j)) (Fin.snoc (vr i) (.const false))
def load (bank : Bool) (dst addr : Fin r) (next : Fin p) : E w p r :=
  .and (tag .read) (.and (addrOk bank addr) (put next dst fun j => .input (.data j.castSucc)))
def store (bank : Bool) (addr src : Fin r) (next : Fin p) : E w p r :=
  .and (tag .write) (.and (addrOk bank addr) (.and (dataOk src) (go (vpc next) vr)))

/-- Test one statically decoded instruction against adjacent rows. The arithmetic
result for slot `i` is shared by all bit checks that refer to it. -/
def instruction (_pub : Fin k → Word w) (i : Fin p) : Instr w p r k → Expr (Port w p r)
  | .constant dst _ n | .publicWord dst _ n => tick n dst (fun j => .input (.alu i j))
  | .stateWord dst n => tick n dst vst
  | .copy dst src n => tick n dst (vr src)
  | .binary _ dst _ _ n => tick n dst (fun j => .input (.alu i j))
  | .loadPrivate dst addr n => load true dst addr n
  | .storePrivate addr src n => store true addr src n
  | .jumpEq _ _ yes no | .jumpLt _ _ yes no =>
    .and (tag .tick) (go (Expr.mux (.input (.cmp i)) (vpc yes) (vpc no)) vr)
  | .choose yes no =>
    .or (.and (tag .left) (go (vpc no) vr)) (.and (tag .right) (go (vpc yes) vr))
  | .readExternal dst addr n => load false dst addr n
  | .writeExternal addr src n => store false addr src n
  | .returnState src => .and (tag .result) (dataOk src)
  | .accept => tag .accept
  | .reject => .const false

/-- The counter lookup and all local checks for a single machine. -/
def issue (M : Machine w p r k) : Expr (Port w p r) :=
  TraceFetch.fetch (fun i => .input (.pc i)) (fun i => instruction M.publicData i (M.code i))

end ThreeFlat.Diagonal.TraceIssue

end OAI
