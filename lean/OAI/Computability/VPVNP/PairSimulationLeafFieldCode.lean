import OAI.Computability.VPVNP.PairSimulationLeafFieldSources

/-!
# Private RAM instructions that stage one scalar leaf field

Only the destination length, value, and one arithmetic temporary are
written. Source words occupy a fixed register bank shared by every field.
The field number and its operand register are selected by finite control.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup.Staging

open BurstRAM PrivateRAM PrimedCounter.GuessWord

/-- The three writable scalar-staging destinations holding the field length, field value and
arithmetic temporary. -/
inductive Out | len | value | tmp deriving DecidableEq
instance : Fintype Out := derive_fintype% _
/-- Named staging registers for the three outputs, constants and site geometry, and the virtual
machine's indexed public operands. -/
inductive Reg (k : ℕ)
  | out (i : Out) | zero | one | d | width | bucket | fuel | address | initial | header | operand (i : Fin k)
  deriving DecidableEq, Fintype

/-- A scalar-staging expression that copies one register or applies a binary word operation to
two registers. -/
inductive Rhs (k : ℕ)
  | copy (src : Reg k)
  | binary (op : BinaryOp) (a b : Reg k)

/-- One scalar-staging assignment, pairing a writable destination with the expression whose
word it receives. -/
abbrev Line (k : ℕ) := Out × Rhs k

variable {k w p r pubs : ℕ}

/-- The fixed assignments that compute a field's stack length and source word from the leaf's
geometry and cached operands. -/
def code : Field k → List (Line k)
  | .blank | .incident => [(.len,.copy .zero),(.value,.copy .one)]
  | .zeroWord => [(.len,.copy .width),(.value,.copy .zero)]
  | .address => [(.len,.copy .d),(.value,.copy .address)]
  | .addressWidth => [(.len,.copy .d),(.value,.copy .one)]
  | .width => [(.len,.copy .width),(.value,.copy .one)]
  | .slots => [(.len,.binary .add .bucket .bucket),(.len,.binary .add (.out .len) (.out .len)),(.value,.copy .one)]
  | .bucket => [(.len,.copy .bucket),(.value,.copy .one)]
  | .fuel => [(.len,.copy .fuel),(.value,.copy .one)]
  | .siteCredit => [(.len,.binary .add .bucket .bucket),(.len,.binary .sub (.out .len) .one),(.value,.copy .one)]
  | .choices => [(.tmp,.binary .add .bucket .bucket),(.len,.binary .add .fuel .width),
      (.len,.binary .mul (.out .tmp) (.out .len)),(.value,.copy .one)]
  | .cap => [(.value,.binary .shiftLeft .one .d),(.value,.binary .mul (.out .value) .bucket),(.len,.copy .width)]
  | .lower => [(.value,.binary .mul .address .bucket),(.len,.copy .width)]
  | .upper => [(.value,.binary .add .address .one),(.value,.binary .mul (.out .value) .bucket),(.len,.copy .width)]
  | .initial => [(.len,.copy .width),(.value,.copy .initial)]
  | .siteWord => [(.len,.copy .width),(.value,.copy .address)]
  | .header => [(.len,.copy .width),(.value,.copy .header)]
  | .operand i => [(.len,.copy .width),(.value,.copy (.operand i))]

theorem length_le (f : Field k) : (code f).length ≤ 4 := by cases f <;> simp [code]

/-- Compile a scalar-staging assignment to a host copy or binary instruction that jumps to the
supplied continuation. -/
def instruction (ports : Reg k ↪ Fin r) (next : Fin p) (line : Line k) : Instr w p r pubs :=
  match line.2 with
  | .copy src => .copy (ports (.out line.1)) (ports src) next
  | .binary op a b => .binary op (ports (.out line.1)) (ports a) (ports b) next

theorem resize_instruction (ports : Reg k ↪ Fin r) (next : Fin p) (l : Line k) :
    (instruction (w := 1) (pubs := pubs) ports next l).resize w = instruction ports next l := by
  obtain ⟨o,s⟩ := l
  cases s <;> rfl

/-- Evaluate a scalar-staging expression against the current named register values using
machine-word arithmetic. -/
def Rhs.eval (bank : Reg k → Word w) : Rhs k → Word w
  | .copy src => bank src
  | .binary op a b => op.eval (bank a) (bank b)

/-- Update the named destination register with the value of one staging assignment. -/
def applyLine (bank : Reg k → Word w) (l : Line k) : Reg k → Word w :=
  Function.update bank (.out l.1) (l.2.eval bank)

/-- Perform a staging assignment in the host register bank using the physical placement of its
source and destination registers. -/
def applyPhysical (ports : Reg k ↪ Fin r) (bank : Fin r → Word w) (l : Line k) : Fin r → Word w :=
  Function.update bank (ports (.out l.1)) (l.2.eval (bank ∘ ports))

theorem physical_at (ports : Reg k ↪ Fin r) (ls : List (Line k)) (bank : Fin r → Word w) :
    ls.foldl (applyPhysical ports) bank ∘ ports = ls.foldl applyLine (bank ∘ ports) := by
  induction ls generalizing bank with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    funext i
    by_cases he : i = .out l.1
    · subst i; simp [applyPhysical, applyLine]
    · simp [applyPhysical,applyLine,he,ports.injective.ne he]

theorem physical_outside (ports : Reg k ↪ Fin r) (ls : List (Line k)) (bank : Fin r → Word w)
    (j : Fin r) (h : ∀ o, j ≠ ports (.out o)) : ls.foldl (applyPhysical ports) bank j = bank j := by
  induction ls generalizing bank with
  | nil => rfl
  | cons l ls ih => simp only [List.foldl_cons, ih, applyPhysical, Function.update_of_ne (h l.1)]

/-- Each row makes an actual private step in the supplied parent table. -/
theorem run (M : Machine w p r pubs) (ports : Reg k ↪ Fin r) (ls : List (Line k))
    (pc : Fin (ls.length+1) → Fin p)
    (link : ∀ i : Fin ls.length, M.code (pc i.castSucc) = instruction ports (pc i.succ) ls[i])
    (c : Config w p r) (entry : c.pc = pc 0) :
    Prefix M c (List.replicate ls.length .tick)
      {c with pc := pc (Fin.last ls.length), reg := ls.foldl (applyPhysical ports) c.reg} := by
  induction ls generalizing c with
  | nil =>
    change Prefix M c [] {c with pc := pc (Fin.last 0)}
    rw [show Fin.last 0 = 0 from rfl, ← entry]
    exact .nil c
  | cons l ls ih =>
    let u : Config w p r := {c with pc := pc (Fin.succ 0), reg := applyPhysical ports c.reg l}
    have h := link 0
    have step : M.program.step c = .localStep u := by
      change (M.code c.pc).run M.publicData c = _
      rw [entry]
      change M.code (pc 0) = instruction ports (pc (Fin.succ 0)) l at h
      rw [h]
      obtain ⟨dst,rhs⟩ := l
      cases rhs <;> rfl
    exact .tick step (ih (fun i => pc i.succ) (fun i => link i.succ) u rfl)

end PairSimulation.LeafStartup.Staging

end VPVNP
end Computability
end OAI
