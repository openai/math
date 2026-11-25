import OAI.Optimization.LinearProgramming.RAM.Call
import OAI.Optimization.LinearProgramming.RAM.Footprint
import OAI.Optimization.LinearProgramming.PrimalDual.Layout
import OAI.Optimization.LinearProgramming.Specification

/-! Subroutine calls during a single RAM execution.
The host, original guest, and both installed address ranges precede the LP input. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace SubroutineCalls

open RAM

structure Site where
  entry : ℕ
  ret : ℕ → ℕ

def Site.limit (site : Site) (guest : Program) : ℕ := site.entry+(Call.subroutine guest site.entry site.ret).length
def Site.Inside (site : Site) (guest : Program) (pc : ℕ) : Prop := site.entry ≤ pc ∧ pc < site.limit guest
def Site.Installed (site : Site) (host guest : Program) : Prop :=
  CodeAt host site.entry (Call.subroutine guest site.entry site.ret)

def stateAt {k : ℕ} (tr : Fin (k+1) → State ℚ) (j : ℕ) : State ℚ :=
  tr ⟨min j k,Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

def window {k : ℕ} (tr : Fin (k+1) → State ℚ) (offset length : ℕ) (j : Fin (length+1)) : State ℚ :=
  stateAt tr (offset+j.val)

/-- Every executed instruction in an ordinary interval lies outside both guest images. -/
def Outside (guest : Program) (first second : Site) {k : ℕ} (tr : Fin (k+1) → State ℚ) (off n : ℕ) : Prop :=
  ∀ i : Fin n, ¬ first.Inside guest ((window tr off n i.castSucc).pc) ∧
    ¬ second.Inside guest ((window tr off n i.castSucc).pc)

/-- The states are literal slices of the full host trace. The same endpoint
contains the virtual result and preserves every odd caller register. -/
structure GuestOn (host guest : Program) (site : Site) (H : ℕ) (dims : List ℕ) (input : List ℚ)
    (valid : State ℚ → Prop) (tag : ℕ) {k : ℕ} (tr : Fin (k+1) → State ℚ) (off n : ℕ) : Prop where
  fits : off+n ≤ k
  used : 0 < n
  actual : Trace host (stateAt tr off) n (window tr off n)
  entryPC : (stateAt tr off).pc = site.entry
  entryLive : (stateAt tr off).output = none
  returnPC : (stateAt tr (off+n)).pc = site.ret tag
  returnLive : (stateAt tr (off+n)).output = none
  inside : ∀ i : Fin n, site.Inside guest ((window tr off n i.castSucc).pc)
  inputData : ∀ j, (stateAt tr off).data (2*j) = (start dims input).data j
  inputIndex : ∀ j, (stateAt tr off).index (2*j) = 2*(start dims input).index j
  virtual : ∃ (l : ℕ) (u : Fin (l+1) → State ℚ), Trace guest (start dims input) l u ∧
    valid (u (Fin.last l)) ∧ (u (Fin.last l)).output = some tag ∧ n ≤ 2*l ∧ (∀ i, scalarBound H (u i)) ∧
    (∀ j, (stateAt tr (off+n)).data (2*j) = (u (Fin.last l)).data j) ∧
    (∀ j, (stateAt tr (off+n)).index (2*j) = 2*(u (Fin.last l)).index j) ∧
    (∀ j, (stateAt tr (off+n)).data (2*j+1) = (stateAt tr off).data (2*j+1)) ∧
    ∀ j, (stateAt tr (off+n)).index (2*j+1) = (stateAt tr off).index (2*j+1)

inductive Phase where
  | outside
  | guest (site : Site) (dims : List ℕ) (input : List ℚ) (valid : State ℚ → Prop) (tag : ℕ)

/-- There are no gaps: the next phase begins at the end of the current phase. -/
inductive OnTrace (host guest : Program) (first second : Site) (H : ℕ) {k : ℕ} (tr : Fin (k+1) → State ℚ) :
    ℕ → List Phase → ℕ → Prop where
  | nil {off} (fits : off ≤ k) : OnTrace host guest first second H tr off [] off
  | outside {off n ps stop} (fits : off+n ≤ k) (clear : Outside guest first second tr off n)
      (rest : OnTrace host guest first second H tr (off+n) ps stop) :
      OnTrace host guest first second H tr off (.outside :: ps) stop
  | guestRun {off n ps stop site dims input valid tag} (call : GuestOn host guest site H dims input valid tag tr off n)
      (rest : OnTrace host guest first second H tr (off+n) ps stop) :
      OnTrace host guest first second H tr off (.guest site dims input valid tag :: ps) stop

def calls : List Phase → ℕ
  | [] => 0
  | .outside :: ps => calls ps
  | .guest _ _ _ _ _ :: ps => calls ps+1

def plan {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (first second : Site) (tag : ℕ) : List Phase :=
  if tag=0 then [.outside,.guest first [m,d] (lpInput A b) (FeasibilityOutput A b) 1,.outside]
  else [.outside,.guest first [m,d] (lpInput A b) (FeasibilityOutput A b) 0,.outside,.outside,
    .guest second [m+(m+(d+(d+1))),d+m] (lpInput (finJointMatrix A b c) (finJointRhs b c))
      (FeasibilityOutput (finJointMatrix A b c) (finJointRhs b c)) (tag-1), .outside]

def Solver (guest : Program) (C E bC bE : ℕ) : Prop :=
  ∀ (m d : ℕ), 0 < m → 0 < d → ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
    ∃ (k : ℕ) (tr : Fin (k+1) → State ℚ), Trace guest (start [m,d] (lpInput A b)) k tr ∧
      k ≤ polyBound C E (m+d) ∧ (∀ i, scalarBound (polyBound bC bE (totalBits (lpInput A b))) (tr i)) ∧
      FeasibilityOutput A b (tr (Fin.last k))

def Correct (host guest : Program) (first second : Site) (C E bC bE : ℕ) : Prop :=
  ∀ (m d : ℕ), 0 < m → 0 < d → ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ),
    let input := lpInput A b++List.ofFn c
    let H := polyBound bC bE (totalBits input)
    ∃ (tag k : ℕ) (tr : Fin (k+1) → State ℚ), tag ≤ 2 ∧ Trace host (start [m,d] input) k tr ∧
      k ≤ polyBound C E (m+d) ∧ (∀ i, scalarBound H (tr i)) ∧
      (tr (Fin.last k)).output = some tag ∧ OptimizationOutput A b c (tr (Fin.last k)) ∧
      OnTrace host guest first second H tr 0 (plan A b c first second tag) k ∧
      calls (plan A b c first second tag) = (if tag=0 then 1 else 2)

/-- The ordinary prefix is fixed. The middle bytes and both return maps can
inspect only the address following the first hole. A guest instruction list is
provided solely to the two explicit subroutine insertions in `assemble`. -/
structure Template where
  «prefix» : Program
  middle : ℕ → Program
  firstReturn : ℕ → ℕ → ℕ
  secondReturn : ℕ → ℕ → ℕ

def Template.afterFirst (t : Template) (guest : Program) := t.«prefix».length+(guest.map Call.width).sum

def Template.firstSite (t : Template) (guest : Program) : Site :=
  ⟨t.«prefix».length,t.firstReturn (t.afterFirst guest)⟩

def Template.secondSite (t : Template) (guest : Program) : Site :=
  let off := t.afterFirst guest
  ⟨off+(t.middle off).length,t.secondReturn off⟩

def Template.assemble (t : Template) (guest : Program) : Program :=
  let a := t.firstSite guest
  let b := t.secondSite guest
  t.«prefix» ++ Call.subroutine guest a.entry a.ret ++ t.middle (t.afterFirst guest) ++ Call.subroutine guest b.entry b.ret

structure Registered (t : Template) (host guest : Program) (first second : Site) : Prop where
  bytes : host = t.assemble guest
  original : first = t.firstSite guest
  joint : second = t.secondSite guest
  firstPlaced : first.Installed host guest
  secondPlaced : second.Installed host guest
  disjoint : first.limit guest ≤ second.entry

/-- The template family is chosen before the supplied guest. Its arguments are
only the static numerical address reserve and the two time-bound constants. -/
def Uniform (family : ℕ → ℕ → ℕ → Template) : Prop :=
  ∀ (guest : Program) (C E bC bE : ℕ), Solver guest C E bC bE →
    ∃ (host : Program) (first second : Site) (tC tE sC sE : ℕ),
      Registered (family (addressBudget guest) C E) host guest first second ∧ Correct host guest first second tC tE sC sE

/-- A single bounded guest, host and two disjoint, physically installed holes
serve every LP. The full execution is covered by its prescribed, contiguous plan. -/
def StrongTwoCalls : Prop :=
  ∃ family : ℕ → ℕ → ℕ → Template, Uniform family ∧
    ∃ (guest host : Program) (first second : Site) (C E bC bE tC tE sC sE : ℕ),
      Solver guest C E bC bE ∧ Registered (family (addressBudget guest) C E) host guest first second ∧
      Correct host guest first second tC tE sC sE

end SubroutineCalls
end PrimalDual
end LinearProgramming
end Optimization
end OAI
