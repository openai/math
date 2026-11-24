import OAI.Computability.VPVNP.CompressorRefreshOperandInputs
import OAI.Computability.VPVNP.CompressorRecordRegisterSetup
import OAI.Computability.VPVNP.PairRefreshDiagonalArguments

/-!
# Native setup of the two diagonal comparisons at a refresh site

The six computed registers contain both old half-wire intervals and both starts in the
parent's external bundles. All offsets come from the constructed segment tables. The
expression program hands control directly to the linked comparison code.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.DiagonalFrame

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe NewSlots PairSimulation NodeArguments RefreshMapOperands OperandInputs
open scoped Fin.CommRing

variable {a b g dH w pcs regs params d₀ : ℕ}

/-- Computes the old outgoing and incoming interval endpoints and the corresponding segment
starts in the new external half-wires. -/
def fields (degree : ℕ) (external : Fin d₀) (I : OperandInputs.Input) : Fin 6 → Expr :=
  let z := I.parent.siteOrd
  let slot := ArgumentSite.portIndex degree z I.lanes
  let idx := ArgumentSite.diagonal degree z I.lanes
  let oldOut := ArgumentAddress.field degree I.child false slot
  let oldIn := ArgumentAddress.field degree I.child true slot
  let extOut := ArgumentAddress.fieldStatic I.parent false external
  let extIn := ArgumentAddress.fieldStatic I.parent true external
  ![oldOut,oldOut.add (.load (I.widthOut.add idx)),extOut.add (.load (I.offOut.add idx)),
    oldIn,oldIn.add (.load (I.widthIn.add idx)),extIn.add (.load (I.offIn.add idx))]

/-- The output-bank indices in the existing diagonal comparison program. -/
def register : Fin 6 → Fin 10 := ![0,1,2,7,8,9]

variable (X : State a (a+g)) (p : (X.Base × BitWord g) × Fin (2^a))
  (P : SlotGraph (Fin (2^a)) dH) (hD : 1 < 2^a) (hd : dH+1 ≤ 2^b)
  (internal : X.Base × BitWord g → Fin (2^a) × Fin dH → ℕ) (A : Arena) (child parent : ℕ)
  (old next : IncidenceDirectory w) (q : Fin 8 → W w) (demand term : W w) (I : OperandInputs.Input)
  (pub : Fin 5 → W w) (state : W w) (m : Memory w)

local notation "Y" => newState X P hD hd internal
local notation "G" => splitSlots X
local notation "port" => bitWordFinEquiv a
local notation "ws" => groupedWidths port (splitWidths X)
local notation "perm" => oldPortMatching G port
local notation "S" => Fintype.card X.Base * 2^a * 2^g * 2^a
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "f" => fields (2^a) (refreshSlots hd (Sum.inl 0)) I
local notation "args" => RefreshDiagonal.argumentPointers X p P hD hd internal A child parent

private theorem encode {u : W w} {n : ℕ} (h : u.val = n) : u = (n : W w) :=
  Fin.ext (h.trans (Nat.mod_eq_of_lt (h ▸ u.isLt)).symm)

/-- Evaluating the fixed setup formulas uses the actual old and new slot layouts.
Incoming half-wires keep their own lengths and their source-bundle ordering. -/
theorem values {fit : S ≤ 2^w} (h : Describes I pub state m X p P hD hd internal A child parent old next q demand term)
    (oldRows : old.ActualColumns X m) (newRows : next.ActualColumns Y m) (data : SegmentFields X q fit m)
    (wide : 2^a < 2^w) :
    let v : RefreshDiagonal.Pointers w := args
    ∀ i, (f i).eval pub state m = ![v.oldOut,v.oldOut+(ws (p,p.2) : W w),v.externalOut,
      v.oldIn,v.oldIn+(ws ((perm).symm (p,p.2)) : W w),v.externalIn] i := by
  let slot := ArgumentSite.portIndex (2^a) I.parent.siteOrd I.lanes
  let idx := ArgumentSite.diagonal (2^a) I.parent.siteOrd I.lanes
  have id : idx.eval pub state m = idWord O fit (p,p.2) :=
    ArgumentSite.diagonal_eval X p pub state m I.parent.siteOrd I.lanes h.site h.lanes wide fit
  have sj : slot.eval pub state m = CursorRAM.encode w p.2.val :=
    ArgumentSite.portIndex_eval X p pub state m I.parent.siteOrd I.lanes h.site h.lanes wide
  have oldAt (dir : Bool) := ArgumentAddress.eval_field h.childRep oldRows dir slot p.2 wide sj
  have newAt (dir : Bool) := ArgumentAddress.eval_fieldStatic h.parentRep newRows dir (refreshSlots hd (.inl 0))
  have pair := Readback.interval_spec X q m data (p,p.2)
  let i := idWord O fit (p,p.2)
  have wo : m (q 1+i).val = (ws (p,p.2) : W w) := encode (congrArg Prod.fst pair.1)
  have oo : m (q 5+i).val = ((outgoingRecord G port (splitWidths X) (p,p.2)).offset : W w) := encode (congrArg Prod.snd pair.1)
  have wi : m (q 7+i).val = (ws ((perm).symm (p,p.2)) : W w) := encode (congrArg Prod.fst pair.2)
  have oi : m (q 6+i).val = ((incomingRecord G port (splitWidths X) (p,p.2)).offset : W w) := encode (congrArg Prod.snd pair.2)
  have read (head : Expr) (c : Fin 8) (hc : head.eval pub state m = q c) :
      (Expr.load (head.add idx)).eval pub state m = m (q c+i).val := by
    change m ((head.eval pub state m)+(idx.eval pub state m)).val = _
    rw [hc,id]
  dsimp only
  intro j
  fin_cases j
  · exact oldAt false
  · exact congrArg₂ (·+·) (oldAt false) ((read _ _ h.widthOut).trans wo)
  · have eq := congrArg₂ (·+·) (newAt false) ((read _ _ h.offOut).trans oo)
    exact eq.trans (Nat.cast_add ..).symm
  · exact oldAt true
  · exact congrArg₂ (·+·) (oldAt true) ((read _ _ h.widthIn).trans wi)
  · have eq := congrArg₂ (·+·) (newAt true) ((read _ _ h.offIn).trans oi)
    exact eq.trans (Nat.cast_add ..).symm

/-- The native setup's exit satisfies the six-register ABI consumed by
`RefreshDiagonal.compare_arguments`. Its only external accesses are reads. -/
theorem setup_trace {fit : S ≤ 2^w} (M : Machine w pcs regs params) (c : Config w pcs regs)
    (inputs : Fin 6 → Fin regs) (vm : Fin (RegisterSetup.regCount f) ↪ Fin regs) (reg : Fin 10 ↪ Fin regs)
    (pc : ℕ → Fin pcs) (link : RegisterSetup.Linked vm inputs M pc (RegisterSetup.lines f))
    (safe : ∀ i j, vm i ≠ inputs j) (outputs : ∀ i, vm (RegisterSetup.output f i) = reg (register i))
    (atStart : c.pc = pc 0)
    (h : Describes I (fun i => c.reg (inputs i.castSucc)) (c.reg (inputs (Fin.last 5))) m X p P hD hd internal
      A child parent old next q demand term)
    (oldRows : old.ActualColumns X m) (newRows : next.ActualColumns Y m) (data : SegmentFields X q fit m)
    (wide : 2^a < 2^w) :
    ∃ ev d, ev.length = (RegisterSetup.lines f).length ∧ countProbes ev = (∑ i, (f i).loads) ∧ choiceBits ev = [] ∧
      d.pc = pc (RegisterSetup.lines f).length ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (args).Ready reg d (ws (p,p.2)) (ws ((perm).symm (p,p.2))) ∧
      (∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+ev.length) c m bs =
        (execute M.program fuel d m bs).map (fun rep => ⟨ev++rep.events,rep.result⟩) := by
  obtain ⟨ev,d,len,probes,paths,ep,priv,pers,vals,frame,run⟩ := RegisterSetup.execute_setup_trace f inputs vm M m pc link safe c atStart
  have val (i) := (vals i).trans (values X p P hD hd internal A child parent old next q demand term I _ _ m
    h oldRows newRows data wide i)
  simp only [outputs] at val
  exact ⟨ev,d,len,probes,paths,ep,priv,pers,⟨⟨val 0,val 1,val 2⟩,⟨val 3,val 4,val 5⟩⟩,frame,run⟩

/-- Register and continuation postconditions for the physical operand setup. -/
theorem setup {fit : S ≤ 2^w} (M : Machine w pcs regs params) (c : Config w pcs regs)
    (inputs : Fin 6 → Fin regs) (vm : Fin (RegisterSetup.regCount f) ↪ Fin regs) (reg : Fin 10 ↪ Fin regs)
    (pc : ℕ → Fin pcs) (link : RegisterSetup.Linked vm inputs M pc (RegisterSetup.lines f))
    (safe : ∀ i j, vm i ≠ inputs j) (outputs : ∀ i, vm (RegisterSetup.output f i) = reg (register i))
    (atStart : c.pc = pc 0)
    (h : Describes I (fun i => c.reg (inputs i.castSucc)) (c.reg (inputs (Fin.last 5))) m X p P hD hd internal
      A child parent old next q demand term)
    (oldRows : old.ActualColumns X m) (newRows : next.ActualColumns Y m) (data : SegmentFields X q fit m)
    (wide : 2^a < 2^w) :
    ∃ ev d, ev.length = (RegisterSetup.lines f).length ∧ d.pc = pc (RegisterSetup.lines f).length ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (args).Ready reg d (ws (p,p.2)) (ws ((perm).symm (p,p.2))) ∧
      (∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+ev.length) c m bs =
        (execute M.program fuel d m bs).map (fun rep => ⟨ev++rep.events,rep.result⟩) := by
  obtain ⟨ev,d,len,_,_,result⟩ := setup_trace X p P hD hd internal A child parent old next q demand term I m M c inputs vm reg pc link safe outputs atStart h oldRows newRows data wide
  exact ⟨ev,d,len,result⟩

end CompressorRecords.PortRefresh.DiagonalFrame

end VPVNP
end Computability
end OAI
