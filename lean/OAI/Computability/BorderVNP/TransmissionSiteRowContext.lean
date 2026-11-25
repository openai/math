import OAI.Computability.BorderVNP.TransmissionSiteProcessor
import OAI.Computability.BorderVNP.TeamSiteProcessorRow

/-! # The signed processor row installed on each physical contraction tape

The prepared row is obtained by executing the fixed parser and frame cutters from
the literal word, exterior pins and shared interior bits. Its primary sorting lane
contains the real time-zero records for its local portion of RAM initialization.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RAMTape TeamTapeHandoff TeamSite TeamSite.Processor

variable {pc reg k routines m g R r w a n e : ℕ} {Q Γ : Type}
variable {P : TeamOpcode.Program pc reg k routines} {lib : Fin routines → Macro Q Γ m g}

/-- Field-by-field identification of a physical processor context with the owner,
the fixed team parameters, and the interior assignment of the actual contraction. -/
structure RowInstalled (S : SiteData R r reg k w a) (u : Fin (R+1)) (j : Fin r)
    (int : Wires.Edge r reg w e (w+1) → Bool) (f : Frame w reg)
    (raw data : List Bool) (address : ℕ)
    (X : Row.Context P lib n (Nat.clog 2 r) e w) : Prop where
  rawEq : X.raw = raw
  lastEq : X.last = last j
  frameEq : X.frame = f
  pubEq : X.pub = S.publicWords u
  blockEq : X.block = S.block
  limitEq : X.limit = S.limit
  capEq : X.cap = S.burst
  primaryEq : X.primary = Wires.primary j
  secondaryEq : X.secondary = Wires.secondary j
  fieldsEq : X.fields = (Wires.edgeEquiv int).2
  initialEq : X.initial = TeamTapeInputEmit.records (w+1) address data
  outgoing : X.base .outgoing = egress int j
  dataWithin : data.length ≤ n
  preludeBound : X.preludeTicks ≤ preludeTime (entryBudget w n e data.length) reg k w (last j)

variable {S : SiteData R r reg k w a} {u : Fin (R+1)} {j : Fin r}
    {int : Wires.Edge r reg w e (w+1) → Bool} {f : Frame w reg}
    {raw data : List Bool} {address : ℕ} {X : Row.Context P lib n (Nat.clog 2 r) e w}

/-- Parser and frame extraction consume at most the prefix budget used by the uniform
row clock. -/
theorem RowInstalled.prefix_le (h : RowInstalled S u j int f raw data address X) :
    X.preludeTicks ≤ Budget.inputCost n w (2^e) data.length + Budget.prefixCost reg k w X.last := by
  rw [h.lastEq]
  have pre := h.preludeBound
  unfold preludeTime entryBudget at pre
  unfold Budget.inputCost Budget.prefixCost
  omega

/-- Bound the complete local physical path using this actual initialization length,
real owner role and runtime record count. -/
theorem RowInstalled.cost_le (h : RowInstalled S u j int f raw data address X)
    (body : ℕ) (es : List (TeamRAM.Event w)) :
    X.cost body es ≤ Budget.total reg k n (Nat.clog 2 r) e w data.length body
      (X.slots es).length (last j) := by
  have pre := h.preludeBound
  unfold preludeTime entryBudget at pre
  unfold Row.Context.cost Budget.total Budget.inputCost Budget.prefixCost
  omega

/-- The first optional padded sorter block cannot coincide with its real owner. -/
private theorem secondary_ne (j : Fin r) (v : Word (Nat.clog 2 r))
    (h : Wires.secondary j = some v) : v ≠ Wires.primary j := by
  unfold Wires.secondary at h
  split at h
  · cases h
    intro eq
    have val := congrArg Fin.val eq
    change j.val+r = j.val at val
    have bound := j.isLt
    omega
  · contradiction

set_option maxHeartbeats 800000 in
set_option maxRecDepth 3000 in
/-- Construction of the row context from the genuine fixed input tape, including
all input registers, the signed-loop bank and both actual sorting lanes. A sender
can supply any candidate output bits. The typed incoming frame names its bits. -/
theorem siteRowContextWith (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg k routines)
    (lib : Fin routines → Macro Q Γ m g) (S : SiteData R r reg k w a)
    (d link n e : ℕ) (fit : fitsWith physical reg k r w a R link n e)
    (hw : 0 < w) (hB : 2^e ≤ n) (hD : Nat.clog 2 r ≤ n) (hW : w+1 ≤ n)
    (hL : TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n)
    (capacity : 2^Nat.clog 2 r*2^e < 2^(w+1)) (pcs : pc ≤ 2^w)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) (f : Frame w reg) (incoming : f.bits = ingress (S.start P u) int j) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    let data := F.row j
    let stride := entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link
    let address := j.val*stride
    let raw := List.ofFn (G.word pin ext int u j)
    2*(address+data.length) ≤ 2^(w+1) → 2*data.length+2*S.block.val ≤ 4*2^e →
    ∃ X : Row.Context P lib n (Nat.clog 2 r) e w, RowInstalled S u j int f raw data address X := by
  intro G F data stride address raw room space
  have initSpace : 2*data.length ≤ 4*2^e := by omega
  obtain ⟨t,bank,clock,parsed,startup,work,route,sent,payload,_⟩ :=
    sitePreludeWith physical P lib S d link n e fit hw hB u j pin ext int ibase hbase starbase room initSpace
  let X : Row.Context P lib n (Nat.clog 2 r) e w := {
    raw := raw
    base := bank
    last := last j
    preludeTicks := t
    prelude := parsed
    pub := S.publicWords u
    block := S.block
    limit := S.limit
    cap := S.burst
    frame := f
    startup := by rw [incoming]; exact startup
    payload := payload
    fields := (Wires.edgeEquiv int).2
    primary := Wires.primary j
    secondary := Wires.secondary j
    distinct := secondary_ne j
    initial := TeamTapeInputEmit.records (w+1) address data
    hw₂ := by omega
    capacity := capacity
    hd := hD
    hw := hW
    hB := hB
    hL := hL
    work := work
    space := by simpa only [TeamTapeInputEmit.length_records] using space
    fits := pcs
    route := route }
  have len := congrArg List.length (wordEqWith physical P S d link n e fit u j pin ext int ibase hbase starbase)
  change raw.length = (data ++ ownerStream int j ++ _).length at len
  have width : raw.length = n := List.length_ofFn
  simp only [List.length_append,width] at len
  exact ⟨X, rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,sent,by omega,clock⟩

variable [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

set_option maxRecDepth 3000 in
/-- The signed physical processor instance, using its own universal program prefix. -/
theorem siteRowContext (d link n e : ℕ) (fit : Fits P lib r w a R link n e)
    (hw : 0 < w) (hB : 2^e ≤ n) (hD : Nat.clog 2 r ≤ n) (hW : w+1 ≤ n)
    (hL : TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n)
    (capacity : 2^Nat.clog 2 r*2^e < 2^(w+1)) (pcs : pc ≤ 2^w)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) (f : Frame w reg) (incoming : f.bits = ingress (S.start P u) int j) :
    let G := wiring P lib S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    let data := F.row j
    let stride := entryStride (Processor.machine P lib) (w+1) n (prefixCapacity r k reg w n+1+a) R link
    let address := j.val*stride
    let raw := List.ofFn (G.word pin ext int u j)
    2*(address+data.length) ≤ 2^(w+1) → 2*data.length+2*S.block.val ≤ 4*2^e →
    ∃ X : Row.Context P lib n (Nat.clog 2 r) e w, RowInstalled S u j int f raw data address X := siteRowContextWith (Processor.machine P lib) P lib S d link n e fit hw hB hD hW hL
    capacity pcs u j pin ext int ibase hbase starbase f incoming

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
