import OAI.Computability.BorderVNP.TransmissionSiteLiteral

/-! # The signed contraction for the real team processor's instruction table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine TeamTapeHandoff RoutingISA.Pins

variable {p reg k routines m g R r w a : ℕ} {Q Γ : Type} [Fintype Q]

/-- The public values and reserved literal bits of one physical installation. -/
structure SiteData (R r reg k w a : ℕ) where
  /-- Team-local public ISA operand bank. -/
  publicWords : Fin (R+1) → Fin k → Word w
  /-- Logical block tick cap H, supplied to the RAM meter independently of the sorting bucket. -/
  block : Word w
  /-- Public elapsed-tick cap. -/
  limit : Word w
  /-- Public burst-size cap. -/
  burst : Word w
  /-- The prescribed initial registers on each team's first processor. -/
  registers : Fin (R+1) → Fin reg → Word w
  /-- One distributed advice bit in the common literal position of each processor. -/
  advice : Fin (R+1) → Fin r → Bool
  /-- Remaining free literal bits, e.g. the local site descriptions. -/
  free : Fin (R+1) → Fin r → Fin a → Bool

variable (P : TeamOpcode.Program p reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

/-- Public initial frame, including the actual entry PC and zero elapsed ticks. -/
def SiteData.start (u : Fin (R+1)) : Frame w reg :=
  initial (TeamTapeInputEmit.word w P.base.entry.val) (S.registers u)

/-- All free bits following the four compact input/record fields in one physical literal. -/
def SiteData.siteBits (n e : ℕ) (u : Fin (R+1)) (j : Fin r) :
    Fin (prefixCapacity r k reg w n+1+a) → Bool :=
  payloadBits (S.publicWords u) S.block S.limit S.burst (S.start P u)
    j e n (S.advice u j) (S.free u j)

/-- Bit budget for a physical interpreter prefix, including its actual serialized table. -/
def fitsWith (physical : UniversalMachine.Program) (reg k r w a R link n e : ℕ) : Prop :=
  entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link +
    Wires.innerWidth r reg w e (w+1) ≤ n

/-- Physical slots for an arbitrary fixed interpreter table and the stated RAM template.
The complete prefix of that very interpreter is part of the initialized memory. -/
noncomputable def wiringWith (physical : UniversalMachine.Program) (P : TeamOpcode.Program p reg k routines)
    (S : SiteData R r reg k w a) (d link n e : ℕ) (fit : fitsWith physical reg k r w a R link n e) :
    Wiring R r (cutWidth n+(setupWidth (w+1) n+(prefixCapacity r k reg w n+1+a))) d link
      (Wires.innerWidth r reg w e (w+1)) n (Wires.Edge r reg w e (w+1)) :=
  entryWiring physical (S.siteBits P n e) Wires.ownerSlots d link n (w+1) (2^e) fit

/-- The actual site table's program prefix and its three memory fields, together with
all owner handoff and sorting slots, fit in the common processor length. -/
def Fits (r w a R link n e : ℕ) : Prop :=
  entryStride (TeamSite.Processor.machine P lib) (w+1) n (prefixCapacity r k reg w n+1+a) R link +
    Wires.innerWidth r reg w e (w+1) ≤ n

/-- The contraction uses the concrete fixed processor program, the actual fixed-width owner
wiring, and all finite input and record parameters pinned in the literal itself. -/
noncomputable def wiring (d link n e : ℕ) (fit : Fits P lib r w a R link n e) :
    Wiring R r (cutWidth n+(setupWidth (w+1) n+(prefixCapacity r k reg w n+1+a))) d link
      (Wires.innerWidth r reg w e (w+1)) n (Wires.Edge r reg w e (w+1)) :=
  entryWiring (TeamSite.Processor.machine P lib) (S.siteBits P n e) Wires.ownerSlots d link n
    (w+1) (2^e) fit

/-- The interior stream presented by a real signed input consists of the two existing
register handoffs, the assigned virtual sorter streams and their fixed zero padding. -/
def ownerStream {e : ℕ} (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) : List Bool :=
  Wires.frameInput (Wires.edgeEquiv int).1 true j ++ Wires.frameInput (Wires.edgeEquiv int).1 false j ++
    TeamTapeInputRoute.ownerBits (Wires.edgeEquiv int).2 (Wires.primary j) (Wires.secondary j) ++
    List.replicate (Wires.innerWidth r reg w e (w+1) -
      (Wires.activeSlots j : List (Option (Wires.Edge r reg w e (w+1)))).length) false

set_option maxRecDepth 3000 in
/-- The complete physical word begins with the actual initialized RAM row and presents the
named owner frames and sorter exchange bits in the order used by the processor table. -/
theorem wordEqWith (physical : UniversalMachine.Program) (P : TeamOpcode.Program p reg k routines)
    (S : SiteData R r reg k w a) (d link n e : ℕ) (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    List.ofFn (G.word pin ext int u j) = F.row j ++ ownerStream int j ++
      List.replicate (n-(entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link+
        Wires.innerWidth r reg w e (w+1))) false := by
  intro G F
  have h := G.word_processorFields u j pin ext int ibase hbase starbase
  change List.ofFn (G.word pin ext int u j) = F.row j ++
    List.ofFn (fun i => (Wires.ownerSlots j i).elim false int) ++ _ at h
  rw [Wires.ownerSlots_read] at h
  exact h

set_option maxRecDepth 3000 in
/-- The complete physical word begins with the actual initialized RAM row and presents the
named owner frames and sorter exchange bits in the order used by the processor table. -/
theorem word_eq (d link n e : ℕ) (fit : Fits P lib r w a R link n e) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) :
    let G := wiring P lib S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    List.ofFn (G.word pin ext int u j) = F.row j ++ ownerStream int j ++
      List.replicate (n-(entryStride (TeamSite.Processor.machine P lib) (w+1) n (prefixCapacity r k reg w n+1+a) R link+
        Wires.innerWidth r reg w e (w+1))) false :=
  wordEqWith (TeamSite.Processor.machine P lib) P S d link n e fit u j pin ext int ibase hbase starbase

set_option maxRecDepth 3000 in
/-- The real processor's empty-workspace entry reads the pinned public words and flags
from its residual literal, leaves the handoffs and sorter on the incident stack, and
initializes its buffer at the globally addressed start. All scratch remains as required
by the public-word and sorter decoders. -/
theorem entryReadyWith (physical : UniversalMachine.Program) (P : TeamOpcode.Program p reg k routines)
    (S : SiteData R r reg k w a) (d link n e : ℕ) (fit : fitsWith physical reg k r w a R link n e) (hw : 0 < w)
    (hH : 2^e ≤ n) (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    let data := F.row j
    let stride := entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link
    let base := j.val*stride
    let pad := List.replicate (n-(stride+Wires.innerWidth r reg w e (w+1))) false
    let more := payload (S.publicWords u) S.block S.limit S.burst
      (S.start P u) j e n (S.advice u j) (S.free u j)
    2*(base+data.length) ≤ 2^(w+1) → 2*data.length ≤ 4*(2^e) →
    ∃ ticks out,
      ticks ≤ 46*n+19 + (3*(w+1)+9*Nat.clog 2 (n+1)+7*(2^e)+4) +
        (10*(w+1)+20*(2^e)+13 + TeamTapeInputEmit.budget (w+1) data.length) ∧
      TeamTapeInput.Entry.program.Runs ticks
        (Sum.elim (TeamTapeInput.initial (List.ofFn (G.word pin ext int u j))) (fun _ => [])) out ∧
      TeamTapeInputEmit.Ready (by omega : 2 ≤ w+1) (2^e) (base+data.length) []
        (TeamTapeInputEmit.records (w+1) base data)
        (out ∘ TeamTapeInput.Entry.setupPort ∘ TeamTapeInputEmit.Setup.Port.emit) ∧
      out (.inl (.cut .incident)) = ownerStream int j ∧
      out (.inr .start) = wordBits (TeamTapeInputEmit.word (w+1) base) ∧
      out (.inl (.peek .input)) = more ++ (F.exterior j).flatten ++ F.pins j ++ ownerStream int j ++ pad ∧
      out (.inl .bits) = [] ∧ out (.inl .high) = [] ∧ out (.inl .scratch) = [] ∧
      out (.inr .bucket) = List.replicate (2^e) true := by
  intro G F data stride base pad more room cap
  have result := entryWiring_start_full physical (S.siteBits P n e)
    Wires.ownerSlots d link n (w+1) (2^e) (by omega) hH fit u j pin ext int ibase hbase starbase room cap
  obtain ⟨ticks,out,clock,run,ready,inc,addr,peek,workspace⟩ := result
  have route : List.ofFn (fun i => (Wires.ownerSlots j i).elim false int) = ownerStream int j :=
    Wires.ownerSlots_read int j
  have moreEq : List.ofFn (S.siteBits P n e u j) = more := ofFn_payloadBits ..
  rw [route] at inc
  rw [route, moreEq] at peek
  exact ⟨ticks,out,clock,run,ready,inc,addr,peek,workspace⟩

set_option maxRecDepth 3000 in
/-- The real processor's empty-workspace entry reads the pinned public words and flags
from its residual literal, leaves the handoffs and sorter on the incident stack, and
initializes its buffer at the globally addressed start. All scratch remains as required
by the public-word and sorter decoders. -/
theorem entry_ready (d link n e : ℕ) (fit : Fits P lib r w a R link n e) (hw : 0 < w)
    (hH : 2^e ≤ n) (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) :
    let G := wiring P lib S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    let data := F.row j
    let stride := entryStride (TeamSite.Processor.machine P lib) (w+1) n (prefixCapacity r k reg w n+1+a) R link
    let base := j.val*stride
    let pad := List.replicate (n-(stride+Wires.innerWidth r reg w e (w+1))) false
    let more := payload (S.publicWords u) S.block S.limit S.burst
      (S.start P u) j e n (S.advice u j) (S.free u j)
    2*(base+data.length) ≤ 2^(w+1) → 2*data.length ≤ 4*(2^e) →
    ∃ ticks out,
      ticks ≤ 46*n+19 + (3*(w+1)+9*Nat.clog 2 (n+1)+7*(2^e)+4) +
        (10*(w+1)+20*(2^e)+13 + TeamTapeInputEmit.budget (w+1) data.length) ∧
      TeamTapeInput.Entry.program.Runs ticks
        (Sum.elim (TeamTapeInput.initial (List.ofFn (G.word pin ext int u j))) (fun _ => [])) out ∧
      TeamTapeInputEmit.Ready (by omega : 2 ≤ w+1) (2^e) (base+data.length) []
        (TeamTapeInputEmit.records (w+1) base data)
        (out ∘ TeamTapeInput.Entry.setupPort ∘ TeamTapeInputEmit.Setup.Port.emit) ∧
      out (.inl (.cut .incident)) = ownerStream int j ∧
      out (.inr .start) = wordBits (TeamTapeInputEmit.word (w+1) base) ∧
      out (.inl (.peek .input)) = more ++ (F.exterior j).flatten ++ F.pins j ++ ownerStream int j ++ pad ∧
      out (.inl .bits) = [] ∧ out (.inl .high) = [] ∧ out (.inl .scratch) = [] ∧
      out (.inr .bucket) = List.replicate (2^e) true :=
  entryReadyWith (TeamSite.Processor.machine P lib) P S d link n e fit hw hH u j pin ext int ibase hbase starbase

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
