import OAI.Computability.BorderVNP.TransmissionSiteRoles
import OAI.Computability.BorderVNP.TeamSiteProcessorPrelude

/-! # Reaching the physical RAM block from the actual signed site input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RAMTape TeamSite TeamSite.Processor TeamTapeHandoff

variable {pc reg k routines m g R r w a : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

/-- The clock allowance for parsing and building the initialization pairs from a raw site. -/
def entryBudget (w n e size : ℕ) : ℕ :=
  46*n+19+(3*(w+1)+9*Nat.clog 2 (n+1)+7*(2^e)+4) +
    (10*(w+1)+20*(2^e)+13+TeamTapeInputEmit.budget (w+1) size)

omit [Fintype Q] in
set_option maxRecDepth 3000 in
/-- The fixed processor starts on the tape carrying the supplied physical interpreter.
At its first RAM block instruction, both the endpoint and its assigned sorter see their
correct inputs, including the true initial record buffer and unmodified handoffs. -/
theorem sitePreludeWith (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg k routines)
    (lib : Fin routines → Macro Q Γ m g) (S : SiteData R r reg k w a) (d link n e : ℕ) (fit : fitsWith physical reg k r w a R link n e) (hw : 0 < w)
    (hH : 2^e ≤ n) (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    let data := F.row j
    let stride := entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link
    let base := j.val*stride
    let raw := List.ofFn (G.word pin ext int u j)
    let incoming := ingress (S.start P u) int j
    2*(base+data.length) ≤ 2^(w+1) → 2*data.length ≤ 4*(2^e) →
    ∃ t bank, t ≤ preludeTime (entryBudget w n e data.length) reg k w (last j) ∧
      StackRuns (Processor.code P lib) t Processor.start (StackCompiler.labeledInput Layout.input raw)
        (beginBlock (last j)) bank ∧
      bank ∘ endpoint ∘ Endpoint.startup = TeamLocalClock.Startup.input
        (S.publicWords u) S.block S.limit S.burst incoming ∧
      Work.Ready (by omega : 2 ≤ w+1) (2^e) (TeamTapeInputEmit.records (w+1) base data)
        (bank ∘ Layout.site) ∧
      RouteReady n (Wires.edgeEquiv int).2 (Wires.primary j) (Wires.secondary j) bank ∧
      bank .outgoing = egress int j ∧ bank .payload = [] ∧ bank .tmp = [] := by
  intro G F data stride base raw incoming room cap
  obtain ⟨ticks,out,clock,init,ready,incident,addr,peek,bits,high,scratch,bucket⟩ :=
    entryReadyWith physical P S d link n e fit hw hH u j pin ext int ibase hbase starbase room cap
  let pad := List.replicate (n-(stride+Wires.innerWidth r reg w e (w+1))) false
  let rest := (F.exterior j).flatten ++ F.pins j ++ ownerStream int j ++ pad
  let metadataRest := metadataTail (S.publicWords u) S.block S.limit S.burst (S.start P u) j e n
    (S.advice u j) (S.free u j) ++ rest
  have width : (out (.inr .start)).length = w+1 := by rw [addr,length_wordBits]
  have pubData : out (.inl (.peek .input)) =
      TeamPublicWords.bytes (Layout.parameters (S.publicWords u) S.block S.limit S.burst) ++
        roleBytes (first j) (last j) incoming metadataRest := by
    rw [peek]
    simpa only [rest,metadataRest,incoming,List.append_assoc] using
      payload_roles (S.publicWords u) S.block S.limit S.burst (S.start P u) j e n
        (S.advice u j) (S.free u j) int rest
  have linkData := incident.trans (ownerStream_roles (S.start P u) int j)
  let outgoing := egress int j
  let marks := List.replicate (Layout.frameSize reg w) true
  let bank := Bank.loaded (r := reg) (d := m*g) out (S.publicWords u) S.block S.limit S.burst
    metadataRest (sortTail int j) marks incoming (if last j then [] else outgoing)
  have prefixRun := prelude_run P lib raw out init (S.publicWords u) S.block S.limit S.burst (first j) (last j)
    incoming outgoing metadataRest (sortTail int j) width pubData linkData
      (ingress_size ..) (egress_size int j)
  refine ⟨preludeTime ticks reg k w (last j),bank,?_,prefixRun,Bank.startup_view ..,?_,?_,?_,rfl,rfl⟩
  · change ticks ≤ entryBudget w n e data.length at clock
    unfold preludeTime
    omega
  · apply Bank.workReady
    exact ready
  · apply Bank.routeReady
    · unfold metadataRest metadataTail
      simp only [List.append_assoc]
      exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact width
    · rw [bucket,List.length_replicate]
    · exact bits
    · exact high
    · exact scratch
  · change (if last j then [] else outgoing) = egress int j
    cases h : last j with
    | false => rfl
    | true => exact (egress_at_last int j h).symm

set_option maxRecDepth 3000 in
/-- The actual fixed signed machine starts with its unmodified contraction tape alone.
At its first RAM block instruction, both the endpoint and its assigned sorter see their
correct inputs, including the true initial record buffer and unmodified handoffs. -/
theorem sitePrelude (d link n e : ℕ) (fit : Fits P lib r w a R link n e) (hw : 0 < w)
    (hH : 2^e ≤ n) (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (int : Wires.Edge r reg w e (w+1) → Bool)
    (ibase hbase starbase : ℕ) :
    let G := wiring P lib S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    let data := F.row j
    let stride := entryStride (Processor.machine P lib) (w+1) n (prefixCapacity r k reg w n+1+a) R link
    let base := j.val*stride
    let raw := List.ofFn (G.word pin ext int u j)
    let incoming := ingress (S.start P u) int j
    2*(base+data.length) ≤ 2^(w+1) → 2*data.length ≤ 4*(2^e) →
    ∃ t bank, t ≤ preludeTime (entryBudget w n e data.length) reg k w (last j) ∧
      StackRuns (Processor.code P lib) t Processor.start (StackCompiler.labeledInput Layout.input raw)
        (beginBlock (last j)) bank ∧
      bank ∘ endpoint ∘ Endpoint.startup = TeamLocalClock.Startup.input
        (S.publicWords u) S.block S.limit S.burst incoming ∧
      Work.Ready (by omega : 2 ≤ w+1) (2^e) (TeamTapeInputEmit.records (w+1) base data)
        (bank ∘ Layout.site) ∧
      RouteReady n (Wires.edgeEquiv int).2 (Wires.primary j) (Wires.secondary j) bank ∧
      bank .outgoing = egress int j ∧ bank .payload = [] ∧ bank .tmp = [] :=
  sitePreludeWith (Processor.machine P lib) P lib S d link n e fit hw hH u j pin ext int ibase hbase starbase

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
