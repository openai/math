import OAI.Computability.BorderVNP.TeamSiteProcessor

/-! # Role and frame parsing at the common signed processor

Two public role bits select the frame sources. A processor always gets one incoming
frame. Only the first takes it from the literal, and only a nonfinal processor cuts a
candidate outgoing frame. In all four cases the owner sorter receives the unconsumed
literal and interior tails exactly.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor

open VPVNP BurstRAM RAMTape Layout

variable {Q Γ : Type} {p r k a m g w : ℕ}

local notation "Bank" => Stacks (Layout.Port r k (m*g))

/-- Public role flags, the initial frame only at the first processor, and the residual literal. -/
def roleBytes (first last : Bool) (incoming tail : List Bool) : List Bool :=
  first :: last :: ((if first then incoming else []) ++ tail)

/-- Interior frame fields followed by the physical sorter stream. A missing endpoint
consumes no wire variables. -/
def incidentBytes (first last : Bool) (incoming outgoing tail : List Bool) : List Bool :=
  (if first then [] else incoming) ++ (if last then [] else outgoing) ++ tail

/-- Full poststate of the actual frame cutter. -/
def staged (s : Bank) (literalTail wires incoming outgoing : List Bool) : Bank :=
  Function.update (Function.update (Function.update (Function.update s metadata literalTail) incident wires)
    .incoming incoming) .outgoing outgoing

/-- Deterministic cost of reading the two flags, one incoming frame, and any outgoing frame. -/
def roleTime (last : Bool) (size : ℕ) := 2+(6*size+2)+(if last then 0 else 6*size+2)

/-- Read both role flags from the actual public stream and leave the complete frame
contents untouched until the selected cutter begins. -/
theorem roleFlags_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (s : Bank) (first last : Bool) (tail : List Bool) (hi : s metadata = first::last::tail) :
    StackRuns (code P lib) 2 .first s (.incoming first last (takeFrame (incomingSource first)).body.entry)
      (Function.update s metadata tail) := by
  refine .cons (.pop (k := metadata) (f := fun b => b.elim .reject .last) rfl) ?_
  simp only [hi,List.head?_cons,Option.elim_some,List.tail_cons]
  refine .cons (.pop (k := metadata) (f := fun b => b.elim .reject (fun last =>
    .incoming first last (takeFrame (incomingSource first)).body.entry)) rfl) ?_
  simp only [Function.update_self,List.head?_cons,Option.elim_some,List.tail_cons,Function.update_idem]
  exact .nil ..

private theorem incoming_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (s : Bank) (first last : Bool) (data tail : List Bool)
    (hi : s (incomingSource first).source = data ++ tail) (hw : s .frameWidth = List.replicate data.length true)
    (ht : s .tmp = []) (he : s (incomingSource first).dest = []) :
    StackRuns (code P lib) (6*data.length+2) (.incoming first last (takeFrame (incomingSource first)).body.entry)
      s (afterReceive last) (Function.update (Function.update s (incomingSource first).source tail) (incomingSource first).dest data) :=
  TeamLink.routine_id (takeFrame_runs (incomingSource first) s data tail hi hw ht he) (code P lib)
    (.incoming first last) (afterReceive last) (fun _ => rfl)

private theorem outgoing_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (s : Bank) (data tail : List Bool) (hi : s incident = data ++ tail)
    (hw : s .frameWidth = List.replicate data.length true) (ht : s .tmp = []) (he : s .outgoing = []) :
    StackRuns (code P lib) (6*data.length+2) (.outgoing (takeFrame .next).body.entry) s (beginBlock false)
      (Function.update (Function.update s incident tail) .outgoing data) :=
  TeamLink.routine_id (takeFrame_runs .next s data tail hi hw ht he) (code P lib)
    .outgoing (beginBlock false) (fun _ => rfl)

/-- Fixed parser on arbitrary ingress and egress payloads. The endpoint checker receives
the original bits, and every unrelated port, including the record buffer, is preserved. -/
theorem roles_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (s : Bank) (first last : Bool) (incoming outgoing literalTail wires : List Bool)
    (literal : s metadata = roleBytes first last incoming literalTail)
    (route : s incident = incidentBytes first last incoming outgoing wires)
    (width : s .frameWidth = List.replicate incoming.length true)
    (outWidth : last = false → outgoing.length = incoming.length)
    (tmp : s .tmp = []) (emptyIn : s .incoming = []) (emptyOut : s .outgoing = []) :
    StackRuns (code P lib) (roleTime last incoming.length) .first s (beginBlock last)
      (staged s literalTail wires incoming (if last then [] else outgoing)) := by
  let prefixTail := (if first then incoming else []) ++ literalTail
  let wire := (if last then [] else outgoing) ++ wires
  let s₁ := Function.update s metadata prefixTail
  let src := incomingSource first
  let tail := if first then literalTail else wire
  let s₂ := Function.update (Function.update s₁ src.source tail) src.dest incoming
  have flags := roleFlags_run P lib s first last prefixTail literal
  have take := incoming_run P lib s₁ first last incoming tail (by
    cases first <;> simp_all [s₁,incomingSource,FrameSource.source,tail,prefixTail,wire,incidentBytes,List.append_assoc])
    (by simpa [s₁] using width) (by simpa [s₁] using tmp)
    (by cases first <;> simpa [s₁,incomingSource,FrameSource.dest] using emptyIn)
  have head : StackRuns (code P lib) (2+(6*incoming.length+2)) .first s (afterReceive last) s₂ :=
    flags.trans take
  have hm : s₂ metadata = literalTail := by cases first <;> simp [s₂,s₁,prefixTail,src,incomingSource,tail,FrameSource.source,FrameSource.dest]
  have hw : s₂ incident = wire := by
    cases first <;> simp_all [s₂,s₁,src,incomingSource,tail,wire,FrameSource.source,FrameSource.dest,incidentBytes]
  have hin : s₂ .incoming = incoming := by cases first <;> simp [s₂,src,incomingSource,FrameSource.dest]
  have hout : s₂ .outgoing = [] := by cases first <;> simp [s₂,s₁,src,incomingSource,FrameSource.source,FrameSource.dest,emptyOut]
  have hs {j : Layout.Port r k (m*g)} (hneMeta : j ≠ metadata) (hneWire : j ≠ incident) (hneIn : j ≠ .incoming) :
      s₂ j = s j := by cases first <;> simp [s₂,s₁,src,incomingSource,FrameSource.source,FrameSource.dest,hneMeta,hneWire,hneIn]
  cases last with
  | true =>
    have he : s₂ = staged s literalTail wires incoming [] := by
      funext j
      by_cases h₁ : j = metadata
      · simpa [h₁,staged] using hm
      by_cases h₂ : j = incident
      · simpa [h₂,staged,wire] using hw
      by_cases h₃ : j = .incoming
      · simpa [h₃,staged] using hin
      by_cases h₄ : j = .outgoing
      · simpa [h₄,staged] using hout
      simpa [staged,h₁,h₂,h₃,h₄] using hs h₁ h₂ h₃
    simpa [roleTime,afterReceive,he] using head
  | false =>
    have second := outgoing_run P lib s₂ outgoing wires (by simpa [wire] using hw)
      (by rw [hs (j := .frameWidth) (by simp) (by simp) (by simp),outWidth rfl]; exact width)
      ((hs (j := .tmp) (by simp) (by simp) (by simp)).trans tmp) hout
    have he : Function.update (Function.update s₂ incident wires) .outgoing outgoing =
        staged s literalTail wires incoming outgoing := by
      funext j
      by_cases h₁ : j = metadata
      · simpa [h₁,staged] using hm
      by_cases h₂ : j = incident
      · simp [h₂,staged]
      by_cases h₃ : j = .incoming
      · simpa [h₃,staged] using hin
      by_cases h₄ : j = .outgoing
      · simp [h₄,staged]
      simpa [staged,h₁,h₂,h₃,h₄] using hs h₁ h₂ h₃
    simpa [roleTime,outWidth rfl,he] using head.trans second

end TeamSite.Processor

end BorderVNP
end Computability
end OAI
