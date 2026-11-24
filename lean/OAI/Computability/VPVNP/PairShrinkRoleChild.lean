import OAI.Computability.VPVNP.PairNodeChildStage
import OAI.Computability.VPVNP.PairShrinkRoleStages

/-!
# Decoding the child arguments of a shrinking visit

The popped descriptor supplies the list of old sites. A complete guess
assigns each outgoing and incoming slot independently and leaves the suffix
for the local kernel. Every shorter stream rejects inside the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.ChildArguments

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DFS NodeArguments
open NodeArguments.ChildScan
open scoped Fin.CommRing

variable {w p r k a g endAddr : ℕ} (X : State a g)

/-- Bits consumed by one child's slots in the order of the native scan. -/
noncomputable def width (u : X.network.Site) : ℕ :=
  ChildSlots.length X u (ChildSlots.slots (2 ^ a))

/-- Number of bits in the child part of a local shrinking argument. -/
noncomputable def demand (us : List X.network.Site) : ℕ := (us.map (width X)).sum

theorem payload_length (xs : List (Child X)) :
    (xs.flatMap (Child.payload X)).length = demand X (xs.map Child.site) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, ih, Child.payload_length]
    rfl

/-- Split an arbitrary sufficiently long tape at every old-site boundary. -/
theorem chooseChildren (us : List X.network.Site) (bs : List Bool)
    (enough : demand X us ≤ bs.length) :
    ∃ xs : List (Child X), xs.map Child.site = us ∧
      xs.flatMap (Child.payload X) ++ bs.drop (demand X us) = bs := by
  induction us generalizing bs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons u us ih =>
    have count : demand X (u :: us) = width X u + demand X us := rfl
    rw [count] at enough
    obtain ⟨x, hx, head⟩ := choose_payload X u bs (by change width X u ≤ _; omega)
    have len : (x.payload X).length = width X u := by rw [Child.payload_length, hx]; rfl
    rw [len] at head
    obtain ⟨xs, hxs, rest⟩ := ih (bs.drop (width X u)) (by simp; omega)
    exact ⟨x :: xs, by simp [hx, hxs], by
      rw [count, ← List.drop_drop, List.flatMap_cons, List.append_assoc, rest, head]⟩

/-- The row and its old-layer directory are read at their actual machine addresses. -/
structure Descriptor (w : ℕ) (X : State a g) where
  /-- External start address of the selected row's consecutive child-node pointers. -/
  source : ℕ
  /-- Machine-word address of the old-layer directory supplying the child argument geometry. -/
  directoryBase : Word w
  /-- Old sites of this parent's selected placement fiber, in the same order as the stored
  child-node pointers. -/
  sites : List X.network.Site

variable {X} (A : Arena) (T : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)

/-- Physical bounds and contents required for the finite descriptor scan. -/
structure Resident (endAddr : ℕ) (node : Word w) (row : Descriptor w X) : Prop where
  directory : (ChildScan.directory a older cap A T).Stored m row.directoryBase
  children : Row m node.val row.source (row.sites.map fun u => (childNode X older cap u : Word w))
  nodes : ∀ u ∈ row.sites, childNode X older cap u < 2 ^ w
  stack : ∀ u ∈ row.sites, endAddr ≤ A.base (childNode X older cap u)
  stride : ∀ u ∈ row.sites, width X u ≤ A.stride
  room : ∀ u ∈ row.sites, A.base (childNode X older cap u) + width X u < 2 ^ w

variable {A T m older cap}

private theorem requirements {node : Word w} {row : Descriptor w X}
    (h : Resident A T m older cap endAddr node row) (xs : List (Child X))
    (sites : xs.map Child.site = row.sites) :
    Row m node.val row.source (xs.map fun x => (childNode X older cap x.site : Word w)) ∧
    (∀ x ∈ xs, childNode X older cap x.site < 2 ^ w) ∧
    (∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w) ∧
    (∀ q ∈ xs.map (Child.packet X older cap), q.Fits A w endAddr) := by
  have member (x : Child X) (hx : x ∈ xs) : x.site ∈ row.sites := sites ▸ List.mem_map_of_mem hx
  refine ⟨?_, fun x hx => h.nodes _ (member x hx), fun x hx => ?_, ?_⟩
  · simpa only [← sites, List.map_map, Function.comp_def] using h.children
  · rw [Child.payload_length]
    exact h.room _ (member x hx)
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    have hu := member x hx
    exact ⟨h.stack _ hu, (Child.payload_length X x) ▸ h.stride _ hu,
      (Child.payload_length X x) ▸ (h.room _ hu).le⟩

variable (A T m older cap) (desc : Word w → Descriptor w X)

/-- The header trace, per-child trace and actual addressed writes of this decode. -/
noncomputable def outcome (node : Word w) (saved : Scratch w endAddr) (xs : List (Child X)) :
    Outcome w endAddr (List (Child X)) where
  value := xs
  trace := ChildHeader.events m node (desc node).directoryBase ++ events X T m (desc node).source xs
  updated := writePackets A (xs.map (Child.packet X older cap)) saved

/-- On a complete prefix the native child stage uses precisely the values decoded
from that prefix. The first kernel bit remains at the start of the returned suffix. -/
noncomputable def reader : Reader w endAddr (List (Child X)) := fun node saved bs =>
  let us := (desc node).sites
  if h : demand X us ≤ bs.length then
    let xs := (chooseChildren X us bs h).choose
    some (outcome A T m older cap desc node saved xs, bs.drop (demand X us))
  else none

theorem reader_some {node : Word w} {saved : Scratch w endAddr} {bs rest : List Bool}
    {out : Outcome w endAddr (List (Child X))}
    (h : reader A T m older cap desc node saved bs = some (out, rest)) :
    out.value.map Child.site = (desc node).sites ∧
      out = outcome A T m older cap desc node saved out.value ∧
      bs = out.value.flatMap (Child.payload X) ++ rest := by
  simp only [reader] at h
  split at h
  next enough =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have spec := (chooseChildren X (desc node).sites bs enough).choose_spec
    exact ⟨spec.1, rfl, spec.2.symm⟩
  next => contradiction

theorem reader_none_iff {node : Word w} {saved : Scratch w endAddr} {bs : List Bool} :
    reader A T m older cap desc node saved bs = none ↔ bs.length < demand X (desc node).sites := by
  by_cases h : demand X (desc node).sites ≤ bs.length
  · simp [reader, h]
  · simp [reader, h, lt_of_not_ge h]

private theorem outcome_bits (node : Word w) (saved : Scratch w endAddr) (xs : List (Child X)) :
    choiceBits (outcome A T m older cap desc node saved xs).trace =
      xs.flatMap (Child.payload X) := by
  simp only [outcome, PrimedInputRAM.Flow.choiceBits_append, (ChildHeader.cost ..).2.2,
    (events_cost ..).1, List.nil_append]

/-- Tape splitting holds even if no live DFS stack represents this particular scratch. -/
theorem splitBits {node : Word w} {saved : Scratch w endAddr} {bs rest : List Bool}
    {out : Outcome w endAddr (List (Child X))}
    (h : reader A T m older cap desc node saved bs = some (out, rest)) :
    bs = choiceBits out.trace ++ rest := by
  obtain ⟨_, eqn, hb⟩ := reader_some A T m older cap desc h
  exact (congrArg (fun o => choiceBits o.trace) eqn |>.trans
    (outcome_bits A T m older cap desc ..)) ▸ hb

variable {M : Machine w p r k} {s : ChildScan.Sites a p} {reg : Fin 16 ↪ Fin r}
  {source : ChildSlots.Names (2 ^ a) r k} {ret : Fin p} {header : Fin 17 → Fin p}

/-- The child reader starts at its first instruction with the popped parent, directory address,
slot ordinals, and resident external rows required by its scan. -/
structure Entry (header : Fin 17 → Fin p) (reg : Fin 16 ↪ Fin r) (M : Machine w p r k)
    (source : ChildSlots.Names (2 ^ a) r k) (endAddr : ℕ) (node : Word w)
    (c : Config w p r) : Prop where
  pc : c.pc = header 0
  parent : c.reg (reg 7) = node
  directory : c.reg (reg 8) = (desc node).directoryBase
  ordinals : source.Valid M c
  resident : Resident A T m older cap endAddr node (desc node)

variable {A T m older cap desc}

/-- The register-bank or public-operand scan realizes the decoder on every tape.
The postcondition can use the exact native stores and every untouched register to
prepare the next stage at the common return label. -/
theorem realizesWith {dfs : Fin 9 ↪ Fin r}
    (hh : ChildHeader.Linked M header reg (s.guard 0))
    (hl : ChildScan.LinkedWith M s reg source ret)
    (apart : source.Apart reg) (rep : T.ActualColumns X m) (strideFit : cap + 2 < 2 ^ w)
    (separate : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → ∀ j, dfs i ≠ reg j)
    {pre : Word w → Config w p r → Prop} {post : List (Child X) → Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → Entry A T m older cap desc header reg M source endAddr node c)
    (finish : ∀ node c d xs, pre node c → xs.map Child.site = (desc node).sites → d.pc = ret →
      d.persistent = c.persistent →
      d.privateMem = storePackets A (xs.map (Child.packet X older cap)) c.privateMem →
      (∀ i, ChildHeader.Preserved reg i → i ∉ mutableRegs reg → d.reg i = c.reg i) →
      post xs node d) :
    Realizes (endAddr := endAddr) (reader A T m older cap desc) M m dfs pre post := by
  constructor
  · intro node c bs out rest hc got
    let h := start node c hc
    obtain ⟨sites, result, split⟩ := reader_some A T m older cap desc got
    obtain ⟨row, nodes, room, fits⟩ := requirements h.resident out.value sites
    obtain ⟨d, hd, per, mem, scratchEq, regs, native⟩ := native_stageWith hh hl apart rep
      out.value (desc node).source c h.ordinals h.pc
      (by rw [h.directory]; exact h.resident.directory)
      (by rw [h.parent]; exact row) strideFit nodes room
    have frame : ShrinkRole.Frame dfs endAddr c d := by
      refine ⟨fun i hi => regs (dfs i) (fun j _ => separate i hi j) ?_, fun z hz => ?_, per⟩
      · simp [mutableRegs, separate i hi]
      · rw [mem]
        exact storePackets_below A _ c.privateMem endAddr fits z hz
    have bits := (congrArg (fun o => choiceBits o.trace) result).trans
      (outcome_bits A T m older cap desc ..)
    refine ⟨bits ▸ split, d, finish node c d out.value hc sites hd per mem regs, frame,
      (scratchEq endAddr).trans (congrArg Outcome.updated result).symm, ?_⟩
    rw [bits, congrArg Outcome.trace result]
    simpa only [h.parent, h.directory, List.flatMap_map, Function.comp_def, Child.packet, outcome]
      using native
  · intro node c bs hc failed
    let h := start node c hc
    let xs : List (Child X) := (desc node).sites.map (fun u => ⟨u, fun _ _ => false⟩)
    have sites : xs.map Child.site = (desc node).sites := by simp [xs, Function.comp_def]
    obtain ⟨row, nodes, room, _⟩ := requirements h.resident xs sites
    apply reject_stageWith hh hl apart rep xs (desc node).source c h.ordinals h.pc
      (by rw [h.directory]; exact h.resident.directory) (by rw [h.parent]; exact row)
      strideFit nodes room bs
    rw [payload_length, sites]
    exact (reader_none_iff A T m older cap desc).mp failed

end PairSimulation.ShrinkRole.ChildArguments

end VPVNP
end Computability
end OAI
