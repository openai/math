import OAI.Computability.VPVNP.PairSimulationMapCallRun

/-!
# Complete motif call table including initialization

A single fixed table loads the operand expressions from the private descriptor,
constructs the port directory, and enters the grouped map interpreter. The
expression compiler writes directly into the interpreter's allocated registers.
The descriptor pointer and the directory temporaries occupy distinct registers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapCallTable

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry
open MapEntryTable MapPortAgreement MapResidentAgreement MapCallSetup
open BurstRAM.PrivateRAM CompressorRecords
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (j : J) {r k p w u t : ℕ}

private noncomputable def number (X : Type*) [Finite X] : X ≃ Fin (Nat.card X) := by
  letI := Fintype.ofFinite X
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

variable {B z j} in
/-- Map-call register initialization expressions using the field of this party's anchor port to
locate its selector suffix. -/
noncomputable abbrev formulas (A : Allocation B z j r k)
    (args : Arg D E ≃ Fin (Fintype.card (Arg D E)))
    (slots : Register D E ≃ Fin (Fintype.card (Register D E))) :=
  recipes A args (MapDirectoryInit.portField (anchorPort G j)) slots

/-- Register layout for the compiler bank and the map, including their shared outputs. -/
structure Layout (r k : ℕ) where
  /-- Register and public-word allocation, with supply-edge order, for the grouped map
  interpreter entered after call initialization. -/
  core : Allocation B z j r k
  /-- Number the fields of the private call descriptor so each argument can be loaded by its
  word offset. -/
  args : Arg D E ≃ Fin (Fintype.card (Arg D E))
  /-- Number the map interpreter's logical registers to identify the corresponding
  initialization outputs. -/
  slots : Register D E ≃ Fin (Fintype.card (Register D E))
  /-- Place the expression compiler's output and scratch registers in the physical register
  file. Each output aliases its designated map register. -/
  vm : Fin (RegisterSetup.regCount (formulas core args slots)) ↪ Fin r
  /-- Register containing the base address of the private call descriptor during register
  initialization. -/
  ptr : Fin r
  /-- Two temporary registers for the port directory writer, holding the current directory cell
  and the selector-suffix pointer to store there. -/
  scratch : Fin 2 ↪ Fin r
  output : ∀ a, vm (RegisterSetup.output (formulas core args slots) (slots a)) = core.reg a
  vmApart : ∀ i, vm i ≠ ptr
  directoryApart : ∀ a i, core.reg a ≠ scratch i

/-- Allocate the output and expression scratch bank, then two directory temporaries
and the descriptor pointer. The seed supplies the public ports and edge order. -/
noncomputable def allocate (seed : Allocation B z j r k)
    (args : Arg D E ≃ Fin (Fintype.card (Arg D E)))
    (slots : Register D E ≃ Fin (Fintype.card (Register D E))) :
    Layout B z j (RegisterSetup.regCount (formulas seed args slots) + 3) k := by
  let f := formulas seed args slots
  let N := RegisterSetup.regCount f
  let vm : Fin N ↪ Fin (N + 3) := Fin.castAddEmb 3
  let out : Register D E ↪ Fin (N + 3) :=
    ⟨fun a ↦ vm (RegisterSetup.output f (slots a)), fun a b h ↦ slots.injective <|
      Fin.ext (congrArg (Fin.val : Fin N → ℕ) (vm.injective h))⟩
  let core : Allocation B z j (N + 3) k := ⟨out, seed.pub, seed.edgeOrder⟩
  let dir : Fin 2 ↪ Fin (N + 3) := (Fin.castAddEmb 1).trans (Fin.natAddEmb N)
  refine ⟨core, args, slots, vm, (Fin.last 2).natAdd N, dir, fun _ ↦ rfl, ?_, ?_⟩
  · intro i eq
    have he := congrArg Fin.val eq
    change i.val = N + 2 at he
    have hi : i.val < N := i.isLt
    omega
  · intro a i eq
    have he := congrArg Fin.val eq
    change (RegisterSetup.output f (slots a)).val = N + i.val at he
    have hi : (RegisterSetup.output f (slots a)).val < N := (RegisterSetup.output f (slots a)).isLt
    omega

namespace Layout

variable {B z j} (L : Layout B z j r k)

/-- Ordered assignments emitted by the expression compiler to initialize the map registers from
the private descriptor. -/
noncomputable abbrev lines := RegisterSetup.lines (formulas L.core L.args L.slots)

/-- Instruction addresses of the complete map call, partitioned into descriptor setup, port
directory construction, and grouped map evaluation. -/
noncomputable abbrev Address :=
  Fin L.lines.length ⊕ MapDirectoryInit.Address L.core ⊕ L.core.Address

variable (loc : L.Address → Fin p)

/-- Relocate an instruction address of the grouped map interpreter into the complete call
table. -/
def corePC (a : L.core.Address) := loc (.inr (.inr a))

/-- Relocate an address of the incident port directory initializer into the complete call
table. -/
def dirPC (a : MapDirectoryInit.Address L.core) := loc (.inr (.inl a))

/-- Program counter for a compiled register assignment, with the end of the assignment list
transferring control to the directory initializer. -/
noncomputable def initPC (n : ℕ) :=
  if h : n < L.lines.length then loc (.inl ⟨n, h⟩) else L.dirPC loc (.inl ())

/-- Emit the instruction at a call-table address, linking the last setup assignment to the
directory writer and the directory writer to the map's selector scan. -/
noncomputable def text : L.Address → Instr 2 p r k
  | .inl i => MapInitCompiler.instruction L.vm L.ptr L.lines[i.val] (L.initPC loc (i.val + 1))
  | .inr (.inl a) => MapDirectoryInit.text L.core L.scratch (L.dirPC loc)
      ((L.core.selector (L.corePC loc)).scan 0) a
  | .inr (.inr a) => L.core.text (L.corePC loc) a

/-- Keep the successful exit available as the caller's continuation. -/
noncomputable def installed : L.Address → Bool
  | .inr (.inr a) => L.core.installed a
  | _ => true

/-- Finite numbering of all descriptor setup, directory, and map interpreter addresses in this
layout. -/
noncomputable def locations : L.Address ≃ Fin (Nat.card L.Address) := number _

/-- Standalone template for a complete map call, starting with descriptor setup and using the
finite address numbering for all jump targets. -/
noncomputable def template : Template (Nat.card L.Address) r k :=
  ⟨2, L.initPC L.locations 0, fun pc ↦ L.text L.locations (L.locations.symm pc)⟩

theorem template_at (pub : Fin k → BurstRAM.Word w) (a : L.Address) :
    (L.template.instantiate w pub).code (L.locations a) = (L.text L.locations a).resize w := by
  simp [template, Template.instantiate]

/-- These are the precise instruction-level links of initialization and execution. -/
theorem links (M : Machine w p r k) (h : ∀ a, L.installed a = true →
    M.code (loc a) = (L.text loc a).resize w) :
    MapInitCompiler.Linked L.vm L.ptr M (L.initPC loc) L.lines ∧
    (∀ a, M.code (L.dirPC loc a) = (MapDirectoryInit.text L.core L.scratch (L.dirPC loc)
      ((L.core.selector (L.corePC loc)).scan 0) a).resize w) ∧
    ∀ a, L.core.installed a = true → M.code (L.corePC loc a) =
      (L.core.text (L.corePC loc) a).resize w := by
  refine ⟨?_, fun a ↦ h (.inr (.inl a)) rfl, fun a ha ↦ h (.inr (.inr a)) ha⟩
  intro i
  rw [initPC, dite_eq_left i.isLt]
  exact (h (.inl i) rfl).trans (MapInitCompiler.resize_instruction ..)

/-- Execute the installed finite table, including the operand and directory prefix. -/
theorem native_post (M : Machine w p r k) (h : ∀ a, L.installed a = true →
    M.code (loc a) = (L.text loc a).resize w)
    {demand : D → ℕ} {v : E → ℕ} {d : DemandBits src dst demand j}
    {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
    (X : MapEntry.Program.Workspace (L.core.program (L.corePC loc)) demand v d x t w)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) (pub : ∀ a, M.publicData (L.core.pub a) =
      Allocation.words fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w)) a)
    (histApart : ∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
      ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w))
    (c : Config w p r) (hc : c.pc = L.initPC loc 0)
    (input : Input L.core L.args (L.corePC loc) X L.ptr c) :
    (L.core.program (L.corePC loc)).RunsPost M c X.hist (L.lines.length +
      (1 + 3 * (ports G j L.core.edgeOrder).length) + MapNativeClock.cap B z j u)
      (MapCallSetup.Outside L.core (L.corePC loc) X)
      ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
        (selectorTable B) (selectorCode B) v j d x).1.map (List.map ord))
      (MapCallSetup.Success L.core (L.corePC loc) X sel ord c.privateMem) := by
  obtain ⟨init, dir, core⟩ := L.links loc M h
  exact MapCallSetup.run_post L.core L.args L.slots (L.corePC loc) X M core L.ptr L.scratch
    L.directoryApart (L.dirPC loc) dir fb fd fs sel ord pub histApart L.vm L.output L.vmApart
    (L.initPC loc) init (by simp [initPC]) c hc input

/-- The exact memory update implies preservation outside the written cells. -/
theorem native_framed (M : Machine w p r k) (h : ∀ a, L.installed a = true →
    M.code (loc a) = (L.text loc a).resize w)
    {demand : D → ℕ} {v : E → ℕ} {d : DemandBits src dst demand j}
    {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
    (X : MapEntry.Program.Workspace (L.core.program (L.corePC loc)) demand v d x t w)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) (pub : ∀ a, M.publicData (L.core.pub a) =
      Allocation.words fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w)) a)
    (histApart : ∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
      ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w))
    (c : Config w p r) (hc : c.pc = L.initPC loc 0)
    (input : Input L.core L.args (L.corePC loc) X L.ptr c) :
    (L.core.program (L.corePC loc)).RunsFramed M c X.hist (L.lines.length +
      (1 + 3 * (ports G j L.core.edgeOrder).length) + MapNativeClock.cap B z j u)
      (MapCallSetup.Outside L.core (L.corePC loc) X)
      ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
        (selectorTable B) (selectorCode B) v j d x).1.map (List.map ord)) :=
  (L.native_post loc M h X fb fd fs sel ord pub histApart c hc input).framed _

/-- The histogram and exit semantics of the native call. -/
theorem native (M : Machine w p r k) (h : ∀ a, L.installed a = true →
    M.code (loc a) = (L.text loc a).resize w)
    {demand : D → ℕ} {v : E → ℕ} {d : DemandBits src dst demand j}
    {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
    (X : MapEntry.Program.Workspace (L.core.program (L.corePC loc)) demand v d x t w)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) (pub : ∀ a, M.publicData (L.core.pub a) =
      Allocation.words fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w)) a)
    (histApart : ∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
      ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w))
    (c : Config w p r) (hc : c.pc = L.initPC loc 0)
    (input : Input L.core L.args (L.corePC loc) X L.ptr c) :
    (L.core.program (L.corePC loc)).Runs M c X.hist (L.lines.length +
      (1 + 3 * (ports G j L.core.edgeOrder).length) + MapNativeClock.cap B z j u)
      ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
        (selectorTable B) (selectorCode B) v j d x).1.map (List.map ord)) :=
  (L.native_framed loc M h X fb fd fs sel ord pub histApart c hc input).forget _

/-- The very same instruction and public-data bank implements the map for all live
inputs. Only the resident raw descriptor and the actual input bit slices are required. -/
theorem run_entryInput_post (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
    (L : Layout B (demandGrid B hp I.demand) I.party r k)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B (demandGrid B hp I.demand) e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) :
    let loc := L.corePC L.locations
    let P := L.core.program loc
    let pub := L.core.install
      (Allocation.words fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w))) (fun _ ↦ 0)
    let M := L.template.instantiate w pub
    let demand := demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ inputBits) I.supplyBits
    ∀ (X : MapEntry.Program.Workspace P I.demand I.payload demand supply t w)
      (c : Config w (Nat.card L.Address) r), c.pc = M.entry →
      Input L.core L.args loc X L.ptr c →
      (∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) →
      P.RunsPost M c X.hist (L.lines.length +
        (1 + 3 * (ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        (MapCallSetup.Outside L.core loc X)
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord))
        (MapCallSetup.Success L.core loc X sel ord c.privateMem) := by
  intro loc P pub M demand supply X c hc input disj
  exact L.native_post L.locations M (fun a _ ↦ L.template_at pub a) X fb fd fs sel ord
    (L.core.install_at (Allocation.words fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w)))
      (fun _ ↦ 0)) disj c hc input

/-- The exterior memory frame at a recorded native call. -/
theorem run_entryInput_framed (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
    (L : Layout B (demandGrid B hp I.demand) I.party r k)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B (demandGrid B hp I.demand) e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) :
    let loc := L.corePC L.locations
    let P := L.core.program loc
    let pub := L.core.install
      (Allocation.words fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w))) (fun _ ↦ 0)
    let M := L.template.instantiate w pub
    let demand := demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ inputBits) I.supplyBits
    ∀ (X : MapEntry.Program.Workspace P I.demand I.payload demand supply t w)
      (c : Config w (Nat.card L.Address) r), c.pc = M.entry →
      Input L.core L.args loc X L.ptr c →
      (∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) →
      P.RunsFramed M c X.hist (L.lines.length +
        (1 + 3 * (ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        (MapCallSetup.Outside L.core loc X)
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord)) := by
  intro loc P pub M demand supply X c hc input disj
  exact (run_entryInput_post hp I L fb fd fs sel ord X c hc input disj).framed _

/-- The same physical path evaluated on an actual recorded template invocation. -/
theorem run_entryInput (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
    (L : Layout B (demandGrid B hp I.demand) I.party r k)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B (demandGrid B hp I.demand) e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (sel : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) :
    let loc := L.corePC L.locations
    let P := L.core.program loc
    let pub := L.core.install
      (Allocation.words fb fd fs sel (fun e ↦ ((ord e).val : BurstRAM.Word w))) (fun _ ↦ 0)
    let M := L.template.instantiate w pub
    let demand := demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ inputBits) I.supplyBits
    ∀ (X : MapEntry.Program.Workspace P I.demand I.payload demand supply t w)
      (c : Config w (Nat.card L.Address) r), c.pc = M.entry →
      Input L.core L.args loc X L.ptr c →
      (∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) →
      P.Runs M c X.hist (L.lines.length + (1 + 3 * (ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord)) := by
  intro loc P pub M demand supply X c hc input disj
  exact (run_entryInput_framed hp I L fb fd fs sel ord X c hc input disj).forget _

end Layout

end PairSimulation.MapCallTable

end VPVNP
end Computability
end OAI
