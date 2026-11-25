import OAI.Computability.BorderVNP.PackedHistoryBootPaths
import OAI.Computability.BorderVNP.PackedRoutingControls
import OAI.Computability.BorderVNP.GeometryAdviceAllocation

/-! # Routing and delivery operands after the native signed pack-history prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction TeamContraction.ProcessorSlots GeometryAdvice
open Packing RoutingOutputs DiagonalResidueRAM
open private PinClear.read from OAI.Computability.BorderVNP.PackedHistoryPreparedInput

variable {w d : ℕ} (arena : StartupArena) (team : Fin arena.teams) (slot : ℕ) (p : ReferencePacket w d)
local notation "B" => arena.operands team slot p
variable {f : BroadcastFrame} {A : AdviceLayout}
variable {bits : List Bool} {bank : Bank w} {saved after : Memory w}

/-- The actual ordinary and extended frame words survive every returning guessed pin
and profile evaluation. The needed address separation follows from the allocated arena. -/
theorem resident_frames {F : Pins.ProcessorFields (arena.operands team slot p).layout} {pub : Arg → Word w} (guess : ℕ → Bool) (base : (pub 0).val = arena.frame)
    (boot : JointHeader.BootHeaderState F f A p pub bits bank saved)
    (resident : ∀ j < arena.next, after j = Pins.preparedMemory (B).layout guess saved (B).layout.count j) :
    (∀ i : Fin 31, after ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
      (∀ i : Fin 81, after ((pub 0).val+31+i.val) = p.extension i) := by
  have clear := (arena_pin_clear arena team slot p).2.1
  have past : arena.frame+112 ≤ arena.next := by
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase StartupArena.broadcastBase StartupArena.dense
    omega
  have keep (i : ℕ) (hi : i < 112) : after ((pub 0).val+i) = saved ((pub 0).val+i) := by
    rw [base]
    exact (resident _ ((Nat.add_lt_add_left hi _).trans_le past)).trans (PinClear.read clear guess saved i hi)
  refine ⟨fun i => (keep i.val (by have := i.isLt; omega)).trans (boot.core i),fun i => ?_⟩
  simpa only [Nat.add_assoc] using (keep (31+i.val) (by have := i.isLt; omega)).trans
    (by simpa only [Nat.add_assoc] using boot.extension i)

/-- Install the actual delivery directory parameters in the five unclaimed extension
fields read by the directory setup. The code uses one plus the last of these fields. -/
def directoryFields (old : Fin 81 → Word w) (D : Directory.Layout) (i : Fin 81) : Word w :=
  match i.val+31 with
  | 66 => word w D.entries
  | 67 => word w D.sites
  | 68 => word w D.block
  | 69 => word w D.description
  | 70 => word w (D.fields-1)
  | _ => old i

/-- Exact routing operands and all unrelated extension values after the signed prefix. -/
structure RoutingFrame (head origin edges cells entries live : ℕ) (old : Fin 81 → Word w) (mem : Memory w) : Prop where
  header : Header head origin edges cells entries (readings mem)
  control : readings mem (head+92) = controlsBase origin edges cells entries live
  other (i : Fin 81) (free : i.val+31 ∉ [64,65,87,92,96,97,98,99,100,101,104,105,106,107,108]) :
    mem (head+31+i.val) = old i

/-- Recover the routing and secondary control pointers from the 112 returned words
of either native bootstrap. The seven-word delivery reserve may precede the geometry. -/
theorem routing_frame_of_words (ops : PacketOperands) (other : Arg → Word w) (old : Fin 81 → Word w)
    (origin edges cells entries live fresh reserve gates outputs width off ell : ℕ) (after : Memory w)
    (room : controlsBase origin edges cells entries live < 2^w) :
    let args := core other origin edges cells
    let pub := ops.bank args
    (∀ i : Fin 31, after ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) →
    (∀ i : Fin 81, after ((pub 0).val+31+i.val) =
      Allocation.fields (controlsExtension old origin edges cells entries live) fresh reserve gates outputs width off ell i) →
    RoutingFrame (pub 0).val origin edges cells entries live old after := by
  intro args pub ordinary extended
  have c1 := (ordinary 6).trans (ops.bank_passthrough args 7 (by decide) (by decide))
  have c2 := (ordinary 7).trans (ops.bank_passthrough args 8 (by decide) (by decide))
  have c3 := (ordinary 11).trans (ops.bank_passthrough args 12 (by decide) (by decide))
  have ext (i : Fin 81) (skip : i.val+31 ∉ [96,97,98,99,100,101,104,105,106,107,108]) :
      after ((pub 0).val+(31+i.val)) = controlsExtension old origin edges cells entries live i := by
    rw [← Nat.add_assoc,extended,Allocation.fields_other _ _ _ _ _ _ _ _ i skip]
  have numeric := room
  dsimp [controlsBase,bases] at numeric
  constructor
  · constructor
    · exact (congrArg Fin.val c1).trans (word_val _ _ (by omega))
    · exact (congrArg Fin.val c2).trans (word_val _ _ (by omega))
    · exact (congrArg Fin.val c3).trans (word_val _ _ (by omega))
    · exact (congrArg Fin.val (ext 33 (by decide))).trans (word_val _ _ (by dsimp [bases]; omega))
    · exact (congrArg Fin.val (ext 34 (by decide))).trans (word_val _ _ (by dsimp [bases]; omega))
    · exact (congrArg Fin.val (ext 56 (by decide))).trans (word_val _ _ (by dsimp [bases]; omega))
  · exact (congrArg Fin.val (ext 61 (by decide))).trans (word_val _ _ room)
  · intro i skip
    have geo : i.val+31 ∉ [96,97,98,99,100,101,104,105,106,107,108] := fun bad =>
      skip (by simp only [List.mem_cons] at bad ⊢; tauto)
    have ctl : i.val+31 ≠ 92 := fun eq => skip (by simp [eq])
    have routing : i.val+31 ∉ [64,65,87] := fun bad =>
      skip (by simp only [List.mem_cons] at bad ⊢; tauto)
    rw [Nat.add_assoc,ext i geo,controlsExtension_other _ _ _ _ _ _ _ ctl,extension_other _ _ _ _ _ _ routing]

/-- The routing pointers in the real public bank and selected reader extension feed
the original, live and end-offset tables through the complete signed native prefix.
No physical frame slot needs to be supplied separately at its end. -/
theorem routing_header {F : Pins.ProcessorFields (arena.operands team slot p).layout} (other : Arg → Word w) (old : Fin 81 → Word w) (origin edges cells entries live : ℕ)
    (reserve gates outputs width off ell : ℕ) (guess : ℕ → Bool) (fits : (B).Fits w)
    (room : controlsBase origin edges cells entries live < 2^w)
    {fresh : ℕ} (packed : p.extension = Allocation.fields (controlsExtension old origin edges cells entries live)
      fresh reserve gates outputs width off ell) :
    let args := core other origin edges cells
    let pub := (B).bank args
    JointHeader.BootHeaderState F f A p pub bits bank saved →
    (∀ j < arena.next, after j = Pins.preparedMemory (B).layout guess saved (B).layout.count j) →
    RoutingFrame arena.frame origin edges cells entries live old after := by
  intro args pub boot resident
  have base : (pub 0).val = arena.frame := (B).frameBase_word args fits
  obtain ⟨ordinary,extended⟩ := resident_frames arena team slot p guess base boot resident
  rw [packed] at extended
  exact base ▸ routing_frame_of_words (B) other old origin edges cells entries live fresh reserve gates outputs width off ell
    after room ordinary extended

/-- The five scalar fields read by the public delivery directory at startup. -/
structure DirectoryHeader (D : Directory.Layout) (head : ℕ) (mem : Memory w) : Prop where
  entries : readings mem (head+66) = D.entries
  sites : readings mem (head+67) = D.sites
  block : readings mem (head+68) = D.block
  description : readings mem (head+69) = D.description
  fields : readings mem (head+70) = D.fields-1

/-- With the directory's length-only operands in the chosen extension, the real routing
header also supplies all five actual delivery dimensions. -/
theorem routing_directory {head origin edges cells live : ℕ} (old : Fin 81 → Word w) (D : Directory.Layout)
    (h : RoutingFrame head origin edges cells D.entries live (directoryFields old D) after)
    (room : D.entries < 2^w ∧ D.sites < 2^w ∧ D.block < 2^w ∧ D.description < 2^w ∧ D.fields-1 < 2^w) :
    Header head origin edges cells D.entries (readings after) ∧
      readings after (head+92) = controlsBase origin edges cells D.entries live ∧ DirectoryHeader D head after := by
  have atWord (i : Fin 81) (free : i.val+31 ∉ [64,65,87,92,96,97,98,99,100,101,104,105,106,107,108]) :
      (after (head+(31+i.val))).val = (directoryFields old D i).val := by
    simpa only [Nat.add_assoc] using congrArg Fin.val (h.other i free)
  refine ⟨h.header,h.control,?_,?_,?_,?_,?_⟩
  · exact (atWord 35 (by decide)).trans (word_val _ _ room.1)
  · exact (atWord 36 (by decide)).trans (word_val _ _ room.2.1)
  · exact (atWord 37 (by decide)).trans (word_val _ _ room.2.2.1)
  · exact (atWord 38 (by decide)).trans (word_val _ _ room.2.2.2.1)
  · exact (atWord 39 (by decide)).trans (word_val _ _ room.2.2.2.2)

/-- Populate the true ordinary routing operands in each team's signed site data before
the chosen reader replaces its packet-owned fields. -/
def routingSites {R r reg a : ℕ} (S : SiteData R r reg 32 w a) (origin edges cells : ℕ) :
    SiteData R r reg 32 w a :=
  {S with publicWords := fun u => core (S.publicWords u) origin edges cells}

/-- The postcondition exposed by every genuine returning chosen profile path. -/
def BootResidence {k : ℕ} {F : Pins.ProcessorFields (arena.operands team slot p).layout}
    (f : BroadcastFrame) (A : AdviceLayout) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (bits : List Bool) (initial : Memory w) (bank : Bank w) (guess : Fin k → Bool) (after : Memory w) : Prop :=
  ∃ trace z saved, Runs pub mac JointHeader.bootHeader bank initial trace z saved ∧
    JointHeader.BootHeaderState F f A p pub bits z saved ∧
    ∀ j < arena.next, after j = Pins.preparedMemory (arena.operands team slot p).layout
      (Pins.extendGuess guess) saved (arena.operands team slot p).layout.count j

/-- Attach the physical routing and directory frame to every returning path while
retaining its pin-specific low-memory assertion, sign, cost, and geometry outputs. -/
theorem ProfilePaths.with_routing_directory {k o time dest : ℕ} {mac : TeamOpcode.Macros w 8}
    {F : Pins.ProcessorFields (arena.operands team slot p).layout} {initial : Memory w} {body : Code}
    {words : Fin o → ℕ} {ok : Prop} (other : Arg → Word w) (old : Fin 81 → Word w)
    (D : Directory.Layout) (origin edges cells live reserve gates outputs width off ell : ℕ)
    (fits : (B).Fits w) (room : controlsBase origin edges cells D.entries live < 2^w)
    (directoryRoom : D.entries < 2^w ∧ D.sites < 2^w ∧ D.block < 2^w ∧ D.description < 2^w ∧ D.fields-1 < 2^w)
    {fresh : ℕ} (packed : p.extension = Allocation.fields (controlsExtension (directoryFields old D) origin edges cells D.entries live)
      fresh reserve gates outputs width off ell) :
    let pub := (B).bank (core other origin edges cells)
    let source := BootResidence (F := F) (k := k) arena team slot p f A pub mac bits initial bank
    ProfilePaths body k pub mac bank initial ok time dest words source →
    ProfilePaths body k pub mac bank initial ok time dest words (fun guess m => source guess m ∧
      Header arena.frame origin edges cells D.entries (readings m) ∧
      readings m (arena.frame+92) = controlsBase origin edges cells D.entries live ∧ DirectoryHeader D arena.frame m) := by
  intro pub source paths
  apply paths.map_memory
  intro guess mem path
  have original := path
  obtain ⟨trace,z,saved,_,post,resident⟩ := path
  have h := routing_header arena team slot p other (directoryFields old D) origin edges cells D.entries live
    reserve gates outputs width off ell (Pins.extendGuess guess) fits room packed post resident
  exact ⟨original,routing_directory old D h directoryRoom⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
