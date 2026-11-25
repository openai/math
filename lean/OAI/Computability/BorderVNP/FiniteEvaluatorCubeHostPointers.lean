import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostSource
import OAI.Computability.BorderVNP.CubeRouteJointPacket
import OAI.Computability.BorderVNP.CubeRoutePreparedEntry
import OAI.Computability.BorderVNP.CubeRouteWriterReadback
import OAI.Computability.BorderVNP.RoutingISASignedFrame
import OAI.Computability.BorderVNP.CubeScatterOwnedStaticWords

/-! # The host scatter's original and returned public operands

The static host table pointers and packet strides are words of the selected
signed reference packet. The packet base and number of blocks are loaded
indirectly through the installed secondary header. The native directory,
transmission, and owned-group returns preserve these particular reads.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open VPVNP.BurstRAM BorderVNP.Cube RoutingISA RoutingISA.Transmission LocalRow PackedHistoryCircuit

/-- Primary-frame positions of the fixed host addresses and packet shape. -/
def hostPointerFields : List ℕ := [48,56,58,72,88,91,93,94]

/-- All eight length-only operands have their allocated values in this actual memory. -/
def HostPointers (a : CubeArena.Layout) (frame : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ k ∈ hostPointerFields, ∀ value, a.operand k = some value → mem (frame+k) = value

private theorem pointer_fit {w : ℕ} (a : CubeArena.Layout)
    (room : a.stop < 2^w) (fixed : templateLimit a.n a.b a.h a.K a.s < 2^w)
    {k v : ℕ} (field : k ∈ hostPointerFields) (operand : a.operand k = some v) : v < 2^w := by
  obtain ⟨_,labels,group,pair,host,records,reserved,endRoom⟩ := a.writer_order
  have ordPower : a.ordinalBase+a.cables=a.powerBase := rfl
  have powerGroup : a.powerBase+(a.n+1)≤a.groupWeights := a.group_order.2.2.2.2.2.2.2.1
  have alpha : a.dataMean+a.alphabet=a.widthBase := rfl
  have widthOrd : a.widthBase≤a.ordinalBase := Nat.le_add_right ..
  have single := a.separated.2.1
  have vertex : a.vertexBase ≤ a.publicBase := Nat.le_add_right ..
  have selector := selector_room a.n a.b a.h a.K a.s
  unfold templateLimit at fixed
  simp only [hostPointerFields,List.mem_cons,List.not_mem_nil,or_false] at field
  rcases field with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [CubeArena.Layout.operand,Option.some.injEq] at operand <;> subst v <;> omega

variable {w : ℕ} (task : SignedTaskArena.Layout) (old : Fin 81 → Word w) (D : Packing.Directory.Layout)
variable (origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell : ℕ)

local notation "selected" => signedProfileExtension task old D origin edges cells raw team subtotalWidth fresh profile gates outputs width off ell

/-- Each of the host words keeps its exact unsigned spelling through the signed
report, geometry, directory and header overlays of the one physical literal. -/
theorem signed_host_pointer (i : Fin 81) (field : 31+i.val ∈ hostPointerFields) (v : ℕ)
    (operand : task.cube.operand (31+i.val)=some v)
    (room : task.cube.stop < 2^w) (fixed : templateLimit task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s < 2^w) :
    (selected i).val = v := by
  have range := pointer_fit task.cube room fixed field operand
  rw [signedProfileExtension_taskWord,task.extension_cube,CubeArena.Layout.extension,operand,Option.elim_some]
  · exact Nat.mod_eq_of_lt range
  all_goals
    simp only [hostPointerFields,List.mem_cons,List.not_mem_nil,or_false,not_or] at field ⊢
    omega

/-- Any genuine boot of this selected reference packet has all the static host
words. Only those eight addresses will be transported to the physical scatter. -/
theorem host_pointers_boot {pub : Arg → Word w} {f : BroadcastFrame} {bits : List Bool} {m : Memory w}
    (pins : BootPins pub f selected bits m) (room : task.cube.stop < 2^w)
    (fixed : templateLimit task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s < 2^w) :
    HostPointers task.cube (pub 0).val (readings m) := by
  intro k field v operand
  have limits : 31 ≤ k ∧ k ≤ 111 := by
    simp only [hostPointerFields,List.mem_cons,List.not_mem_nil,or_false] at field
    omega
  let i : Fin 81 := ⟨k-31,by omega⟩
  have index : 31+i.val=k := by dsimp [i]; omega
  have ext := pins.extension i
  rw [Nat.add_assoc,index] at ext
  exact (congrArg Fin.val ext).trans (signed_host_pointer task old D origin edges cells raw team subtotalWidth
    fresh profile gates outputs width off ell i (index ▸ field) v (index ▸ operand) room fixed)

variable {a : CubeArena.Layout} {frame : ℕ} {before after : ℕ → ℕ}

/-- The eight host operands survive any memory pass preserving their actual addresses. -/
theorem HostPointers.transfer (p : HostPointers a frame before)
    (keep : ∀ k ∈ hostPointerFields, after (frame+k) = before (frame+k)) : HostPointers a frame after :=
  fun k hk v operand => (keep k hk).trans (p k hk v operand)

/-- The original signed pointers survive both actual public directory writers. -/
theorem HostPointers.after_directory (p : HostPointers a frame before)
    {controls R : ℕ} {axis : Fin (a.n+1)} {input : ℕ → ℕ}
    (entry : Evaluator.NativeEntry a frame controls axis R input before after)
    (low : frame+112 ≤ a.header.header) : HostPointers a frame after := by
  apply p.transfer
  intro k field
  simp only [hostPointerFields,List.mem_cons,List.not_mem_nil,or_false] at field
  exact entry.low _ (by omega)

/-- The native data writer changes the record count and output rows. Its real
shared-writer entry still contains the original signed host words. -/
theorem HostPointers.after_data {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {width R controls : ℕ} {axis : Fin (a.n+1)} {rr rt : Bank w} {initial last : Memory w}
    {es : List (TeamRAM.Event w)} {input : ℕ → ℕ}
    (p : HostPointers a (pub 0).val (readings initial))
    (W : Evaluator.WriterHistory a.n width pub mac rr initial es rt last)
    (entry : Evaluator.NativeEntry a (pub 0).val controls axis R input (readings initial) (readings W.dataInput))
    (ready : Evaluator.DataReady pub W.dataInput)
    (records : (DataWriter.layout (readings pub) (readings W.dataInput)).output = a.records)
    (low : (pub 0).val+112 ≤ a.header.header) : HostPointers a (pub 0).val (readings W.sharedInput) := by
  apply (p.after_directory entry low).transfer
  intro k field
  simp only [hostPointerFields,List.mem_cons,List.not_mem_nil,or_false] at field
  have before : (pub 0).val+k < a.records := by have := Evaluator.secondary_le_records a; omega
  apply congrArg Fin.val
  rw [W.dataImage ready,DataWriter.publish,Function.update_of_ne (by omega : (pub 0).val+k ≠ (pub 0).val+13),
    Packing.Directory.ISA.putWords_outside _ _ _ _ (.inl (records ▸ before))]

/-- The stored primary header pointer supplies both indirect operands at the native
host scatter, including the packet address at offset eight. -/
theorem host_header_reads {src final : ℕ → ℕ} {team axis : ℕ} {owner : Fin a.header.d → ℕ}
    {pub : Arg → ℕ} {rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ}
    (scanner : a.ScannerWords frame team axis owner pub src rows)
    (primary : ∀ k ∈ [61,63], final (frame+k)=src (frame+k))
    (secondary : ∀ k ∈ [7,8], final (a.header.header+k)=src (a.header.header+k)) :
    let l := HostScatter.Layout.fromFrame frame final
    l.packets = a.header.packetBase ∧ l.blocks = a.header.blocks ∧ l.bc = a.h*a.b := by
  have header := scanner.setup.header
  change src (pub 0+63)=a.header.header at header
  rw [scanner.frameBase] at header
  have width := scanner.setup.bc
  change src (pub 0+61)=a.h*a.b at width
  rw [scanner.frameBase] at width
  change final (final (frame+63)+8)=_ ∧ final (final (frame+63)+7)=_ ∧ final (frame+61)=_
  rw [primary 63 (by decide),header,secondary 8 (by decide),secondary 7 (by decide),primary 61 (by decide)]
  exact ⟨scanner.setup.bank,scanner.setup.blocks,width⟩

/-- The complete host metadata and both source bases, assembled from actual
static pointer words and indirect secondary-header readback. -/
theorem HostPointers.host_words (p : HostPointers a frame after)
    (dynamic : let l := HostScatter.Layout.fromFrame frame after
      l.packets = a.header.packetBase ∧ l.blocks = a.header.blocks ∧ l.bc = a.h*a.b) :
    HostWords a frame after ∧ (HostScatter.Layout.fromFrame frame after).packets = a.header.packetBase ∧
      (HostScatter.Layout.fromFrame frame after).singles = a.singleBank ∧
      (HostScatter.Layout.fromFrame frame after).selectorWidth = Tally.selectorWidth a.n a.K a.h :=
  ⟨⟨p 48 (by decide) _ rfl,p 56 (by decide) _ rfl,p 58 (by decide) _ rfl,p 72 (by decide) _ rfl,
      p 91 (by decide) _ rfl,dynamic.2.1,dynamic.2.2,p 93 (by decide) _ rfl⟩,
    dynamic.1,p 88 (by decide) _ rfl,p 94 (by decide) _ rfl⟩

end FiniteEvaluator.CubeAllocation

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator.CubeAllocation

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
variable {group : Fin ar.header.d → Fin (R+1)} {F : TeamRows.Returns (Fin (R+1)) ar w}
variable {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
variable {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

/-- The actual returned owned-group memory has every static and indirect host
scatter operand. The native writes to the event and vertex counters lie outside
each required primary or secondary frame word. -/
theorem SharedWriters.owned_host_words (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (static : HostPointers ar g.frame (src u)) :
    let frame := readings (F.pub u) 0
    let mem := readings (F.output u)
    let l := HostScatter.Layout.fromFrame frame mem
    HostWords ar frame mem ∧ l.packets = ar.header.packetBase ∧ l.singles = ar.singleBank ∧
      l.selectorWidth = Tally.selectorWidth ar.n ar.K ar.h := by
  intro frame mem l
  have actual : frame = readings (H u).pub 0 := by dsimp only [frame]; rw [handoff.pub u]
  have base : g.frame = frame := (handoff.frame u).trans actual.symm
  have low := (handoff.room u).primary
  rw [←actual] at low
  have bounds := ar.writer_order
  have below : ar.header.header+13 ≤ ar.records := by omega
  have primary (k : ℕ) (endFrame : k < 112) (emit : k ≠ 13) (vertex : k ≠ 46) :
      mem (frame+k) = src u (frame+k) :=
    writer.owned_output_static symbols handoff receipt u _ (by omega) (.inl (by omega))
      (by rw [base]; omega) (by change frame+k ≠ frame+46; omega)
  rw [base] at static
  apply HostPointers.host_words
  · apply static.transfer
    intro k field
    simp only [hostPointerFields,List.mem_cons,List.not_mem_nil,or_false] at field
    exact primary k (by omega) (by omega) (by omega)
  · have scanner := handoff.source u
    rw [←actual] at scanner
    apply host_header_reads scanner
    · intro k field
      simp only [List.mem_cons,List.not_mem_nil,or_false] at field
      exact primary k (by omega) (by omega) (by omega)
    · intro k field
      simp only [List.mem_cons,List.not_mem_nil,or_false] at field
      exact writer.owned_output_static symbols handoff receipt u _ (by omega) (.inl (by omega))
        (by rw [base]; omega) (by change ar.header.header+k ≠ frame+46; omega)

end TeamContraction

end BorderVNP
end Computability
end OAI
