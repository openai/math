import OAI.Computability.BorderVNP.PackedHistoryPrivatePlacement
import OAI.Computability.BorderVNP.PackedRoutingDemandHeader
import OAI.Computability.BorderVNP.PackedRoutingPublishedRun

/-! # The positive demand directory on each real chosen profile return

The actual return carries the installed ordinary and extended scalar words, the emitted
28 controls, and the final placement image. Both native placement passes continue from
that return's registers and memory, with no further profile choice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork RoutingISA RoutingISA.Evaluator Crossing GeometryFrameEncoding
open Packing Packing.RoutingOutputs Diagonal.ExternalSew.FieldExport TeamContraction.ProcessorSlots
open DiagonalResidueRAM

variable {K s m n C d k b W o guesses time origin dg : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable {S Z : Type*} [Fintype S] [Fintype Z]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
/-- On every accepting execution of the real profile reader, the private prefix and
directory scanner publish exactly the chosen physical rows into the reserved workspace.
The initial scalar words are decoded from the actual startup. -/
theorem profile_demand_publication (D : Directory.Layout) (N : Network K P bits) (cell : N.Site → Fin C)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : CellAddressCircuit.Fields s m n C d k b (S ⊕ Bool)) (source : Frame Z S) (input : Z → Bool)
    (rep : CellAddressPhysical.Represents N cell aux siteID edgeID portID F ((withSewnFields source).eval input))
    (ids : ∀ c, (F.cells c).val = c.val) (wireFit : ∀ c,
      CellAddresses.guessedSize N cell c+CellAddresses.siteSize N cell c aux+CellAddresses.suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (width : b ≤ W) (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
    (controls : Fin 28 → Fin (2^b)) (rest : Frame (S ⊕ Bool) (Outputs o b))
    (arena : StartupArena) (team : Fin arena.teams) (slot : ℕ) (p : ReferencePacket W dg)
    (other : Arg → Word W) (body : Code) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (mem : Memory W) (ok : Prop)
    {PF : Pins.ProcessorFields (arena.operands team slot p).layout} (frame : BroadcastFrame) (A : AdviceLayout)
    (headerBits : List Bool) (extent : ℕ) :
    let a := D.teams*D.sites
    let B := arena.operands team slot p
    let pub := B.bank (core (withDemandBase other arena.next) origin m C)
    let words := fun i => ParseBatchSort.value (fun j => (controlEmitter F hk (siteID ∘ original) (portID ∘ live)
      rest source controls).eval input (i,j))
    let resident := fun g after => BootResidence (F:=PF) (k:=guesses) arena team slot p frame A pub mac headerBits mem bank g after ∧
      Header arena.frame origin m C D.entries (readings after) ∧
      readings after (arena.frame+92) = controlsBase origin m C D.entries a ∧ DirectoryHeader D arena.frame after
    let q := privateLayout arena.frame origin m C D.entries D.description (controls 8).val
    let t := bases origin m C D.entries
    ProfilePaths body guesses pub mac bank mem ok time origin words resident →
    B.Fits W → D.teams = B.layout.teams ∧ D.processors = B.layout.processors ∧
      D.literal = B.layout.literal ∧ D.link = B.layout.link →
    D.DestinationBounds → 0 < D.teams → 0 < D.fields → D.processors ≤ D.sites → D.entries ≤ a →
    arena.next+7*D.candidates ≤ origin → controlsBase origin m C D.entries a+8 < 2^W →
    (∀ c, CellAddresses.suppliedSize N cell c+(controls 8).val+D.entries*D.description ≤ extent) →
    Directory.ISA.wordBound (Directory.ISA.placementBound D t.privatePairs t.livePairs extent) < 2^W →
    ∀ v : Returns body pub mac bank mem, ∃ (es fs : List (TeamRAM.Event W)) (z u : Bank W) (mid : Memory W),
      let rows := D.directory (Directory.ISA.placement (readings mid) t.privatePairs)
        (Directory.ISA.placement (readings mid) t.livePairs)
      let result := Directory.ISA.publish mid arena.frame arena.next rows
      Runs pub mac PrivatePlacement.program v.val.2.1 v.val.2.2 es z mid ∧
      q.Image (readings v.val.2.2) D.entries (readings mid) ∧
      Runs pub mac Directory.ISA.program z mid fs u result ∧
      Runs pub mac (.seq PrivatePlacement.program Directory.ISA.program) v.val.2.1 v.val.2.2 (es++fs) u result ∧
      traceCost (es++fs) ≤ deliveryScanTicks D.entries D.teams D.sites ∧
      ∀ ev ∈ es++fs, ev.choices = [] ∧ ev.sign = .plus := by
  intro a B pub words resident q t paths fit dims bounds teams fields sites originalCap reserve controlRoom cap wordRoom v
  obtain ⟨E,effects⟩ := paths.outputs (paths.passes.mp ⟨v⟩)
  obtain ⟨g,rfl⟩ := E.surjective v
  let h := E g
  obtain ⟨⟨_,z,saved,_,boot,kept⟩,header,ptr,ext⟩ := paths.memory h g (effects g).1
  have same : (pub 0).val = arena.frame := B.frameBase_word _ fit
  have first := (resident_frames arena team slot p (Pins.extendGuess g) same boot kept).1
  have low : arena.frame+112 ≤ arena.next := by
    dsimp [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
    omega
  have nextRoom : arena.next < 2^W :=
    ((Nat.le_add_right ..).trans reserve).trans_lt
      ((show origin ≤ controlsBase origin m C D.entries a by dsimp [controlsBase,bases]; omega).trans_lt (by omega))
  have ext' : DirectoryHeader D (pub 0).val h.val.2.2 := same ▸ ext
  obtain ⟨shape,base⟩ := decoded_demand_header D B other arena.next origin m C h.val.2.2 dims fit nextRoom fields first ext'
  obtain ⟨img,_,control⟩ := profile_controls F hk (siteID ∘ original) (portID ∘ live) rest source controls input
    origin h.val.2.2 width (effects g).2.2.2
  have run := img.publish_directory D N cell aux siteID edgeID portID F rep ids wireFit original live
    origin arena.next (controls 8).val extent pub mac h.val.2.1 h.val.2.2 (same ▸ header) shape base
    (by rw [same,ptr]; exact control 8) (by rw [same,ptr]; exact controlRoom)
    (by rw [same]; omega) reserve bounds teams fields sites originalCap cap wordRoom
  simpa only [same] using run

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
