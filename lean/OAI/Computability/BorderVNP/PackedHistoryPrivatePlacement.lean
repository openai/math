import OAI.Computability.BorderVNP.PackedHistoryRoutingControls
import OAI.Computability.BorderVNP.PackedHistoryRoutingFrame
import OAI.Computability.BorderVNP.PackedRoutingPrefix

/-! # The next native placement pass on each actual profile return

Use the physical return of the guarded history, its copied header and its 28 emitted
control words to run the private-placement instructions. The input consists of the real
cable triples, cell counts, private slots and live pairs from that return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork RoutingISA RoutingISA.Evaluator Crossing GeometryFrameEncoding
open Packing Packing.RoutingOutputs Diagonal.ExternalSew.FieldExport

variable {K s m n C d k b W a o guesses time origin : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable {S Z : Type*} [Fintype S] [Fintype Z]

set_option maxRecDepth 3500 in
/-- Every actual accepted history prefix runs the following native private-slot pass with
its certified linear charge. The indirect gap is read from the geometry output's eighth
control and the other dimensions from the actual retained public frame. -/
theorem profile_private_placement (D : Directory.Layout) (N : Network K P bits) (cell : N.Site → Fin C)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : CellAddressCircuit.Fields s m n C d k b (S ⊕ Bool)) (source : VerifierNetwork.Frame Z S) (input : Z → Bool)
    (rep : CellAddressPhysical.Represents N cell aux siteID edgeID portID F ((withSewnFields source).eval input))
    (ids : ∀ c, (F.cells c).val = c.val) (wireFit : ∀ c,
      CellAddresses.guessedSize N cell c+CellAddresses.siteSize N cell c aux+CellAddresses.suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (width : b ≤ W) (original : Fin D.entries → N.Site) (live : Fin a → P)
    (controls : Fin 28 → Fin (2^b)) (rest : VerifierNetwork.Frame (S ⊕ Bool) (Outputs o b))
    (body : Code) (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (mem : Memory W) (ok : Prop)
    (prior : (Fin guesses → Bool) → Memory W → Prop) :
    let head := (pub 0).val
    let words := fun i => ParseBatchSort.value (fun j => (controlEmitter F hk (siteID ∘ original) (portID ∘ live)
      rest source controls).eval input (i,j))
    let resident := fun guess after => prior guess after ∧ Header head origin m C D.entries (readings after) ∧
      readings after (head+92) = controlsBase origin m C D.entries a ∧ DirectoryHeader D head after
    let gap := (controls 8).val
    let l := privateLayout head origin m C D.entries D.description gap
    ProfilePaths body guesses pub mac bank mem ok time origin words resident →
    head+92 < 2^W → controlsBase origin m C D.entries a+8 < 2^W →
    (∀ c, CellAddresses.suppliedSize N cell c+gap+D.entries*D.description < 2^W) →
    ∀ v : Returns body pub mac bank mem,
      BoundedRun pub mac PrivatePlacement.program v.val.2.1 v.val.2.2
        (PrivatePlacement.setup.slots+(D.entries*15+1)) (fun z => l.Image (readings v.val.2.2) D.entries z.mem) := by
  intro head words resident gap l paths frameRoom controlRoom bankRoom v
  obtain ⟨E,effects⟩ := paths.outputs (paths.passes.mp ⟨v⟩)
  obtain ⟨g,rfl⟩ := E.surjective v
  let h := E g
  obtain ⟨_,header,ptr,fields⟩ := paths.memory h g (effects g).1
  obtain ⟨img,_,controlWords⟩ := profile_controls F hk (siteID ∘ original) (portID ∘ live) rest source controls input
    origin h.val.2.2 width (effects g).2.2.2
  have address : (bases origin m C D.entries).livePairs < 2^W := by dsimp only [controlsBase] at controlRoom; omega
  have fits : readings h.val.2.2 (head+92)+8 < 2^W := ptr ▸ controlRoom
  have readGap : readings h.val.2.2 (readings h.val.2.2 (head+92)+8) = gap := ptr ▸ controlWords 8
  exact img.private_run N cell aux siteID edgeID portID F rep ids wireFit original live pub mac h.val.2.1 h.val.2.2
    origin D.description gap header fields.entries fields.description readGap frameRoom fits address bankRoom

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
