import OAI.Hierarchy.DescentIssuedRootWork
import OAI.Hierarchy.DescentResetReceivedSourcePrice

namespace OAI
/-! Raw sender and candidate operand costs on the stage's actual paid rotor sources. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty DescentCompiler DescentDenseHostOrder DescentResetGates DescentFallbackPeriod
open DescentFallbackPeriod.Projected DescentSIMDLookup DescentPackedWalsh DescentPlainTerminal.Suffix
open DescentPackedColony.Phase.Arena DescentSharedLeafLookup DescentPackedColony DescentPackedPrivateMenu DescentSixParty.Chronology ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (S : AtomSchedule) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (k tail age D cf g receiverBatch nextBatch rootField metaBits chartSize wordBits : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S board k tail age D cf g receiverBatch nextBatch rootField metaBits chartSize wordBits calendar
variable {N c H G K R M hi lo t field Ht w bit : ℕ}
    (a : Receiver D ((calendar.take age).prod*256) N n k c H G K R M hi lo t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (capacity : Expr) (f fee full total portPitch : ℕ)
    (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage k (2^n))
    (oldHub : Bank) (dir : DescentResetNewActorDirectory.Layout) (actor : Bank)
    (floor : ℕ) (flags count inverse : Bank)
local notation "book" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId capacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "src" => a.atlasSources E stencil old stencilBase splitBank hubWidth peers oldId capacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "early" => EarlierBanks.fromRoot a book src oldId oldHub dir actor
local notation "org" => calendarOriginals S board k tail age D cf g receiverBatch nextBatch rootField metaBits chartSize wordBits
  calendar floor early
local notation "scene" => (A).fromOriginals floor org flags count inverse
local notation "U" => Receiver.readWork stencil.m old.count capacity

theorem issued_sender_price :
    (A).OperandPrice (scene) (sourceLimit (A).peer.shapes (U+64)) := by
  have rows:=a.issued_matrix_work E stencil old stencilBase splitBank hubWidth peers oldId capacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage H
  have sender:=EarlierBanks.sender_limit a book src oldId oldHub dir actor U rows
  exact original_price S board k tail age D cf g receiverBatch nextBatch rootField metaBits chartSize wordBits
    calendar floor early flags count inverse (U+64) sender.1 sender.2.1 sender.2.2

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
