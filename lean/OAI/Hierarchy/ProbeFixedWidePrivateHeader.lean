import OAI.Hierarchy.ProbeFixedWideSignedBoot
import OAI.Hierarchy.ProtocolRAMChargedMasterLocal
import OAI.Hierarchy.TaggedWireHeaderLocal
import OAI.Hierarchy.TaggedWireFixedAdmission

namespace OAI
/-! # The actual charged wide input carries exactly the independent chronological selector tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets CatalystArchive
open Tagged WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies

theorem wide_signed_words_local (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) :
    AdviceLocal (v.wideSignedWords h width stock M π o) := by
  unfold wideSignedWords
  apply chargedMasterWords_local

/-- Private histogram pages can be installed in the original raw payload and passed through
every true input constructor, or installed directly on the same fully loaded public input. -/
theorem wide_signed_header (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
    (room : (A).endAddress v.mesh<2^w) (count : v.menu.copiesAt v.copyScale width<2^w) :
    let reader:=v.nativeSelector P h width r banks src tbl dst owners room count
    let es:=events v.mesh
    let L:=reader.format.windows
    ∀(bits : Bits (CalendarTape.bits reader.format.slot es)) (seed : Boot.Tape h D),
      v.wideSignedWords h width stock M π o (L.header es bits seed)=
        L.header es bits (v.wideSignedWords h width stock M π o seed) := by
  intro reader es L bits seed
  apply L.header_local _ (v.wide_signed_words_local h width stock M π o) es bits seed
  intro m e he x inside
  have first : (A).first<2^w:=(Nat.le_add_right ..).trans_lt room
  apply v.wide_signed_words_above h width stock M π o m x first
  cases e with
  | attempt a=>
    have hx : (A).base v.mesh (.attempt a)≤x:=inside.1
    exact (Nat.le_add_right ..).trans hx
  | feed b=>
    have zero : x<0:=inside.2
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
