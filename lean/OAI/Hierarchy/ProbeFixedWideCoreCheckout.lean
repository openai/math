import OAI.Hierarchy.ProbeFixedWideSignedCore
import OAI.Hierarchy.ProbeFixedWideRowBoards

namespace OAI
/-! # The real core rows and their word bounds on the pre-settlement signed checkout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open CoreRoute StripChart CatalystArchive ReportSockets BoughtSockets
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "P" => v.widePlacement

theorem wide_core_checkout (h width size : ℕ) (extent : (v.privateArena (P h width) h width).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h (2^v.W) k) (raw : Boot.Tape h (2^v.W))
    (word : (v.privateArena (P h width) h width).endAddress v.mesh < 2^wordBits h (2^v.W) Native.copies)
    (live : Calendar.mounted (v.wideSignedChart h width stock) (events v.mesh)
      (v.wideSignedMidAt h width size stock M π o raw)) :
    CoreCatalogue.Rows (P h width).catalogue.core (v.wideOrder h width)
      (WideMemory.dir h v.W k v.wideJobs) π M (v.wideSignedCheckoutAt h width size stock M π o raw) := by
  obtain ⟨_,_,boot,_,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock M π o raw word
  let G:=v.privateArena (P h width) h width
  have bound:=(v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first (P h width) h width)
  have first : G.first≤G.endAddress v.mesh:=Nat.le_add_right ..
  have seen:=boot.frame (bound.trans_lt (first.trans_lt word))
    (fun x hx=>v.wide_signed_checkout_below h width stock M π o raw size x (hx.trans_le bound) live)
  exact seen.board.rows

/-- The physical site ordinals, sentinel and core metrics all fit the same word
width at every sufficiently large height, uniformly over the pricing width. -/
theorem wide_alignment_room :
    ∀ᶠ h : ℕ in Filter.atTop,∀width : ℕ,
      siteLast h (2^v.W) k+1≤2^wordBits h (2^v.W) Native.copies ∧
      (P h width).catalogue.idBase+(P h width).catalogue.rows<2^wordBits h (2^v.W) Native.copies ∧
      ∀j,coreCode v.sampler v.radius ((v.wideOrder h width) j)<2^wordBits h (2^v.W) Native.copies := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.wide_row_room,Filter.eventually_ge_atTop (siteFactor (2^v.W) k+1)] with h found big
  intro width
  have enough : siteFactor (2^v.W) k+1≤2^h:=big.trans (Nat.lt_two_pow_self (n:=h)).le
  have tall:=append_room (d:=2^v.W) (copies:=Native.copies) enough
  have shape:=site_count h (2^v.W) k Nat.one_le_two_pow
  refine ⟨shape.trans ((Nat.le_add_left ..).trans tall.le),?_,?_⟩
  · change 0+(P h width).catalogue.rows<_
    simpa only [Nat.zero_add] using (found width).1
  · intro j
    exact (Public.coreCode_le _ _ _).trans_lt (found width).2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
