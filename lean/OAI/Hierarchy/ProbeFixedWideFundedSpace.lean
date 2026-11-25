import OAI.Hierarchy.ProbeFixedWidePaidClock
import OAI.Hierarchy.ProbeFixedWideSignedSize
import OAI.Hierarchy.TaggedWideReplayLengths
import OAI.Hierarchy.ProbeFixedWideFundedSize
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Space for all genuine signed paid rows and their dated prefix reports -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open CatalystArchive StripChart ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram Filter
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement
local notation "stock" => (fun h width=>v.fixedTerminalStock (P h width) h width)

theorem wide_funded_size_linear : ∃ K : ℕ,∀h width bits, v.keepLimit*width+1≤2^h →
    v.wideFundedSize h width bits≤K*2^h := by
  let pad:=2*copies k v.wideJobs
  have ok : 2*copies k v.wideJobs≤2^pad:=Nat.lt_two_pow_self.le
  obtain ⟨C,room⟩:=RoleRoom.appended v.sampler v.W k v.wideJobs pad v.depth ok
  obtain ⟨A,arena⟩:=v.wideArena
  let M:=v.widePageFactor+2*(v.wideSliceLength*v.wideSliceFactor)
  refine ⟨3*(A+M)+C,?_⟩
  intro h width bits budget
  let ss:=v.widePaidSlices h width bits
  let page:=v.wideSignedPage h width (stock h width)
  let start:=v.wideRoleStart h width (stock h width) ss
  have pages:=v.page_charge h width (stock h width) budget (v.fixedTerminalStock_end (P h width) h width)
  have shape:=(v.wide_paid_shape h width bits budget).2.2
  have source : TerminalLayout.extent page ss≤M*2^h := by
    calc
      _≤28*2^page+2*(ss.map PaidWidths.Slice.count).sum:=TerminalLayout.extent_le ..
      _≤v.widePageFactor*2^h+2*((v.wideSliceLength*v.wideSliceFactor)*2^h) :=
        Nat.add_le_add pages (Nat.mul_le_mul_left 2 shape)
      _=_:=by dsimp [M];ring
  have first : start≤(A+M)*2^h := by
    change max _ _≤_
    rw [Nat.add_mul]
    exact max_le ((arena h width budget).trans (Nat.le_add_right ..)) (source.trans (Nat.le_add_left ..))
  have surrounding : v.wideFundedSize h width bits≤3*start+C*2^h :=
    room h (WideMemory.R v.sampler h v.W k) (v.wideOrder h width) start
  exact surrounding.trans ((Nat.add_le_add_right (Nat.mul_le_mul_left 3 first) _).trans_eq (by ring))

theorem cofinal_funded_scan {κ X : ℝ} :
    ∃ K : ℕ,∀ᶠ x : Tagged.WideParent κ X in Tagged.WideParent.large κ X,∀bits : ℕ,
      let ss:=v.widePaidSlices x.h x.w bits
      let maxRows:=2^v.wideSignedPage x.h x.w (stock x.h x.w)
      (∀t∈ss,t.count≤ maxRows) ∧ v.wideScanEnd x.h x.w ss maxRows≤K*2^x.h ∧
      v.wideScanEnd x.h x.w ss maxRows<2^Native.wordBits x.h D Native.copies := by
  obtain ⟨K,size⟩:=v.wide_funded_size_linear
  obtain ⟨L,reports⟩:=v.cofinal_paid_scan (κ:=κ) (X:=X) K
  refine ⟨L,?_⟩
  filter_upwards [reports, Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=X) v.keepLimit] with x room fits
  intro bits
  exact room bits (size x.h x.w bits fits)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
