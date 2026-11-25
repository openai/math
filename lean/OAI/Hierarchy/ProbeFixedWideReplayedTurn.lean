import OAI.Hierarchy.ProbeFixedWideSliceBound
import OAI.Hierarchy.ProbeFixedWideSignedFits
import OAI.Hierarchy.ProbeFixedWidePrefixRoom
import OAI.Hierarchy.ProbeFixedWidePrefixProgram

namespace OAI
/-! # The turn output after every replayed edge, owner, and temporary row -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "D" => 2^v.W
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "rows" => (v.widePlacement h width).catalogue.rows
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh
  (ownerLedger (v.nativeBoards (v.widePlacement h width) h width) v.mesh
    (v.widePlacement h width).catalogue (v.widePlacement h width).routes F
    (v.privateArena (v.widePlacement h width) h width)))
local notation "last" => (events v.mesh).length

variable (slices : List PaidWidths.Slice)
local notation "lw" => v.wideWidthLayout h width slices
local notation "lr" => v.wideReserveLayout h width slices

open Filter

/-- Start all eleven turn columns after the public reserve replay and its last
two temporary rows per input record. -/
def wideReplayedTurnBase (ss : List PaidWidths.Slice) :=
  (v.wideReserveLayout h width ss).scratch+2*max (wideSliceBound ss) cnt

def wideReplayedTurnEnd (ss : List PaidWidths.Slice) :=
  v.wideReplayedTurnBase h width ss+7*Fintype.card (Old h v.W k rows)+4*rows

theorem wide_replayed_start :
    v.wideRoleSize h width (v.fixedTerminalStock (v.widePlacement h width) h width) slices≤v.wideReplayedTurnBase h width slices ∧
      ((lw).bank last).base+((lw).bank last).size≤v.wideReplayedTurnBase h width slices := by
  let edgePage:=2^(lw).bits+1
  have split : (lr).scratch=(lw).archive+(last+1)*edgePage+(2*last+2)*(2^((num).log2+1)+1):=rfl
  have first : (lw).archive≤(lr).scratch := by omega
  have tail : ((lw).bank last).base+((lw).bank last).size≤(lr).scratch := by
    change (lw).archive+last*edgePage+2^(lw).bits≤(lr).scratch
    rw [Nat.add_mul,one_mul] at split
    dsimp [edgePage] at split ⊢
    omega
  exact ⟨first.trans (Nat.le_add_right ..),tail.trans (Nat.le_add_right ..)⟩

/-- Work on the actual sparse paid rows and a fixed linear charge cover the last
address of the full replay and turn, including all dyadic padding. -/
theorem wide_replayed_turn_charge :
    ∃ C : ℕ,∀ h width (ss : List PaidWidths.Slice),v.keepLimit*width+1≤2^h →
      let P:=v.widePlacement h width
      let stock:=v.fixedTerminalStock P h width
      let bank:=(TerminalLayout.settlement (v.wideSignedPage h width stock) stock).width
      v.wideReplayedTurnEnd h width ss≤C*2^h+4*PaidWidths.clock bank P.catalogue.rows ss := by
  obtain ⟨C,cap⟩:=v.wide_turn_end_charge
  let dates:=(events v.mesh).length
  let edges:=v.rowFactor
  let axes:=resourceFactor D k
  let entries:=stripRecordFactor v.mesh D k v.sampler.degree v.depth
  refine ⟨C+(dates+1)*(2*edges+3)+(2*dates+2)*(2*axes+3)+2*entries,?_⟩
  intro h width ss affordable P stock bank
  let n:=(P.catalogue).rows
  let m:=Fintype.card (Columns h D)*k
  let A:=v.privateArena P h width
  let s:=v.nativeBoards P h width
  let count:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh P.catalogue P.routes F A))
  let ram:=v.wideRoleSize h width stock ss
  let cost:=PaidWidths.clock bank n ss
  let rep:=v.wideReserveLayout h width ss
  let remain:=2*max (wideSliceBound ss) count
  have red : rep.scratch≤ram+(dates+1)*(2*n+3)+(2*dates+2)*(2*m+3):=PrefixWidths.Layout.dense_extent n m ram dates
  have original:=cap h width stock ss affordable (v.fixedTerminalStock_end P h width)
  have rowCount : n≤edges*2^h:=v.wideCatalogueRows h width
  have accountCount : m≤axes*2^h:=physical_resources h D k (Nat.two_pow_pos _)
  have recordCount : count≤entries*2^h:=declared_records s v.mesh P.catalogue P.routes F A
  have padding (j a : ℕ) (small : j≤a*2^h) : 2*j+3≤(2*a+3)*2^h := by
    simpa only [Nat.add_mul,Nat.mul_assoc,Nat.mul_one] using
      Nat.add_le_add (Nat.mul_le_mul_left 2 small) (Nat.mul_le_mul_left 3 (Nat.two_pow_pos h))
  have edgesBound:=Nat.mul_le_mul_left (dates+1) (padding n edges rowCount)
  have axesBound:=Nat.mul_le_mul_left (2*dates+2) (padding m axes accountCount)
  have paid : 2*wideSliceBound ss ≤ cost :=
    (Nat.mul_le_mul_left 2 (wideSliceBound_le_sum ss)).trans (TerminalLayout.scratch_le_paid_clock bank n ss)
  have temporary : remain≤cost+2*(entries*2^h):=by
    dsimp only [remain]
    rcases le_total (wideSliceBound ss) count with b|b
    · rw [max_eq_right b]
      have bound:=Nat.mul_le_mul_left 2 recordCount
      omega
    · rw [max_eq_left b]
      omega
  have turn :
      v.wideReplayedTurnEnd h width ss≤v.wideTurnEnd h width stock ss+(dates+1)*(2*n+3)+
        (2*dates+2)*(2*m+3)+remain := by
    change rep.scratch+remain+7*Fintype.card (Old h v.W k n)+4*n≤
      ram+7*Fintype.card (Old h v.W k n)+4*n+(dates+1)*(2*n+3)+(2*dates+2)*(2*m+3)+remain
    omega
  calc
    _≤_ := turn
    _≤(C*2^h+3*cost)+(dates+1)*((2*edges+3)*2^h)+
        (2*dates+2)*((2*axes+3)*2^h)+(cost+2*(entries*2^h)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add original edgesBound) axesBound) temporary
    _=_ := by ring

theorem cofinal_replayed_turn_room {κ A : ℝ} (B t : ℝ) (ht : 0≤t) :
    ∃ C : ℝ,∀ᶠ x : Tagged.WideParent κ A in Tagged.WideParent.large κ A,
      ∀ ss : List PaidWidths.Slice,
      let P:=v.widePlacement x.h x.w
      let stock:=v.fixedTerminalStock P x.h x.w
      let bank:=(TerminalLayout.settlement (v.wideSignedPage x.h x.w stock) stock).width
      let cost:=PaidWidths.clock bank P.catalogue.rows ss
      (cost:ℝ)≤(2:ℝ)^x.h*(B*(2*(x.h:ℝ))^t) →
      let finish:=v.wideReplayedTurnEnd x.h x.w ss
      (finish:ℝ)≤(2:ℝ)^x.h*(C*(2*(x.h:ℝ))^t) ∧ finish<2^Native.wordBits x.h D Native.copies := by
  obtain ⟨N,invoice⟩:=v.wide_replayed_turn_charge
  let C:ℝ:=N+4*B
  refine ⟨C,?_⟩
  have tall : Tendsto (Tagged.WideParent.h (κ:=κ) (A:=A)) (Tagged.WideParent.large κ A) atTop := tendsto_comap
  filter_upwards [Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit,
    tall.eventually (eventually_ge_atTop 1),tall.eventually (Tagged.eventually_word_room C t ht)] with x budget age word
  intro ss P stock bank cost paid finish
  have charged : (finish:ℝ)≤(N:ℝ)*(2:ℝ)^x.h+4*(cost:ℝ) := by exact_mod_cast invoice x.h x.w ss budget
  have hPos : (1:ℝ)≤x.h := by exact_mod_cast age
  have power : (1:ℝ)≤(2*(x.h:ℝ))^t:=Real.one_le_rpow (by linarith) ht
  have extra:=mul_le_mul_of_nonneg_left power (show (0:ℝ)≤(N:ℝ)*(2:ℝ)^x.h by positivity)
  have full : (finish:ℝ)≤(2:ℝ)^x.h*(C*(2*(x.h:ℝ))^t) := calc
    _≤(N*(2:ℝ)^x.h)*(2*(x.h:ℝ))^t+4*((2:ℝ)^x.h*(B*(2*(x.h:ℝ))^t)) := by linarith
    _=_ := by dsimp [C];ring
  refine ⟨full,(word finish full).trans_le (Nat.pow_le_pow_right (by decide) ?_)⟩
  rw [Native.wordBits_linear]
  omega

abbrev wide_replayed_turn_ready (room : v.wideReplayedTurnEnd h width slices<2^w) :=
  let first:=v.wide_replayed_start h width slices
  v.wide_signed_turn_ready_at h width (v.fixedTerminalStock (v.widePlacement h width) h width) ((lw).bank last) slices (v.wideReplayedTurnBase h width slices)
    (v.fixedTerminalStock_end (v.widePlacement h width) h width) first.1 first.2 room

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
