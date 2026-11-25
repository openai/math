import OAI.Hierarchy.ProbeFixedWideSignedOutput
import OAI.Hierarchy.TaggedWideTerminalTariff
import OAI.Hierarchy.TaggedWireRoleRoomGrowth

namespace OAI
/-! # Charging the entire finite signed input to the native paid-width program -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open CatalystArchive StripChart CatalogueRows CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram Filter
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement
local notation "calendarEnd" => (fun h width=>(v.privateArena (P h width) h width).endAddress v.mesh)

theorem wide_role_size_charge :
    ∃ C : ℕ,∀ h width (stock : Bank) (ss : List PaidWidths.Slice),
      v.keepLimit*width+1≤2^h → stock.base+stock.size≤calendarEnd h width →
      let bank:=(TerminalLayout.settlement (v.wideSignedPage h width stock) stock).width
      v.wideRoleSize h width stock ss≤C*2^h+3*PaidWidths.clock bank (P h width).catalogue.rows ss := by
  let pad:=2*copies k v.wideJobs
  have ok : 2*copies k v.wideJobs≤2^pad:=Nat.lt_two_pow_self.le
  obtain ⟨C,room⟩:=RoleRoom.appended v.sampler v.W k v.wideJobs pad v.depth ok
  obtain ⟨a,arena⟩:=v.wideArena
  refine ⟨3*(a+v.widePageFactor)+C,?_⟩
  intro h width stock ss fit stored bank
  let rows:=(P h width).catalogue.rows
  let cost:=PaidWidths.clock bank rows ss
  let start:=v.wideRoleStart h width stock ss
  have endAt : calendarEnd h width≤a*2^h:=arena h width fit
  have paid : TerminalLayout.extent (v.wideSignedPage h width stock) ss≤v.widePageFactor*2^h+cost :=
    v.priced_extent h width stock bank rows ss fit stored
  have high : start≤a*2^h+v.widePageFactor*2^h+cost := by
    apply max_le
    · exact endAt.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · exact paid.trans (Nat.add_le_add_right (Nat.le_add_left _ _) _)
  have installed : v.wideRoleSize h width stock ss≤3*start+C*2^h :=
    room h (WideMemory.R v.sampler h v.W k) (v.wideOrder h width) start
  calc
    _≤3*(a*2^h+v.widePageFactor*2^h+cost)+C*2^h := installed.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ high) _)
    _=(3*(a+v.widePageFactor)+C)*2^h+3*cost := by ring

/-- Address immediately beyond the original four role columns per row, the four
new role columns per catalogue edge, and the three original stock columns. -/
def wideTurnEnd (h width : ℕ) (stock : Bank) (ss : List PaidWidths.Slice) :=
  let rows:=(P h width).catalogue.rows
  v.wideRoleSize h width stock ss+7*Fintype.card (Old h v.W k rows)+4*rows

theorem wide_turn_end_charge :
    ∃ C : ℕ,∀ h width (stock : Bank) (ss : List PaidWidths.Slice),
      v.keepLimit*width+1≤2^h → stock.base+stock.size≤calendarEnd h width →
      let bank:=(TerminalLayout.settlement (v.wideSignedPage h width stock) stock).width
      v.wideTurnEnd h width stock ss≤C*2^h+3*PaidWidths.clock bank (P h width).catalogue.rows ss := by
  obtain ⟨C,cap⟩:=v.wide_role_size_charge
  let old:=RoleRoom.oldFactor D k v.rowFactor
  refine ⟨C+7*old+4*v.rowFactor,?_⟩
  intro h width stock ss fit stored bank
  let cost:=PaidWidths.clock bank (P h width).catalogue.rows ss
  have raw:=v.wideCatalogueRows h width
  have rows:=RoleRoom.old_bound (W:=v.W) (k:=k) raw
  have endAt:=cap h width stock ss fit stored
  unfold wideTurnEnd
  calc
    _≤(C*2^h+3*cost)+7*(old*2^h)+4*(v.rowFactor*2^h) :=
      Nat.add_le_add (Nat.add_le_add endAt (Nat.mul_le_mul_left _ rows)) (Nat.mul_le_mul_left _ raw)
    _=_ := by ring

/-- All actual role and site words lie in a finite native input. The only variable
charge is that of this run's issued paid slices. The constant is selected before
both the parent and its width, and is common to either radius and permutation. -/
theorem cofinal_signed_turn_room {κ A : ℝ} (B t : ℝ) (ht : 0≤t) :
    ∃ C : ℝ,∀ᶠ x:Tagged.WideParent κ A in Tagged.WideParent.large κ A,
      ∀ (stock : Bank) (ss : List PaidWidths.Slice),
      stock.base+stock.size≤calendarEnd x.h x.w →
      let bank:=(TerminalLayout.settlement (v.wideSignedPage x.h x.w stock) stock).width
      let cost:=PaidWidths.clock bank (P x.h x.w).catalogue.rows ss
      (cost:ℝ)≤(2:ℝ)^x.h*(B*(2*(x.h:ℝ))^t) →
      let size:=v.wideTurnEnd x.h x.w stock ss
      (size:ℝ)≤(2:ℝ)^x.h*(C*(2*(x.h:ℝ))^t) ∧ size<2^(Native.wordBits x.h D Native.copies) := by
  obtain ⟨N,charge⟩:=v.wide_turn_end_charge
  let C:ℝ:=N+3*B
  refine ⟨C,?_⟩
  have tall : Tendsto (Tagged.WideParent.h (κ:=κ) (A:=A)) (Tagged.WideParent.large κ A) atTop := tendsto_comap
  filter_upwards [Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit,
    tall.eventually (eventually_ge_atTop 1),tall.eventually (Tagged.eventually_word_room C t ht)] with x fit large room
  intro stock ss stored bank cost paid size
  have invoice : (size:ℝ)≤(N:ℝ)*(2:ℝ)^x.h+3*(cost:ℝ) := by exact_mod_cast charge x.h x.w stock ss fit stored
  have pos : (1:ℝ)≤x.h := by exact_mod_cast large
  have pow : (1:ℝ)≤(2*(x.h:ℝ))^t := Real.one_le_rpow (by linarith) ht
  have first:=mul_le_mul_of_nonneg_left pow (show (0:ℝ)≤(N:ℝ)*(2:ℝ)^x.h by positivity)
  have total : (size:ℝ)≤(2:ℝ)^x.h*(C*(2*(x.h:ℝ))^t) := calc
    _≤((N:ℝ)*(2:ℝ)^x.h)*(2*(x.h:ℝ))^t+3*((2:ℝ)^x.h*(B*(2*(x.h:ℝ))^t)) := by linarith
    _=_ := by dsimp [C];ring
  refine ⟨total,(room size total).trans_le (Nat.pow_le_pow_right (by decide) ?_)⟩
  rw [Native.wordBits_linear]
  omega

theorem cofinal_signed_word_room {κ A : ℝ} (B t : ℝ) (ht : 0≤t) :
    ∃ C : ℝ,∀ᶠ x:Tagged.WideParent κ A in Tagged.WideParent.large κ A,
      ∀ (stock : Bank) (ss : List PaidWidths.Slice),
      stock.base+stock.size≤calendarEnd x.h x.w →
      let bank:=(TerminalLayout.settlement (v.wideSignedPage x.h x.w stock) stock).width
      let cost:=PaidWidths.clock bank (P x.h x.w).catalogue.rows ss
      (cost:ℝ)≤(2:ℝ)^x.h*(B*(2*(x.h:ℝ))^t) →
      let size:=v.wideRoleSize x.h x.w stock ss
      (size:ℝ)≤(2:ℝ)^x.h*(C*(2*(x.h:ℝ))^t) ∧ size<2^(Native.wordBits x.h D Native.copies) := by
  obtain ⟨C,ready⟩:=v.cofinal_signed_turn_room (κ:=κ) (A:=A) B t ht
  refine ⟨C,?_⟩
  filter_upwards [ready] with x run
  intro stock ss stored bank cost paid size
  have high:=run stock ss stored paid
  have bound : size≤v.wideTurnEnd x.h x.w stock ss:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ⟨(show (size:ℝ)≤(v.wideTurnEnd x.h x.w stock ss:ℝ) by exact_mod_cast bound).trans high.1,
    bound.trans_lt high.2⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
