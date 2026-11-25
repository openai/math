import OAI.Hierarchy.ProbeFixedWideSpillDates
import OAI.Hierarchy.ProbeFixedWideSpillMiddleBounds
import OAI.Hierarchy.ProbeFixedWideDatedSheetFits

namespace OAI
/-! # The three dated spill-role sheets fit above their original rank tapes -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard HistoryRoles RoleProgram
open scoped Classical

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)

local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "T" => (events v.mesh).length
local notation "pages" => v.wideSpillRanks h width
local notation "finish" => v.wideSpillRankEnd h width
local notation "slices" => v.widePaidSlices h width

/-- A completed dated rank tape contains every per-edge group counter, including
the unused padding of its last dyadic bank. -/
theorem wide_spill_rank_page_end (bits first : ℕ) (j : Fin T) :
    (v.wideSpillPage h width bits first j.val).offsetsStart ≤ finish bits first := by
  apply ((pages bits first).page_end j.val).trans
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _

/-- Each dated role query reads either the original overflow bank or the ranked
sum for the corresponding original paid edge. Date zero has a literal zero
width, including for the preclip sheet. -/
theorem wide_spill_amount_fits (ell unitCost bits first : ℕ) (f : Fin 3) (date : Fin (T+1))
    (archive : (v.wideReserveLayout h width (slices bits)).scratch≤first)
    (word : finish bits first<2^w) :
    (((v.wideSpillDates h width ell unitCost bits first).roles f).amount date).Fits w (finish bits first) := by
  let dest := finish bits first
  have before : first≤dest := by
    change first≤first+(pages bits first).zero.size+T*(pages bits first).stride
    omega
  refine Fin.cases ?_ (fun j => ?_) date
  · exact trivial
  · let a := v.wideSpillPage h width bits first j.val
    have ranked : a.offsetsStart≤dest := v.wide_spill_rank_page_end h width bits first j
    have heap := v.wide_prefix_low_heap h width bits
    have overflow : a.overflow.base+a.overflow.size≤dest :=
      (v.wide_spill_page_floor h width bits first j (by omega)).trans before
    let g := v.wideRoleInventory h width bits (j.val+1)
    change (if f=0 then v.wideSpillMiddle h width bits j.val a else
      WideCPU.spillOnly g a (decide (f=2))).Fits w dest
    by_cases mid : f=0
    · rw [ite_eq_left mid]
      exact v.wide_spill_middle_fits h width bits j.val j.isLt a dest
        (archive.trans before) word ranked overflow
    · rw [ite_eq_right mid]
      have operands := (v.wide_role_fits h width bits (j.val+1) j.isLt dest (archive.trans before) word).1
      have kind : g.kind.Fits w dest := operands.1
      have index : g.index.Fits w dest := operands.2.2.1
      have bank (b : Bank) (last : b.base+b.size≤dest) : b.Fits w dest :=
        ⟨Nat.two_pow_pos _,by change dest<2^w at word;omega,last⟩
      cases (decide (f=2)) with
      | false => exact ⟨kind,trivial,⟨bank _ overflow,index⟩,trivial⟩
      | true => exact ⟨kind,trivial,⟨bank _ (a.load_end.trans ranked),index⟩,trivial⟩

/-- The original sockets, party ordinals, public site stride and all three
incremental role quantities fit in the common output address space. -/
theorem wide_spill_role_fits (ell unitCost bits first rom : ℕ) (f : Fin 3) (j : Fin (T+1))
    (prior : v.wideFundedSize h width v.maxBits≤finish bits first)
    (archive : (v.wideReserveLayout h width (slices bits)).scratch≤first)
    (word : finish bits first<2^w)
    (stride : rom+ProtocolRAMPurchaseSampler.span (siteLast h D k+1)≤finish bits first) :
    let a:=(v.wideSpillDates h width ell unitCost bits first).roles f
    DatedRoleSheets.Fits a.physical a.chart a.sockets (a.siteStride rom) (a.amount j) a.ordinal w (finish bits first) :=
  v.wide_dated_role_fits h width ell unitCost rom (finish bits first) _ prior word
    (v.wide_spill_amount_fits h width ell unitCost bits first f j archive word) stride


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
