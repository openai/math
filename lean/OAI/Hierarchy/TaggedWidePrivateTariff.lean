import OAI.Hierarchy.TaggedWideSwitchTariff
import OAI.Hierarchy.TaggedWideCalendarPrivate
import OAI.Hierarchy.TaggedWideWorkspaceTariff

namespace OAI
/-! # Charging the complete original private equality networks at the funded capacity -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.Native ProbeStage.CoreBoard Tagged Filter Real
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "d" => 2^v.W

theorem original_private_bill {κ A : ℝ} (unitCost : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      let b:=(v.widePlacement x.h x.w).catalogue
      let order:=v.wideOrder x.h x.w
      let address:=wordBits x.h d copies
      let width:=v.widePrivateUnit unitCost*x.w
      let bits:=WideParent.columnBits width
      ∃ fits:siteLast x.h d k+1≤2^address,∀ {V:Type} [Fintype V]
        (ep : Fin b.rows→Bool→Fin address→V) (cut : Fin b.rows→Fin bits→V)
        (payload : Bool→b.Private order→Fin width→V),
        let net:=b.privateChecked (F:=F) order fits (WideParent.column_lt width).le ep cut payload
        ((net.cells+net.internal:ℕ):ℝ)≤C*((2:ℝ)^x.h*x.w*log (x.h:ℝ)) := by
  obtain ⟨C,cpos,fee⟩:=WideParent.checked_switch_bill (κ:=κ) (A:=A) v.rowFactor (v.widePrivateUnit unitCost) d copies
  refine ⟨C,cpos,?_⟩
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [fee,high.eventually (eventually_append_room d copies (siteFactor d k))] with x tariff mem
  let b:=(v.widePlacement x.h x.w).catalogue
  let order:=v.wideOrder x.h x.w
  let width:=v.widePrivateUnit unitCost*x.w
  let address:=wordBits x.h d copies
  have fits : siteLast x.h d k+1≤2^address:=by
    have bound := site_count x.h d k Nat.one_le_two_pow
    change heapEnd x.h d copies + siteFactor d k * 2^x.h < 2^wordBits x.h d copies at mem
    exact bound.trans ((Nat.le_add_left _ _).trans mem.le)
  refine ⟨fits,?_⟩
  intro V inst ep cut payload
  have prov:=b.privateChecked_cost (F:=F) order fits (WideParent.column_lt width).le ep cut payload
  have small:Fintype.card (b.Private order)≤b.rows := by
    simp
  have charge:=tariff b.rows (Fintype.card (b.Private order)) small (v.wideCatalogueRows x.h x.w)
  refine ((Nat.cast_le (α:=ℝ)).mpr prov).trans ?_
  simpa only [width, address, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.mul_assoc] using charge

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
