import OAI.Hierarchy.ProbeFixedAttemptStates
import OAI.Hierarchy.ProbeAccountQuotes
import OAI.Hierarchy.ProbeLegalMenuGrid
import OAI.Hierarchy.ProbeFixedPacketRates

namespace OAI
/-! # The coordinates used by the quantized quote on both real repair branches -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ) (bills : Event → WordRows) (a : Attempt)
local notation "n" => Stages z (2^v.W)
local notation "C" => Commodity (Fin (2^z)) n k
local notation "acct" => v.nativeAccount P z width bills
local notation "bank" => (acct).bank.coordinates (v.nativeSlots P z width a)
local notation "phase" => publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W)

/-- The actual nonlinear stock maximizer reads the precise slot addressed by
each key digit in both native mode-two boards. -/
theorem maximizer_word {w} (mem : Memory w) (time : ℝ) (i : C) :
    maximizer (bank).a (bank).M time (bank).coefficient (bank).box ((bank).units width ((acct).read a mem))
      (v.nativeSlots P z width a i) =
    (phase time width v.precision).quote (i.elim (fun _ => 0) (fun _ => 1)) (mem ((acct).stockAt a i)).val := by
  let E := v.nativeSlots P z width a
  change offer v.a (bonus (probeBonus v.W) (E.symm (E i))) v.radius time
    (((mem ((acct).stockAt a (E.symm (E i)))).val:ℝ)/width)
    (routeCap n v.radius (PurchaseInventory.lane (E.symm (E i)))) = _
  rw [E.symm_apply_apply,routeCap_named]
  have count : n=publicStages v.W := fixed_stage_count z v.W
  rcases i with p | ⟨⟨p,t⟩,j⟩ <;>
    simp [PhasePrice.quote,publicPhase,bonus,probeBonus,CoreBoard.commodityLength,count]

/-- No asserted approximation of the stock prices enters this calculation:
each digit is the real, rounded public price word for the old inventory. -/
theorem role_digit {w : ℕ} (mem : Memory w) (time : ℝ) (timepos : 0<time)
    (i : C) (value : ℕ) (read : value =
      (phase time width v.precision).word (i.elim (fun _ => 0) (fun _ => 1)) (mem ((acct).stockAt a i)).val) :
    let price := maximizer (bank).a (bank).M time (bank).coefficient (bank).box
      ((bank).units width ((acct).read a mem)) (v.nativeSlots P z width a i)
    (value:ℝ)/v.precision ≤ price ∧ price ≤ (value:ℝ)/v.precision+1/(v.precision:ℝ) := by
  intro price
  have hit := v.maximizer_word P z width bills a mem time i
  have r := rounded_public (publicStages v.W) width v.precision (i.elim (fun _ => 0) (fun _ => 1))
    (mem ((acct).stockAt a i)).val (a:=(v.a:ℝ)) (M:=(v.radius:ℝ)) (W:=(v.W:ℝ)) (T:=probeHeat v.W)
    (by exact_mod_cast v.quadratic_pos) (Nat.cast_nonneg _) timepos v.clock.precision_pos
  change (value:ℝ)/v.precision ≤ _ ∧ _ ≤ _
  rw [read]
  exact ⟨r.2.1.trans_eq hit.symm,hit.le.trans r.2.2.le⟩

/-- Every index in the exact payload catalogue meets the arity, copied gain
and quote-error obligations for `StripInput.quote_at_live`, uniformly in the
height and in the actual failed row. -/
theorem payload_quote_bounds {w : ℕ} (large : v.widthFloor≤width) (wide : v.menu.alphabet < 2^w) :
    ∀ i : v.payloadPackets.index,
      (v.payloadPackets.packet i).terms ≤ v.menu.alphabet ∧ (v.payloadPackets.packet i).terms < 2^w ∧
      (Fintype.card (PayloadRole (publicStages v.W) k):ℝ)*v.menu.maximum*(1/(v.precision:ℝ)) ≤
        (v.payloadPackets.packet i).width*v.menu.margin/2 ∧
      copied (v.copyScale*commonWidth v.menu.width) (v.payloadPackets.packet i).width width ≤
        v.menu.copiesAt v.copyScale width := by
  intro i
  have cap : (v.payloadPackets.packet i).terms ≤ v.menu.alphabet := v.menu.alphabet_ge (.inl i)
  exact ⟨cap,cap.trans_lt wide,v.payload_precision i,((v.copied_widths width large).2 (.inl i)).2.1⟩

theorem purchased_quote_bounds {w : ℕ} (large : v.widthFloor≤width) (wide : v.menu.alphabet < 2^w) :
    ∀ i : v.boughtPackets.index,
      (v.boughtPackets.packet i).terms ≤ v.menu.alphabet ∧ (v.boughtPackets.packet i).terms < 2^w ∧
      (Fintype.card (PurchasedRole v.depth k):ℝ)*v.menu.maximum*(1/(v.precision:ℝ)) ≤
        (v.boughtPackets.packet i).width*v.menu.margin/2 ∧
      copied (v.copyScale*commonWidth v.menu.width) (v.boughtPackets.packet i).width width ≤
        v.menu.copiesAt v.copyScale width := by
  intro i
  have cap : (v.boughtPackets.packet i).terms ≤ v.menu.alphabet := v.menu.alphabet_ge (.inr i)
  exact ⟨cap,cap.trans_lt wide,v.bought_precision i,((v.copied_widths width large).2 (.inr i)).2.1⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
