import OAI.Hierarchy.DescentMatchLaneNumbers
import OAI.Hierarchy.DescentPackedMatchExecution
import OAI.Hierarchy.DescentPackedMatchPolynomial
import OAI.Hierarchy.DescentPackedPayloadBudget

namespace OAI
/-! # One common lane width and a word-bit price for the entire matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather
open DescentSIMDLookup ProtocolRAM
open scoped Classical
noncomputable section
variable {r D p K : ℕ}


/-- All variable-width dictionaries are fixed functions. Their key widths depend
only on the public local dimensions, including the shift ROM for each input field. -/
theorem key_prices (s : Shape) (d r D p unit payload : ℕ) (large : matchUnit s d r D p≤unit) :
    let m:=lanes payload unit
    let a:=s.outputBits*m
    let b:=s.digit*(m*s.pairs)
    let t:=d*fields r D p
    2^(t*m)≤2^(payload/2) ∧ 2^((t+d)*m)≤2^(payload/2) ∧ 2^(s.inputBits*m)≤2^(payload/2) ∧
      ProfileTable.footprint a b≤5*2^(payload/2) := by
  let m:=lanes payload unit
  have pay (x : ℕ) (h : x≤unit) : x*m≤payload/2 :=
    ((Nat.mul_le_mul_left m h).trans (lanes_fit payload unit)).trans_eq (by rfl) |> fun h'=>by simpa only [Nat.mul_comm x m] using h'
  have long : d*fields r D p+d≤unit := (le_max_left _ _).trans large
  have output : ProfileTable.envelope s≤unit := (le_max_right _ _).trans large
  have full : ProfileTable.bits (s.outputBits*m) (s.digit*(m*s.pairs))≤payload/2 := by
    have scaled : (s.outputBits + 3*(s.digit*s.pairs))*m≤payload/2 := pay _ (by
      have h:=le_max_right s.inputBits s.outputBits
      unfold ProfileTable.envelope at output
      change max s.inputBits s.outputBits+3*(s.digit*s.pairs)≤unit at output
      omega)
    unfold ProfileTable.bits
    nlinarith only [scaled]
  have source : s.inputBits≤unit := (le_max_left s.inputBits s.outputBits).trans
    ((Nat.le_add_right s.bits (3*(s.digit*s.pairs))).trans output)
  have power {x : ℕ} (small : x≤payload/2):=Nat.pow_le_pow_right (by decide : 0<2) small
  have a:=power (show s.outputBits*m≤payload/2 by unfold ProfileTable.bits at full;omega)
  have b:=power (show s.digit*(m*s.pairs)≤payload/2 by unfold ProfileTable.bits at full;omega)
  have all_:=power full
  have footprint : ProfileTable.footprint (s.outputBits*m) (s.digit*(m*s.pairs))≤5*2^(payload/2) := by
    unfold ProfileTable.footprint
    omega
  exact ⟨power (pay _ (by omega)),power (pay _ long),power (pay _ source),footprint⟩

/-- Scan ticks include assembly of each original field, the matched topology
lookup, the exclusive prefix and the two adjacent profile reads. -/
theorem stage_fee (_s : Shape) (_d H G payload W ratio unit : ℕ)
    (tables : Fin (fields r D p)→DescentPackedZip.Tables) (dict : Fin K→Bank) (mask : Bank)
    (wins : Fin r→Bank) (marked : Fin r→Fin p→Bank) (P : DescentPackedColony.Ports D) (base : ℕ)
    (positive : 0<unit) (wide : 2*unit≤payload) (hardware : W≤ratio*payload) :
    let m:=lanes payload unit
    let n:=(K*H)*chunks G m
    let ps:=passes tables (expr wins marked P H) dict mask base H G m
    (clock ps+((4+44*n)+ProfileTable.clock n))*W ≤
      ratio*((432+4*K)*payload+K*(668+112*fields r D p)*(H*payload+4*H*G*unit)) := by
  let m:=lanes payload unit
  let n:=(K*H)*chunks G m
  let ps:=passes tables (expr wins marked P H) dict mask base H G m
  have gather:=clock_le tables (expr wins marked P H) dict mask base H G m 45 (terrain_work wins marked P H)
  have cursor:=PackedProfileCursor.ticks_bound n
  have prof : ProfileTable.clock n≤424+592*n := by unfold ProfileTable.clock;omega
  have whole : clock ps+((4+44*n)+ProfileTable.clock n)≤(432+4*K)+K*(668+112*fields r D p)*(H*chunks G m) := by
    change clock ps≤_ at gather
    dsimp only [n] at prof ⊢
    nlinarith only [gather,prof]
  have vol:=volume H G payload unit positive wide
  change H*chunks G m*payload≤_ at vol
  have v := Nat.mul_le_mul_left (K*(668+112*fields r D p)) vol
  have price : (clock ps+((4+44*n)+ProfileTable.clock n))*payload≤
      (432+4*K)*payload+K*(668+112*fields r D p)*(H*payload+4*H*G*unit) := by
    nlinarith only [Nat.mul_le_mul_right payload whole,v]
  exact DescentPackedPayloadBudget.clock hardware price

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather

end OAI
