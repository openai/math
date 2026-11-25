import OAI.Hierarchy.ProbeFixedWidePartyCapacity
import OAI.Hierarchy.ProbeFixedWidePacketRates
import OAI.Hierarchy.TaggedWidePartyTariff
import OAI.Hierarchy.TaggedWireTurnCost

namespace OAI
/-! # Uniform prices of the actual outer and purchased signed party programs -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ThreeFlat Routing
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles Strip StripChart StripDirectory Probe Tagged
open WireTelescope WireTelescope.PassMatrix WireTelescope.PassMatrix.PartyPins
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "stat" => publicStages v.W
local notation "links" n => TreeLink n k
local notation "pl" s => PayloadStrip.edgeCount s
local notation "ch" => ChainStrip.edgeCount v.depth
local notation "D" => v.widePacketDegree

/-- The upper bound on the rounded lane address uses the native stage count,
real format histMass and both finite signed menus. -/
theorem signed_party_dimensions (unitCost : ℕ) :
    ∃K:ℕ,0<K ∧ ∀h w a,0<w →
      let f:=v.nativeFormats (v.widePlacement h w) h w a
      2^(v.partyLaneBits h w a unitCost)≤ K*w ∧ f.histMass≤ K*w := by
  let payloadFuel (s : ℕ) := (v.payloadPacketMenu s).signedFuel (links (pl s))
  let fuel:=max (payloadFuel stat)
    (v.purchasePacketMenu.signedFuel (links ch))
  let capacity:=D*v.wideHistoryUnit unitCost
  let rate:=2*(capacity+1)+fuel+1
  refine ⟨2*rate,by dsimp [rate];omega,?_⟩
  intro h w a hw f
  have cap : v.signedPartyFuel h a≤ fuel := by
    have fixed : payloadFuel (Stages h (2^v.W))=payloadFuel stat :=
      congrArg payloadFuel (fixed_stage_count h v.W)
    cases a with
    | outer phase trial => exact fixed.le.trans (Nat.le_max_left _ _)
    | inner phase trial layer tick => exact Nat.le_max_right _ _
  have paid : f.histMass≤ w:=by
    rw [(v.ordinary_dimensions (v.widePlacement h w) h w a).2]
    exact Nat.div_le_self ..
  let z:=capacity*w+1
  have digits : Nat.clog 2 z≤ Nat.log 2 z+1:=
    (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr (Nat.lt_pow_succ_log_self (by decide : 1<2) z).le
  have neighbor : v.wideNeighborCap w unitCost≤ 2*z:=by
    change 2^Nat.clog 2 z≤ _
    exact (Nat.pow_le_pow_right (by decide : 0<2) digits).trans (TurnShelf.dyadic_room z (by dsimp [z];omega)).2
  let top:=max (v.wideNeighborCap w unitCost) (f.histMass*v.signedPartyFuel h a)
  have board : top≤ rate*w:=by
    apply max_le
    · calc
        v.wideNeighborCap w unitCost ≤ 2*z := neighbor
        _ ≤ 2*((capacity+1)*w) := Nat.mul_le_mul_left 2 (by
          change capacity*w+1≤(capacity+1)*w
          rw [Nat.add_mul,Nat.one_mul]
          omega)
        _ ≤ rate*w := by
          rw [←Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (by dsimp only [rate];omega)
    · calc
        f.histMass*v.signedPartyFuel h a ≤ w*fuel := Nat.mul_le_mul paid cap
        _ = fuel*w := Nat.mul_comm _ _
        _ ≤ rate*w := Nat.mul_le_mul_right _ (by dsimp only [rate];omega)
  have topPos : 0<top:=(Nat.two_pow_pos (v.wideNeighborDigits w unitCost)).trans_le (Nat.le_max_left _ _)
  have slots : 2^(v.partyLaneBits h w a unitCost)≤ 2*top:=(TurnShelf.dyadic_room top topPos).2
  exact ⟨slots.trans ((Nat.mul_le_mul_left 2 board).trans_eq (Nat.mul_assoc ..).symm),
    paid.trans (Nat.le_mul_of_pos_left _ (by dsimp [rate];omega))⟩

private def payloadPrice (s cols keys limit : ℕ) : ℕ := by
  let names : TreeSite (PayloadStrip.edgeCount s) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount s) k)) := SiteNaming.labels
  letI : Nonempty (Fin (Fintype.card (TreeSite (pl s) k))):=⟨names (PayloadStrip.first s 0,none)⟩
  letI : Nonempty (PayloadRole s k) := ⟨.catalyst (PayloadStrip.first s 0) ⟨0,v.positive⟩⟩
  exact (menuParties_tariff names v.positive (v.payloadPacketMenu s) cols keys limit).choose

private def purchasePrice (cols keys limit : ℕ) : ℕ := by
  let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
  letI : Nonempty (Fin (Fintype.card (TreeSite ch k))):=⟨names (ChainStrip.inlet v.depth 0,none)⟩
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  exact (menuParties_tariff names v.positive v.purchasePacketMenu cols keys limit).choose

/-- Both coefficients are fixed before the parent and its date. The registers,
physical neighbor width, public row choice and loaded ballot are all unrestricted. -/
theorem signed_party_tariff (unitCost : ℕ) :
    ∃P K:ℕ,0<K ∧ ∀ {V:Type} [Fintype V] (h w : ℕ) (a : Attempt) (_hw : 0<w)
      (neighbor : ℕ) (read : ℕ→ℕ→V⊕Bool) (j : Fin (v.signedPartyCount h a)),
      let net:=v.signedParty h w a neighbor (v.partyRoleBits h) (v.partyLaneBits h w a unitCost) v.partyKeyBits read j
      net.cells+net.internal≤ P*(w+1)*(Nat.log 2 (K*w+1)+2)^3 := by
  obtain ⟨K,pos,dimensions⟩:=v.signed_party_dimensions unitCost
  let cols:=Nat.log 2 (2*v.packetRowsRate+D)+1
  let left:=v.payloadPrice stat cols v.partyKeyBits K
  let right:=v.purchasePrice cols v.partyKeyBits K
  refine ⟨left+right,K,pos,?_⟩
  intro V Vfin h w a _hw neighbor read j net
  obtain ⟨room,mass⟩:=dimensions h w a _hw
  have roleEq : v.partyRoleBits h=cols:=by simp only [partyRoleBits,cols,v.packetRows_eq h]
  let P:=v.widePlacement h w
  let N:=Stages h (2^v.W)
  cases a with
  | outer phase trial =>
    let a:=Attempt.outer phase trial
    let names : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    let : Nonempty (Fin (Fintype.card (TreeSite (pl N) k))):=⟨names (PayloadStrip.first N 0,none)⟩
    let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    have price:= (menuParties_tariff names v.positive (v.payloadPacketMenu N) cols v.partyKeyBits K).choose_spec
      D neighbor (v.widePacketRoles h) (Nat.le_max_left ..) (v.wideBallotShape P h w (.attempt a)).columns
      (v.nativeFormats P h w a).histMass (v.partyLaneBits h w a unitCost) w room mass read j
    have small : net.cells+net.internal≤ (v.payloadPrice N cols v.partyKeyBits K)*(w+1)*(Nat.log 2 (K*w+1)+2)^3:=by
      dsimp only [net]
      rw [roleEq]
      exact price
    have fixed : N=stat:=fixed_stage_count h v.W
    have coeff : v.payloadPrice N cols v.partyKeyBits K = left :=
      congrArg (fun s => v.payloadPrice s cols v.partyKeyBits K) fixed
    rw [coeff] at small
    exact small.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right left right)))
  | inner phase trial layer tick =>
    let a:=Attempt.inner phase trial layer tick
    let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    let : Nonempty (Fin (Fintype.card (TreeSite ch k))):=⟨names (ChainStrip.inlet v.depth 0,none)⟩
    let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    have price:=(menuParties_tariff names v.positive v.purchasePacketMenu cols v.partyKeyBits K).choose_spec
      D neighbor (v.widePacketRoles h) (Nat.le_max_right ..) (v.wideBallotShape P h w (.attempt a)).columns
      (v.nativeFormats P h w a).histMass (v.partyLaneBits h w a unitCost) w room mass read j
    have small : net.cells+net.internal≤ right*(w+1)*(Nat.log 2 (K*w+1)+2)^3:=by
      dsimp only [net]
      rw [roleEq]
      exact price
    exact small.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left right left)))

def signedPartyCountCap :=
  max (Fintype.card (v.payloadPacketMenu stat).index*Fintype.card (ColumnSite (PayloadStrip.Columns stat) k))
    (Fintype.card v.purchasePacketMenu.index*Fintype.card (ColumnSite (ChainStrip.Columns v.depth) k))

theorem signed_party_count_bound (h : ℕ) (a : Attempt) : v.signedPartyCount h a≤ v.signedPartyCountCap := by
  let payloadCount (s : ℕ) := Fintype.card (v.payloadPacketMenu s).index*
    Fintype.card (ColumnSite (PayloadStrip.Columns s) k)
  have fixed : payloadCount (Stages h (2^v.W))=payloadCount stat :=
    congrArg payloadCount (fixed_stage_count h v.W)
  cases a with
  | outer phase trial => exact fixed.le.trans (Nat.le_max_left _ _)
  | inner phase trial layer tick => exact Nat.le_max_right _ _

/-- Installing the entire finite lookup bank for a native signed date has the
same cubic digit exponent. The price includes the physically unselected choices. -/
theorem signed_party_bank_tariff (unitCost : ℕ) :
    ∃C K:ℕ,0<K ∧ ∀ {V:Type} [Fintype V] (h w : ℕ) (a : Attempt) (_hw : 0<w)
      (neighbor : ℕ) (read : ℕ→ℕ→V⊕Bool),
      let net:=v.signedParty h w a neighbor (v.partyRoleBits h) (v.partyLaneBits h w a unitCost) v.partyKeyBits read
      (∑ j, ((net j).cells + (net j).internal))≤ C*(w+1)*(Nat.log 2 (K*w+1)+2)^3 := by
  obtain ⟨P,K,positive,each⟩:=v.signed_party_tariff unitCost
  refine ⟨v.signedPartyCountCap*P,K,positive,?_⟩
  intro V Vfin h w a _hw neighbor read net
  have total : (∑ j, ((net j).cells + (net j).internal))≤
      v.signedPartyCount h a*(P*(w+1)*(Nat.log 2 (K*w+1)+2)^3) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (v.signedPartyCount h a))))=>
        each h w a _hw neighbor read j)
  exact total.trans ((Nat.mul_le_mul_right _ (v.signed_party_count_bound h a)).trans_eq (by ring))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
