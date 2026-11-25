import OAI.Hierarchy.TaggedWireRoleRoomShape
import OAI.Hierarchy.TaggedWirePublicCount
import OAI.Hierarchy.ProtocolRAMCoreCatalogueRowBudget
import OAI.Hierarchy.ProtocolRAMPurchaseFrozenCount
import OAI.Hierarchy.ProbeStageRecordSpace
import OAI.Hierarchy.ProbeStageAddress
import OAI.Hierarchy.ProbeCommodityBounds

namespace OAI
/-! # Linear native address space for the complete signed turn directory -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups WireTelescope Filter
open scoped Classical
variable {h W k attempts H R edges : ℕ}

def publicFactor (d k degree jobs : ℕ) :=
  siteFactor d k*(Incident.room k degree jobs+(1+2*k)+1)

theorem raw_public_bound (S : PurchaseSampler) :
    Fintype.card (Public S h W k attempts) ≤ publicFactor (2^W) k S.degree attempts*2^h := by
  have sites : Fintype.card (Site h (2^W) k)=siteLast h (2^W) k+1 :=
    (Fintype.card_congr (siteNumber h (2^W) k)).trans (Fintype.card_fin _)
  have bound := (public_count (h:=h) (W:=W) (k:=k) (attempts:=attempts) S).trans
    (Nat.mul_le_mul_right _ (sites.le.trans (site_count h (2^W) k (Nat.two_pow_pos _))))
  simpa only [publicFactor,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using bound

def oldFactor (d k E : ℕ) := E+(1+2*(2*rounds d+1)*k)+siteFactor d k*k

theorem old_bound {E : ℕ} (fit : edges≤E*2^h) :
    Fintype.card (Old h W k edges)≤oldFactor (2^W) k E*2^h := by
  let mark : Columns h (2^W)→Site h (2^W) k := fun c=>(c,none)
  have center : Function.Injective mark :=
    fun _ _ same=>congrArg Prod.fst same
  have cols := (Fintype.card_le_of_injective _ center).trans
    ((Fintype.card_congr (siteNumber h (2^W) k)).le.trans
      ((Fintype.card_fin _).le.trans (site_count h (2^W) k (Nat.two_pow_pos _))))
  have cat := Nat.mul_le_mul_right k cols
  have stage : Stages h (2^W)=2*rounds (2^W)+1 := template_length ..
  have goods : Fintype.card (Goods h W k)=2^h*(1+2*(2*rounds (2^W)+1)*k) := by
    change Fintype.card (Commodity (Fin (2^h)) (Stages h (2^W)) k)=_
    rw [commodity_count,Fintype.card_fin,stage]
  have cats : Fintype.card (Catalysts h W k)=Fintype.card (Columns h (2^W))*k := by
    change Fintype.card (Columns h (2^W) × Fin k)=_
    rw [Fintype.card_prod,Fintype.card_fin]
  change Fintype.card (Fin edges ⊕ (Goods h W k ⊕ Catalysts h W k)) ≤ _
  rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,goods,cats]
  calc
    _ ≤ E*2^h+(2^h*(1+2*(2*rounds (2^W)+1)*k)+(siteFactor (2^W) k*2^h)*k) :=
      Nat.add_le_add fit (Nat.add_le_add_left cat _)
    _ = oldFactor (2^W) k E*2^h := by unfold oldFactor;ring

def directoryFactor (W k attempts pad : ℕ) :=
  2*((2*rounds (2^W)+1)*4^(rounds (2^W)+1))*copies k attempts+
  2^(9*2^W+18*(2^W-1)+2+pad)

theorem packed_bound (h W k attempts pad : ℕ) (ok : 2*copies k attempts≤2^pad) :
    (stageDir h W (copies k attempts) pad ok).groups*2^superAddress W pad h≤
      directoryFactor W k attempts pad*2^h := by
  let cp := copies k attempts
  have cost := (purchase_stages h W cp pad ok).choose_spec
  have height := CoreCatalogue.packed_height W pad h
  exact cost.trans ((Nat.add_le_add_left height _).trans_eq (by unfold directoryFactor;dsimp [cp];ring))

def boughtFactor (d k jobs degree depth : ℕ) := jobs*((2*rounds d+1)*(2*k))*degree^depth

theorem padded_edges (S : PurchaseSampler) (depth : ℕ) (order : Fin R≃Edges S h (2^W) k) :
    R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth) ≤
      (CoreCatalogue.coreFactor S (2^W) k+boughtFactor (2^W) k attempts S.degree depth)*2^h := by
  have rowCap : R≤CoreCatalogue.coreFactor S (2^W) k*2^h := by
    have eq := (Fintype.card_fin R).symm.trans (Fintype.card_congr order)
    exact eq.le.trans (CoreCatalogue.rows_linear S h W k)
  rw [PurchaseFrozen.count_eq,PurchaseFrozen.paths]
  exact (Nat.add_le_add_right rowCap _).trans_eq (by unfold boughtFactor;ring)

/-- The actual raw catalogue includes every purchased candidate of every
attempt. The complete rounded memory footprint has a single coefficient,
chosen before the height, permutation or selected purchases. -/
theorem linear (S : PurchaseSampler) (W k attempts pad depth initial : ℕ) (ok : 2*copies k attempts≤2^pad) :
    ∃ C : ℕ,∀ (h R : ℕ) (_order : Fin R≃Edges S h (2^W) k) (start : ℕ), start ≤ initial*2^h →
      let dir := stageDir h W (copies k attempts) pad ok
      let edges := R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
      (shape (R:=R) S dir edges).ceiling start≤C*2^h := by
  let d := 2^W
  let f := CoreCatalogue.coreFactor S d k
  let e := f+boughtFactor d k attempts S.degree depth
  let p := publicFactor d k S.degree attempts
  let u := siteFactor d k
  let a := directoryFactor W k attempts pad
  refine ⟨3*(initial+7*oldFactor d k e+2*p+2*f+2+u*(2*k)+3*a+1),?_⟩
  intro h R order start base
  dsimp only
  let dir := stageDir h W (copies k attempts) pad ok
  let edges := R+attempts*(PurchaseFrozen.count h d k*PurchaseFrozen.paths h S.degree depth)
  have raw : edges≤e*2^h := padded_edges (attempts:=attempts) S depth order
  have old : Fintype.card (Old h W k edges)≤oldFactor d k e*2^h := old_bound raw
  have pub : Fintype.card (Public S h W k attempts)≤p*2^h := raw_public_bound S
  have core : R≤f*2^h :=
    ((Fintype.card_fin R).symm.trans (Fintype.card_congr order)).le.trans (CoreCatalogue.rows_linear S h W k)
  have axis : (siteLast h d k+1)*(2*k)≤(u*(2*k))*2^h := by
    have bound := Nat.mul_le_mul_right (2*k) (site_count h d k (Nat.two_pow_pos _))
    simpa only [u,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bound
  have packed : dir.groups*2^superAddress W pad h≤a*2^h := packed_bound h W k attempts pad ok
  have groups : dir.groups≤a*2^h :=
    (show dir.groups≤dir.groups*2^superAddress W pad h by
      simpa using Nat.mul_le_mul_left dir.groups (Nat.two_pow_pos (superAddress W pad h))).trans packed
  have one := Nat.two_pow_pos h
  change 3*(start+7*Fintype.card (Old h W k edges)+2*Fintype.card (Public S h W k attempts)+
    2*R+2*2^h+(siteLast h d k+1)*(2*k)+dir.groups*2^superAddress W pad h+
    (dir.groups+dir.groups*2^superAddress W pad h)+1)≤_
  calc
    _ ≤ 3*(initial*2^h+7*(oldFactor d k e*2^h)+2*(p*2^h)+2*(f*2^h)+2*2^h+
      (u*(2*k))*2^h+3*(a*2^h)+2^h) := by omega
    _ = _ := by ring


theorem word_room (S : PurchaseSampler) (W k attempts pad depth initial : ℕ) (ok : 2*copies k attempts≤2^pad) :
    ∀ᶠ h : ℕ in Filter.atTop,∀ (R : ℕ) (_order : Fin R≃Edges S h (2^W) k) (start : ℕ), start ≤ initial*2^h →
      let dir := stageDir h W (copies k attempts) pad ok
      let edges := R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
      (shape (R:=R) S dir edges).ceiling start < 2^Native.wordBits h (2^W) Native.copies := by
  obtain ⟨C,cost⟩ := linear S W k attempts pad depth initial ok
  filter_upwards [Native.eventually_append_room (2^W) Native.copies C] with h space
  intro R order start bound
  exact (cost h R order start bound).trans_lt ((Nat.le_add_left _ _).trans_lt space)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
end

end OAI
