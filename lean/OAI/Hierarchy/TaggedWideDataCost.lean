import OAI.Hierarchy.TaggedWideDataWorkspace
import OAI.Hierarchy.TaggedWideStagePool
import OAI.Hierarchy.TaggedWireRoleRoomBudget
import OAI.Hierarchy.TaggedWireArchiveAperture

namespace OAI
/-! # Width of the actual common data workspace on the physical board -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open scoped Classical BigOperators

variable {T G E H : Type} [Fintype T] [Fintype G] [Fintype E] [Fintype H]
variable (ports lanes dates view : ℕ) (width : T→ℕ) (privateCap : E→ℕ) (historyCap : H→ℕ)

private theorem cap_sum {I : Type} [Fintype I] (c : I→ℕ) (bound : ℕ) (fits : ∀i,c i ≤ bound) :
    Fintype.card ((i:I) × Fin (c i)) ≤ Fintype.card I*bound := by
  rw [Fintype.card_sigma]
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>fits i)

theorem workspace_bill (n w groups free roles K J : ℕ)
    (pool : (Fintype.card G+1)*ports ≤ groups*n)
    (boundedFree : Fintype.card E ≤ free*n) (boundedRoles : Fintype.card H ≤ roles*n)
    (localW : ∀t,width t ≤ w) (old : ∀e,privateCap e ≤ K*w) (states : ∀p,historyCap p ≤ J*w)
    (last : view ≤ J*w) :
    Fintype.card (DataWorkspace T G E H ports lanes dates view width privateCap historyCap) ≤
     (Fintype.card T*(2*groups*lanes)+2*free*K+dates*roles*J+groups*J)*(n*w) := by
  have positive : Fintype.card (OutputData T G ports lanes width)≤
      Fintype.card T*(2*groups*lanes)*(n*w) := by
    simp only [OutputData,Fintype.card_sigma,Fintype.card_prod,Fintype.card_option,Fintype.card_bool,Fintype.card_fin]
    calc
      _ ≤ ∑ _t : T,(Fintype.card G+1)*(2*(ports*lanes))*w := by
        apply Finset.sum_le_sum
        intro t _
        gcongr
        exact localW t
      _ = Fintype.card T*(2*lanes*w)*((Fintype.card G+1)*ports) := by simp;ring
      _ ≤ Fintype.card T*(2*lanes*w)*(groups*n) := Nat.mul_le_mul_left _ pool
      _ = _ := by ring
  have privateBits := (cap_sum privateCap (K*w) old).trans (Nat.mul_le_mul_right _ boundedFree)
  have stateBits := (cap_sum historyCap (J*w) states).trans (Nat.mul_le_mul_right _ boundedRoles)
  have views : Fintype.card G*ports*view ≤ groups*n*(J*w) :=
    Nat.mul_le_mul (((Nat.mul_le_mul_right _ (Nat.le_succ _))).trans pool) last
  simp only [DataWorkspace,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  calc
    _ ≤ Fintype.card T*(2*groups*lanes)*(n*w)+(2*(free*n*(K*w))+
          (dates*(roles*n*(J*w))+groups*n*(J*w))) := by gcongr
    _ = _ := by ring

section Canonical
open ProbeStage ProbeStage.CoreBoard HistoryRoles AdaptiveProbe TaggedShorterSupergroups ProtocolRAM.Calendar
open scoped Classical
variable {h W k attempts pad roles : ℕ} (S : PurchaseSampler)

theorem doubled_pool (padding : 2*roles≤2^pad) (small : 2^superAddress W pad h≤2^h) :
    let dir := stageDir h W roles pad padding
    (dir.groups+1)*2^superAddress W pad h≤
      (2*((2*rounds (2^W)+1)*4^(rounds (2^W)+1))*roles+2)*2^h := by
  intro dir
  have bound := (purchase_stages h W roles pad padding).choose_spec
  change dir.groups*(2^superAddress W pad h) ≤ _ at bound
  calc
    _ = dir.groups*2^superAddress W pad h+2^superAddress W pad h := by ring
    _ ≤ (2*((((2*rounds (2^W)+1)*4^(rounds (2^W)+1))*2^h)*roles)+2^h)+2^h := by omega
    _ = _ := by ring

theorem actual_workspace {T : Type} [Fintype T] (padding : 2*roles≤2^pad)
    (small : 2^superAddress W pad h≤2^h) (mesh : Mesh) (lanes dates w unitCost costCap fuel K : ℕ)
    (width : T→ℕ) (smallWidth : ∀t,width t ≤ w)
    (privateCap : Free S h (2^W) k→ℕ) (smallPrivate : ∀e,privateCap e ≤ K*w) :
    let dir := stageDir h W roles pad padding
    let publicCount := HistoryRoles.RoleProgram.RoleRoom.publicFactor (2^W) k S.degree attempts
    let packedCount := 2*((2*rounds (2^W)+1)*4^(rounds (2^W)+1))*roles+2
    let J := clock mesh*unitCost+(2*costCap+1)+fuel
    let floor := ceiling S (h:=h) (W:=W) (k:=k) (attempts:=attempts) mesh unitCost costCap fuel w
    Fintype.card (DataWorkspace T (Fin dir.groups) _ _ (2^superAddress W pad h) lanes dates (J*w)
      width privateCap floor) ≤
      (Fintype.card T*(2*packedCount*lanes)+2*publicCount*K+dates*publicCount*J+packedCount*J)*(2^h*w) := by
  intro dir publicCount packedCount J floor
  let inc : Free S h (2^W) k ↪ Public S h W k attempts :=
    ⟨fun f=>.inl (.inl (f,false)),fun _ _ eqn=>congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj eqn))⟩
  have pub := HistoryRoles.RoleProgram.RoleRoom.raw_public_bound (h:=h) (W:=W) (k:=k) (attempts:=attempts) S
  apply workspace_bill
  · simpa only [Fintype.card_fin] using doubled_pool (h:=h) (W:=W) padding small
  · exact (Fintype.card_le_of_embedding inc).trans pub
  · exact pub
  · exact smallWidth
  · exact smallPrivate
  · exact ceiling_le S mesh unitCost costCap fuel w
  · exact le_rfl

end Canonical

end Hierarchy.Tagged.WideStack

end
end OAI
