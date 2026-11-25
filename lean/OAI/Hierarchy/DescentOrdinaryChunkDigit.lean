import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentSeedEpochRoom

namespace OAI
/-! # The chunk ordinal of the role-population scan at the actual epoch cutoff -/
namespace Hierarchy.DescentSixParty
open DescentSIMDLookup DescentCompiler DescentCompiler.TerminalScale Filter
open ThreeFlat
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- A nonempty input word holds at least one old group. -/
theorem group_chunk_digit (G M n : ℕ) (positive : 0<M) (groups : G≤2^n) :
    Nat.clog 2 (chunks G M+1)≤ n+1 :=by
  have count : chunks G M≤ G :=by
    change (G+M-1)/M≤ G
    apply (Nat.div_le_iff_le_mul_add_pred positive).mpr
    have plenty : G≤ G*M :=by simpa using Nat.mul_le_mul_left G (show 1≤ M from positive)
    have comm : M*G=G*M:=Nat.mul_comm ..
    omega
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  have : (0:ℕ)<2^n:=by positivity
  omega

/-- The group count itself can exceed a word-sized lookup tariff. Only its
binary chunk ordinal is used as a key. -/
theorem stage_chunk_digit (t f g reset τ B : ℕ) (wide : 5≤ B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M i pitch : ℕ, 0<pitch →
        Nat.clog 2 (chunks ((stageNumbers G t J f g reset M (tail τ J)).groupCount i) pitch+1)≤ h/4 :=by
  let c:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let C:=τ+c*(t+1)+1
  filter_upwards [eventually_late (C+1) B (by omega), eventually_ge_atTop 1] with h late hp
  intro J M i pitch positive
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  have groups : S.groupCount i≤2^(tail τ J+k*((t+1)*J)) :=by
    change 2^(tail τ J)*(2^k)^((t+1)*J-i)≤_
    rw [←pow_mul,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by gcongr; omega)
  have number:=group_chunk_digit (S.groupCount i) pitch _ positive groups
  have kb : k≤ c*(J+1):=groupBits_linear ..
  have age : C+1≤ J:=late
  have jle : J+1≤2^(J+1) :=(Nat.lt_two_pow_self (n:=J+1)).le
  have cle : C≤2^(J+1):=by omega
  have coarse : tail τ J+k*((t+1)*J)+1≤ C*((J+1)*(J+1)):=by
    change τ*(J+1)+k*((t+1)*J)+1≤(τ+c*(t+1)+1)*((J+1)*(J+1))
    have grow:=Nat.mul_le_mul_right ((t+1)*J) kb
    calc
      _≤τ*(J+1)+c*(J+1)*((t+1)*J)+1 :=by omega
      _≤_ :=by ring_nf;omega
  have short : C*((J+1)*(J+1))≤ scale J 3:=by
    refine (Nat.mul_le_mul cle (Nat.mul_le_mul jle jle)).trans_eq ?_
    unfold scale
    rw [←pow_add,←pow_add]
    congr 1
    ring
  have room:=DescentDatedSeedStartup.epoch_room h B 3 hp wide (by omega : 0<J)
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  change Nat.clog 2 (chunks (S.groupCount i) pitch+1)*4≤h
  rw [Nat.mul_comm]
  exact (Nat.mul_le_mul_left 4 ((number.trans coarse).trans short)).trans room

end Hierarchy.DescentSixParty

end OAI
