import OAI.Hierarchy.DescentBaseDepthRAM
import OAI.Hierarchy.DescentBaseDepthBill
import OAI.Hierarchy.DescentMeasuredPriming

namespace OAI
/-! # Computing and installing the resident depth lane from the preceding
native site census and neighbor row -/
noncomputable section
namespace Hierarchy.DescentMeasuredPriming.Depth
open DescentBaseProfile ProtocolRAM DescentColonies DescentMeasuredHeader DescentPackedExchange
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {w H k Δ : ℕ}
local notation "extent" => (H*(k+1)+H*Δ)*2^k

def layout (lo H k Δ f r B scratch : ℕ) : DepthRAM.Layout where
  H := H
  N := 2^k
  Δ := Δ
  hostBits := Nat.clog 2 H
  degreeBits := Nat.clog 2 Δ
  weights := (payload lo H k Δ).sites.base
  edges := (header lo H k Δ).neighbor.base
  start := scratch
  S := 2^f*B
  g := decayExponent Δ
  lo := k-r
  M := k-f

variable (lo f r B K scratch : ℕ)
local notation "L" => layout lo H k Δ f r B scratch
local notation "dst" => ProtocolRAM.Bank.base (DescentMeasuredHeader.Tape.depth (header lo H k Δ))
local notation "src" => DepthRAM.Layout.base L (k-f+1)

def text (lo H k Δ f r B scratch w : ℕ) : Procedure w :=
  ((layout lo H k Δ f r B scratch).cpu w (k-f)).seq (PhysicalInputPhases.copying w
    ((layout lo H k Δ f r B scratch).base (k-f+1)) H (header lo H k Δ).depth.base)

def memory (lo f r B scratch : ℕ) (m : Memory w) : Memory w :=
  let plan := layout lo H k Δ f r B scratch
  PhysicalInputCopy.copied (plan.base (k-f+1)) H (header lo H k Δ).depth.base
    (plan.output m (k-f))

theorem fit (afterInput : start lo H k Δ≤ scratch)
    (endRoom : (L).base (k-f+2)<2^w) (numeric : decayExponent Δ<2^w ∧ k<2^w) : (L).Fits w := by
  have enough := Nat.le_pow_clog (by decide : 1<2) extent
  have s : H*2^k≤extent := by
    apply Nat.mul_le_mul_right
    have h:=Nat.mul_le_mul_left H (show 1≤k+1 by omega)
    omega
  have c : H*Δ≤extent := (Nat.le_add_left ..).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have e : span extent=2^(Nat.clog 2 extent) := rfl
  refine ⟨Nat.le_pow_clog (by decide) H,Nat.le_pow_clog (by decide) Δ,?_,?_,endRoom,numeric.1,?_⟩
  · change lo+9*span extent+H*2^k≤ scratch
    change lo+11*span extent≤ scratch at afterInput
    omega
  · change lo+5*span extent+H*Δ≤ scratch
    change lo+11*span extent≤ scratch at afterInput
    omega
  · exact (max_le (Nat.sub_le ..) (Nat.sub_le ..)).trans_lt numeric.2

theorem frame (m : Memory w) (a : ℕ) (old : a<scratch) (away : a<dst ∨ dst+H≤a) :
    memory (H:=H) (k:=k) (Δ:=Δ) lo f r B scratch m a=m a :=
  (PhysicalInputCopy.copied_outside _ _ _ _ _ away).trans ((L).static m _ _ old)

theorem depth_exec (m : Memory w) (ns : Native.Neighbors H) (rows : Native.Rows H (2^k))
    (afterInput : start lo H k Δ≤ scratch) (endRoom : (L).base (k-f+2)<2^w)
    (numeric : decayExponent Δ<2^w ∧ k<2^w) (supply : (L).Source ns rows m)
    (totals : ∀v,Native.totalWeight rows v<2^w) (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) :
    (text lo H k Δ f r B scratch w).Exec m (memory (H:=H) (k:=k) (Δ:=Δ) lo f r B scratch m)
      ((L).clocks w (k-f)+(6+5*H)) ∧
    ∀v : Fin H,memory (H:=H) (k:=k) (Δ:=Δ) lo f r B scratch m (dst+v.val)=
      (measuredDepth ns rows Δ r f B v:Word w) := by
  have safe:=fit lo f r B scratch afterInput endRoom numeric
  have hr : src+H<2^w := (L).end_room safe (j:=k-f+1) (by change k-f+1<k-f+2;omega)
  have old : dst≤ src := by
    change lo+4*span extent≤ scratch+(k-f+1)*2^(Nat.clog 2 H)
    change lo+11*span extent≤ scratch at afterInput
    omega
  obtain ⟨before,depth⟩:=(L).run ns rows m safe supply totals degree
  have dstRoom : dst+H<2^w := (Nat.add_le_add_right old H).trans_lt hr
  have copy : (PhysicalInputPhases.copying w src H dst).Exec
      ((L).output m (k-f)) (PhysicalInputCopy.copied src H dst ((L).output m (k-f))) (6+5*H) :=
    Procedure.Spec.exec (PhysicalInputPhases.copying_spec src H dst hr dstRoom (.inl old)) _ trivial
  refine ⟨Procedure.Exec.then before copy,?_⟩
  exact fun v=>(PhysicalInputCopy.copied_at _ _ _ _ _ v.isLt).trans (depth v)

theorem resident (m : Memory w) (old : Resident lo H k Δ f B K m) (ahead : start lo H k Δ≤ scratch) :
    Resident lo H k Δ f B K (memory (H:=H) (k:=k) (Δ:=Δ) lo f r B scratch m) := by
  apply resident_of_frame _ _ _ _ _ _ _ old
  intro j hj i hi live
  have s : H≤ span extent := by
    apply le_trans _ (Nat.le_pow_clog (by decide) extent)
    apply le_trans _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    exact (by have h:=Nat.mul_le_mul_left H (show 1≤k+1 by omega);omega)
  have notDepth : j≠4 := by rintro rfl;simp [literal] at live
  change lo+11*span extent≤ scratch at ahead
  have low:=Nat.mul_le_mul_right (span extent) (show j+1≤11 from hj)
  simp only [Nat.succ_mul] at low
  apply frame
  · change lo+j*span extent+i<scratch;omega
  · change lo+j*span extent+i<lo+4*span extent ∨ lo+4*span extent+H≤lo+j*span extent+i
    by_cases pre : j<4
    · left
      have h:=Nat.mul_le_mul_right (span extent) (show j+1≤4 from pre)
      simp only [Nat.succ_mul] at h;omega
    · right
      have h:=Nat.mul_le_mul_right (span extent) (show 5≤j by omega)
      omega

end Hierarchy.DescentMeasuredPriming.Depth

end
end OAI
