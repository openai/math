import OAI.Hierarchy.DescentScheduledResetBounds
import OAI.Hierarchy.DescentScheduledResetDegrees
import OAI.Hierarchy.DescentDatedFiniteRooms

namespace OAI
/-! # A single address exponent for every actual reset of the same native machine -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentPackedWalsh
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset τ maximum drift B : ℕ) {ι : ℕ→Type*}
  (sites age p degree oldOperand oldPrimitive floor : ∀h,ι h→ℕ)
  (ordinary : ∀h,ι h→ℕ→Dated.Ordinary) (old : ∀h,ι h→StageVenueTail.Date)
  (wire : ∀h,ι h→ℕ→ℕ→Bank) (roster : ∀h,ι h→Bank)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "tb_" h:arg => tail τ (J_ h)
local notation "S_" h:arg i:arg =>stageNumbers G t (J_ h) f g reset (sites h i) (tb_ h)
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "cap_" h:arg i:arg => ((capCalendar G.b t g (J_ h)).take (age h i)).prod*256
local notation "seed_" h:arg i:arg =>(S_ h i).firstWidth G.b (p h i)
local notation "grain_" h:arg i:arg =>(S_ h i).grainAt G.b (p h i) 0
local notation "token_" h:arg i:arg =>DescentPrimitivePalette.printedBits G (seed_ h i) (grain_ h i) op
local notation "prior_" h:arg i:arg =>ResetOutput.Prior.atDate G (S_ h i) (age h i) (p h i) drift (oldOperand h i) (oldPrimitive h i) (token_ h i) (old h i)
local notation "oldCut_" h:arg i:arg => NativePitch.resetCut (S_ h i) (k_ h) (tb_ h) (p h i) f h (age h i)
local notation "nextM_" h:arg i:arg => NativePitch.incoming (S_ h i) (k_ h) (tb_ h) (p h i) f h (ordinary h i) (age h i+1)
local notation "e_" h:arg i:arg =>receiverCut G (S_ h i) board (k_ h) (tb_ h) (age h i) (p h i) f g drift
  (degree h i) h (oldCut_ h i) (nextM_ h i) op.C op.w (oldOperand h i) (oldPrimitive h i) (token_ h i) (old h i)
local notation "a_" h:arg i:arg =>scheduled G (S_ h i) board (k_ h) (tb_ h) (age h i) (p h i) f g drift (degree h i) h
  (ordinary h i) op (seed_ h i) (grain_ h i) (oldOperand h i) (oldPrimitive h i) (old h i)
  (wire h i) (roster h i) (floor h i)
local notation "base_" h:arg i:arg =>(a_ h i).rebased ((a_ h i).stageStart (floor h i))
theorem all_scheduled_increments (den : 0<B) (branch : G.b≤2^(capRate G t g))
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B)
    (receiver : 2*degreeRate G board op t f g reset maximum≤B) (tailBought : τ≤B)
    (stagePayload : ∀h i j,(ordinary h i j).payload=h)
    (bound : ℕ) (small : ∀h i,p h i≤h) (degrees : ∀h i,degree h i≤bound)
    (seed : Bounded sites) (before : ∀h i,age h i<(S_ h i).length)
    (oldDegree : ∀h i,(old h i).degree≤ maximum) (oldCap : ∀h i,(old h i).cap=cap_ h i)
    (oldPaid : ∀h i,(old h i).paidBits=(S_ h i).censusBits (p h i))
    (oldHost : ∀h i,(old h i).hosts=(S_ h i).hostSize (age h i))
    (oldGroup : ∀h i,(old h i).groups=(S_ h i).groupCount (age h i))
    (oldK : ∀h i,(old h i).k=k_ h) (oldM : ∀h i,(old h i).lanes=2^(oldCut_ h i))
    (degreeQuota : maximum≤quota t)
    (archives : ∀ᶠ h:ℕ in atTop,∀i,let N:=(prior_ h i).nodes;
      (DescentOperandWidth.recordBits G (S_ h i) (k_ h) (tb_ h) drift (degree h i) (p h i)*N)*oldOperand h i≤h/2 ∧
      ((token_ h i)*N)*oldPrimitive h i≤h/2) :
    Bounded (fun h i=>(a_ h i).fullEnd (floor h i)-floor h i) :=by
  let d (h : ℕ) (i : ι h) : Fin (maximum+1):=⟨(old h i).degree,Nat.lt_succ_of_le (oldDegree h i)⟩
  apply Bounded.finite_parts d
  intro D
  let part (h : ℕ) := {i:ι h //d h i=D}
  have choose : 2*ResetOutput.receiverRate G board op t f g reset D.val≤B :=
    (Nat.mul_le_mul_left 2 (Finset.le_sup (f:=fun z:Fin (maximum+1)=>ResetOutput.receiverRate G board op t f g reset z.val)
      (Finset.mem_univ D))).trans receiver
  exact scheduled_increment G board op t f g reset τ D.val drift B
    (fun h (i:part h)=>sites h i.val) (fun h i=>age h i.val) (fun h i=>p h i.val)
    (fun h i=>degree h i.val) (fun h i=>oldOperand h i.val) (fun h i=>oldPrimitive h i.val)
    (fun h i=>floor h i.val) (fun h i=>ordinary h i.val) (fun h i=>old h i.val)
    (fun h i=>wire h i.val) (fun h i=>roster h i.val) den branch cutoff choose tailBought
    (fun h i=>stagePayload h i.val) bound (fun h i=>small h i.val) (fun h i=>degrees h i.val)
    (seed.restrict _) (fun h i=>before h i.val) (fun h i=>congrArg Fin.val i.property)
    (fun h i=>oldCap h i.val) (fun h i=>oldPaid h i.val) (fun h i=>oldHost h i.val)
    (fun h i=>oldGroup h i.val) (fun h i=>oldK h i.val) (fun h i=>oldM h i.val)
    ((Nat.le_of_lt_succ D.isLt).trans degreeQuota)
    (archives.mono fun h q i=>q i.val)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
