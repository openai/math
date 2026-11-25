import OAI.Hierarchy.DescentInitialArgumentCapacity
import OAI.Hierarchy.DescentCapAtAge
import OAI.Hierarchy.DescentResetSignedTokenWidth
import OAI.Hierarchy.DescentScheduledEntranceRoom
import OAI.Hierarchy.DescentCalibratedResetChart

namespace OAI
/-! # The instantiated complete reset date, from its true previous floor to its final published bank -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentPackedWalsh
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
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
local notation "sample_" h:arg i:arg =>ResetOutput.originalSample G op t f g reset τ D drift (J_ h)
  (sites h i) (age h i) (p h i) (degree h i) h (e_ h i) (oldCut_ h i) (2^(e_ h i)) (nextM_ h i) (base_ h i) (prior_ h i)

/-- The actual previous operand/role archive word and normalized venue width are
read from the seed or the preceding returned date. All later roofs, LUTs and
signed/candidate/paid sheets are computed here from calendar dimensions. -/
theorem scheduled_increment (den : 0<B) (branch : G.b≤2^(capRate G t g))
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B)
    (receiver : 2*ResetOutput.receiverRate G board op t f g reset D≤B) (tailBought : τ≤B)
    (stagePayload : ∀h i j,(ordinary h i j).payload=h)
    (bound : ℕ) (small : ∀h i,p h i≤h) (degrees : ∀h i,degree h i≤bound)
    (seed : Bounded sites) (before : ∀h i,age h i<(S_ h i).length)
    (oldDegree : ∀h i,(old h i).degree=D) (oldCap : ∀h i,(old h i).cap=cap_ h i)
    (oldPaid : ∀h i,(old h i).paidBits=(S_ h i).censusBits (p h i))
    (oldHost : ∀h i,(old h i).hosts=(S_ h i).hostSize (age h i))
    (oldGroup : ∀h i,(old h i).groups=(S_ h i).groupCount (age h i))
    (oldK : ∀h i,(old h i).k=k_ h) (oldM : ∀h i,(old h i).lanes=2^(oldCut_ h i))
    (degreeQuota : D≤quota t)
    (archives : ∀ᶠ h:ℕ in atTop,∀i,let N:=(prior_ h i).nodes;
      (DescentOperandWidth.recordBits G (S_ h i) (k_ h) (tb_ h) drift (degree h i) (p h i)*N)*oldOperand h i≤h/2 ∧
      ((token_ h i)*N)*oldPrimitive h i≤h/2) :
    Bounded (fun h i=>(a_ h i).fullEnd (floor h i)-floor h i) :=by
  let samples:=fun h (i:ι h)=>sample_ h i
  let out:=fun h (i:ι h)=>(samples h i).output G board D f g op.C op.w
  let a:=fun h (i:ι h)=>a_ h i
  let oldExp:=fun h (i:ι h)=>oldCut_ h i
  let newM:=fun h (i:ι h)=>nextM_ h i
  let roots:=fun h (i:ι h)=>e_ h i
  let priors:=fun h (i:ι h)=>prior_ h i
  let base:=fun h (i:ι h)=>base_ h i
  have same (h : ℕ) (i : ι h) : (a h i).successor=out h i :=by
    have raised : ({old h i with degree:=D,cap:=cap_ h i,paidBits:=(S_ h i).censusBits (p h i)} : StageVenueTail.Date)=old h i :=by
      rw [←oldDegree h i,←oldCap h i,←oldPaid h i]
    have last:=named_successor G (S_ h i) board (k_ h) (tb_ h) (age h i) (p h i) f g drift (degree h i) h
      (roots h i) (oldExp h i) (2^(roots h i)) (newM h i) op.C op.w (oldOperand h i) (oldPrimitive h i) (token_ h i)
      (old h i) (wire h i) (roster h i) (floor h i)
    change _=ResetOutput.fromBoard G (S_ h i) board (k_ h) (tb_ h) (age h i) (p h i) f g drift (degree h i) h (roots h i)
      (oldExp h i) (2^(roots h i)) (newM h i) op.C op.w
      {priors h i with venue:={({old h i with degree:=D,cap:=cap_ h i,paidBits:=(S_ h i).censusBits (p h i)} : StageVenueTail.Date) with degree:=D}} (base h i)
    rw [raised]
    exact last
  have priced : ResetOutput.Installed out :=by
    filter_upwards [scheduled_tables G board op t f g reset τ D drift B den receiver branch bound] with h all_
    intro i
    rw [←same h i]
    exact all_ (sites h i) (age h i) (p h i) (degree h i) (ordinary h i) (old h i)
      (oldOperand h i) (oldPrimitive h i) (floor h i) (wire h i) (roster h i)
      (small h i) (degrees h i) (oldDegree h i) (oldCap h i) (oldPaid h i)
  have selected : ∀ᶠ h:ℕ in atTop,∀i,8*(out h i).groupWidth≤h:=by
    filter_upwards [scheduled_short G board op t f g reset τ D drift B den receiver branch bound] with h q
    intro i
    rw [←same h i]
    exact q (sites h i) (age h i) (p h i) (degree h i) (ordinary h i) (old h i)
      (oldOperand h i) (oldPrimitive h i) (floor h i) (wire h i) (roster h i)
      (small h i) (degrees h i) (oldDegree h i) (oldCap h i) (oldPaid h i)
  have heightRoom : Bounded (fun h (_:ι h)=>h) :=by
    exact ⟨1,Filter.Eventually.of_forall fun h i=>by simpa only [one_mul] using (Nat.lt_two_pow_self (n:=h)).le⟩
  have hasNode (h : ℕ) (i : ι h) : 0<(priors h i).nodes :=by
    change 0<(if age h i=0 then 1 else (S_ h i).retainedNodes)
    split
    · decide
    · exact pow_pos (Nat.two_pow_pos _) _
  have hadTypes (h : ℕ) (i : ι h) :
      0<DescentOperandWidth.recordBits G (S_ h i) (k_ h) (tb_ h) drift (degree h i) (p h i) ∧ 0<token_ h i :=by
    constructor
    · exact (Nat.succ_pos _).trans_le (Nat.le_max_right ..)
    · apply Nat.clog_pos (by decide : 1<2)
      unfold DescentPrimitivePalette.colors
      omega
  have widthLanes {b N M h : ℕ} (bits : 0<b) (count : 0<N) (packed : (b*N)*M≤h/2) : M≤h :=
    (Nat.le_mul_of_pos_left M (Nat.mul_pos bits count)).trans (packed.trans (Nat.div_le_self ..))
  have operandLanes : Bounded oldOperand :=heightRoom.of_eventually_le (archives.mono fun h q i=>
    widthLanes (hadTypes h i).1 (hasNode h i) (q i).1)
  have roleLanes : Bounded oldPrimitive :=heightRoom.of_eventually_le (archives.mono fun h q i=>
    widthLanes (hadTypes h i).2 (hasNode h i) (q i).2)
  have entry:=scheduled_entrance G board op t f g reset τ B drift sites age p degree
    (fun h i=>seed_ h i) (fun h i=>grain_ h i) oldOperand oldPrimitive floor ordinary old wire roster
    D seed den cutoff (fun h i=>(before h i).le) small (fun h i=>(oldDegree h i).le)
  have cuts (h : ℕ) (i : ι h) : roots h i≤oldExp h i ∧ oldExp h i≤(S_ h i).groupWidth (k_ h) (tb_ h) (age h i) :=by
    constructor
    · exact (Nat.min_le_left ..).trans (Nat.min_le_left ..)
    · let m:=(S_ h i).groupWidth (k_ h) (tb_ h) (age h i)+k_ h
      have l:=show laneBits m h ((S_ h i).localWalshBits (p h i) m f (quota t))≤ m from Nat.min_le_left ..
      change laneBits m h _-k_ h≤_
      exact (Nat.sub_le_sub_right l (k_ h)).trans_eq (Nat.add_sub_cancel ..)
  have cutNext (h : ℕ) (i : ι h) : roots h i≤(S_ h i).groupWidth (k_ h) (tb_ h) (age h i+1) :=
    (Nat.min_le_left ..).trans ((Nat.min_le_right ..).trans (Nat.min_le_right ..))
  have mask:=ResetOutput.normalized_mask_rate G t f g reset τ B sites age p newM ordinary stagePayload den tailBought
  have oldWords : ∀ᶠ h:ℕ in atTop,∀i,
      DescentSignedCableCodec.width D (cap_ h i)*(old h i).lanes≤h/2 ∧
      (old h i).paidBits*(old h i).lanes≤h/2 :=by
    filter_upwards [eventually_late 1 B den,DescentSixParty.eventually_actual_width G t f g reset B (quota t) τ] with h late width
    intro i
    let S:=S_ h i
    let m:=S.groupWidth (k_ h) (tb_ h) (age h i)+k_ h
    let b:=S.localWalshBits (p h i) m f (quota t)
    have tb : tb_ h≤τ*(Nat.log 2 h+1)^2 :=
      Nat.mul_le_mul_left _ ((Nat.succ_le_succ (Nat.div_le_self ..)).trans (by nlinarith))
    have room : 8*b≤h :=(width (sites h i) (tb_ h) (age h i) (p h i) (small h i) tb (before h i).le).1.trans (Nat.div_le_self ..)
    have pitch : oldExp h i≤laneBits m h b:=Nat.sub_le ..
    have nonzero : 0<b:=by unfold b AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
    have pay : S.censusBits (p h i)≤2*b:=by unfold b AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
    have q:=DescentResetSignedTokens.quarter_key nonzero room pay pitch
    rw [oldM h i,oldPaid h i]
    exact ⟨DescentResetSignedTokens.signed_key_at S (p h i) late (before h i).le
      (NativePitch.cap_at_age G t g (J_ h) (age h i)) degreeQuota room pitch,q.trans (by omega)⟩
  have previousKey : ∀ᶠ h:ℕ in atTop,∀i,(out h i).middle.signedBits*2^(oldExp h i)≤h/2 :=
    oldWords.mono fun h q i=>by rw [←oldM h i];exact (q i).1
  have limits : ∀ᶠ h:ℕ in atTop,∀i,(priors h i).nodes≤(S_ h i).retainedNodes ∧
      (priors h i).arguments≤(S_ h i).retainedArgumentsAt G drift :=by
    filter_upwards [eventually_late 1 B den] with h late
    intro i
    exact DescentSixParty.AtomSchedule.prior_capacity (S_ h i) G (age h i) (p h i) drift (oldOperand h i) (oldPrimitive h i) (token_ h i) (old h i) late branch
  have axes:=schedule_space G t f g reset τ B sites age seed (fun h i=>(before h i).le)
  have oldPitch (h : ℕ) (i : ι h) : (old h i).lanes≤(S_ h i).groupCount (age h i) :=by
    rw [oldM h i]
    exact (Nat.pow_le_pow_right (by decide) (cuts h i).2).trans ((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  have wordPositive (h : ℕ) (i : ι h) : 0<DescentSignedCableCodec.width D (cap_ h i):=by
    unfold DescentSignedCableCodec.width;omega
  have paid : ∀ᶠ h:ℕ in atTop,∀i,(S_ h i).censusBits (p h i)*(old h i).lanes≤h/2 ∧ (old h i).lanes≤h :=by
    filter_upwards [oldWords] with h words
    intro i
    rw [←oldPaid h i]
    exact ⟨(words i).2,(Nat.le_mul_of_pos_left _ (wordPositive h i)).trans ((words i).1.trans (Nat.div_le_self ..))⟩
  have sheets:=ResetOutput.original_reset_bounds G board op t f g reset τ D drift B sites age p degree roots oldExp newM base priors
    a floor same (fun _ _=>rfl) entry den branch bound small degrees seed before cuts cutNext oldHost oldGroup oldK
    ⟨1,mask.mono fun h m i=>m i rfl⟩ previousKey paid limits operandLanes roleLanes archives selected priced
  apply complete_increment a floor sheets
  have cal:=ResetOutput.original_inputs G board op t f g reset τ D drift B sites age p degree roots oldExp newM base priors
    den branch bound small degrees
  let level : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self ..)
  have oldDims (h : ℕ) (i : ι h) : (a h i).ingress.signed.bits=DescentSignedCableCodec.width D (cap_ h i):=by
    change DescentSignedCableCodec.width (old h i).degree (cap_ h i)=_
    rw [oldDegree]
  refine ⟨cal.sheets.block.bounded level,axes.oldHost,?_,cal.previousCap.bounded level,axes.oldGroup.of_le oldPitch,
    axes.oldGroup.of_le (fun h i=>by
      change 2^(oldExp h i) ≤ _
      rw [←oldM h i]
      exact oldPitch h i),⟨1,?_⟩,⟨1,?_⟩,⟨1,?_⟩⟩
  · exact axes.oldGroup.of_le (fun h i=>((S_ h i).group_power (k:=k_ h) rfl rfl _).le)
  · filter_upwards [oldWords] with h words
    intro i
    rw [oldDims,Nat.one_mul]
    exact (words i).1.trans (Nat.div_le_self ..)
  · filter_upwards [oldWords] with h words
    intro i
    rw [Nat.one_mul]
    exact (words i).2.trans (Nat.div_le_self ..)
  · filter_upwards [oldWords] with h words
    intro i
    rw [oldDims,Nat.one_mul]
    change max (old h i).paidBits _*2^(oldExp h i)≤h
    rw [←oldM h i,max_mul]
    exact max_le ((words i).2.trans (Nat.div_le_self ..)) ((words i).1.trans (Nat.div_le_self ..))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
