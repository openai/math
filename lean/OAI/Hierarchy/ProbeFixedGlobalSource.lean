import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProbeFixedAcquisitionScale
import OAI.Hierarchy.ProbeFixedStockCap
import OAI.Hierarchy.ProtocolRAMCalendarGlobalCalibration
import OAI.Hierarchy.ProtocolRAMCalendarGlobalRoom

namespace OAI
/-! # The two rounded global score arrays in the memory of a real outer trial -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "G" => v.privateArena P z width
local notation "freq" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "layout" => JointHeader.scores P.joint z N k
variable (phase trial : ℕ)
local notation "u" => Attempt.outer phase trial
local notation "pg" => DeadlineROM.scorePage v.mesh layout z N k u
local notation "stock" => (f u).stockSource.old
local notation "s" => outerTime v.mesh v.finish phase

theorem global_input_test :
    let B:=repair C u
    let baseline:=envelope v.W ((dyadicScale v.W)^8) s
    B.tests.excess=GlobalTests.check pg z N k false B.tests.excess.out (GlobalTests.bound pg z baseline) stock ∧
    B.tests.payload=GlobalTests.check pg z N k true B.tests.payload.out (GlobalTests.bound pg z 1) stock :=
  ⟨rfl,rfl⟩

theorem global_page_floor :
    GlobalTests.stop pg z N k≤(G).base v.mesh (.attempt u) :=
  (Nat.le_add_right ..).trans (v.election_public P z width u).2.1

theorem global_input_floor :
    (stock).base+GlobalTests.rows z N k≤(G).base v.mesh (.attempt u) := by
  have h:=(v.stock_source_lows P z width u).1
  rw [v.stock_goods P z width u] at h
  exact h

variable (mem : Memory (wordBits z (2^v.W) copies))
local notation "entry" => trialState C mem phase trial
local notation "source" => prepared C u entry
local notation "x" => (A).trial C mem phase trial

theorem global_source (hp : phase<v.mesh.inject+v.mesh.cool) (ht : trial<v.mesh.outerFuel)
    (all : Calendar.mounted C (events (C).mesh) mem) («public» : (H).Resident mem)
    (prices : InitialPrices P.joint z N k freq (fun _=>0) mem)
    (precision : P.joint.precision=v.precision)
    (digits : GlobalTests.kinds N k≤z) (stride : (layout).stride≤2^z)
    (valueRoom : GlobalTests.unitBound layout N k (v.basePhase width)<2^W)
    (capacity : ∀i,(x).bits i<(layout).stride) :
    GlobalTests.ReadStock A x pg stock
      (GlobalTests.price A s (probeBonus v.W) (routeCap N v.radius) (pg).precision) source := by
  obtain ⟨tail,current⟩:=outer_slot C mem phase trial hp ht all
  let root:=(G).base v.mesh (.attempt u)
  let price:=GlobalTests.price A s (probeBonus v.W) (routeCap N v.radius) (pg).precision
  let E:=PurchaseInventory.slotEquiv z N k
  have pages:=(v.guard_pages_at_slot P z width r banks src tab dst owners u _ tail mem entry current «public» _ prices).2
  have schedule : freq (DeadlineROM.index v.mesh u)=price := by
    rw [DeadlineROM.outer_price _ _ _ _ _ hp.le]
    have hn : N=publicStages v.W := fixed_stage_count z v.W
    change {v.basePhase width with time:=s}=
      ⟨v.a,v.radius,s,fun j=>if j=0 then 0 else probeBonus v.W,routeCap N v.radius,width,P.joint.precision⟩
    rw [hn,precision]
    rfl
  rw [schedule] at pages
  have staying (y : ℕ) (hy : y<root) : source y=entry y :=
    prepared_prior C u entry y current.currentReady
      (v.event_prefix P z width r banks src tab dst owners (.attempt u) y hy).1
  have mountedPage : GlobalTests.Resident pg z N k price source := by
    apply pages.transport
    intro y _ h
    have early:=h.trans_le (v.global_page_floor P z width phase trial)
    exact (staying _ early).trans (v.row_buffer_frame P z width r banks src tab dst owners
      u entry current.currentReady y early).1.symm
  have actual (i : Fin (GlobalTests.rows z N k)) : (source ((stock).base+i.val)).val=(x).bits (E.symm i) := by
    have early:=(Nat.add_lt_add_left i.isLt (stock).base).trans_le (v.global_input_floor P z width phase trial)
    rw [staying _ early]
    change (entry ((stock).base+i.val)).val=(entry ((A).stockAt u (E.symm i))).val
    have pointer : (A).stockAt u (E.symm i)=(stock).base+PurchaseInventory.slot (E.symm i) :=
      v.stock_pointer P z width (v.issued P z width r banks src tab dst owners) u (E.symm i)
    have hi : PurchaseInventory.slot (E.symm i)=i.val := congrArg Fin.val (E.apply_symm_apply i)
    rw [hi] at pointer
    exact congrArg (fun address : ℕ => (entry address).val) pointer.symm
  have order : GlobalTests.rows z N k<2^W := by
    rw [GlobalTests.rowCount,Nat.mul_comm]
    exact GlobalTests.linear_room z (2^v.W) _ digits
  have bounded:=GlobalTests.mask_values layout z N k stride
  have spanWord : GlobalTests.span pg N k<2^W := by
    exact (Nat.mul_le_mul_left (GlobalTests.kinds N k) stride).trans_lt order
  have fixed : N=publicStages v.W := fixed_stage_count z v.W
  have hot : 0<s := (show 0<(v.finish:ℝ) by exact_mod_cast v.clock.finish_pos).trans_le (v.real_times hp.le).1
  have aPos : 0<price.a := by
    change 0<(v.a:ℝ)
    exact_mod_cast v.quadratic_pos
  have sameUpper (i : Fin (GlobalTests.kinds N k)) :
      GlobalTests.upper price i.val=GlobalTests.upper (v.basePhase width) i.val := by
    change routeCap N v.radius i.val+((v.a:ℝ)+(if i.val=0 then 0 else probeBonus v.W))*
      (routeCap N v.radius i.val)^2=_
    simp only [basePhase,publicPhase,GlobalTests.upper,routeCap,probeBonus,fixed]
  have sameSum : GlobalTests.unitBound pg N k price=GlobalTests.unitBound layout N k (v.basePhase width) := by
    unfold GlobalTests.unitBound
    apply Finset.sum_congr rfl
    intro i _
    rw [sameUpper i]
    rfl
  have sumRoom := sameSum.trans_lt valueRoom
  refine ⟨mountedPage,order,(GlobalTests.mask_room z N k).1,?_,spanWord,bounded,?_,?_,actual⟩
  · rw [v.stock_old_size P z width u]
    exact (ProtocolRAMPurchaseSampler.lt_span _).le
  · intro i
    rw [actual i]
    change (x).bits (E.symm i)<(layout).stride
    exact capacity (E.symm i)
  · intro pay i
    refine (GlobalTests.valueWord_le pg price pay (GlobalTests.kind i) _ aPos ?_ (Nat.cast_nonneg _) hot ?_).trans_lt sumRoom
    · change 0≤ if (GlobalTests.kind i).val=0 then 0 else probeBonus v.W
      split <;> simp [probeBonus]; positivity
    · change 0≤routeCap N v.radius (GlobalTests.kind i).val
      unfold routeCap
      split <;> positivity

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
