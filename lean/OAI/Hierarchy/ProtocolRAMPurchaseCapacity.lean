import OAI.Hierarchy.ProtocolRAMPurchaseClock
import OAI.Hierarchy.ProtocolRAMPurchaseInventory

namespace OAI
/-! # A uniformly fitting physical allocation for all true CT stage purchases -/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open Filter
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

def config (k extra depth : ℕ) (t : StageAt z d) : PassConfig k :=
  let base := heapEnd z d copies
  let table : Bank := ⟨base+PurchaseInventory.footprint z (2*rounds d+1) k,z+extra⟩
  ⟨table.base+table.size,depth,0,table,PurchaseInventory.bank base z (stageNumber t)⟩

def initialFactor (d k extra : ℕ) := 1+(2*rounds d+1)*(2*k)+2^extra

theorem config_start (k extra depth : ℕ) (t : StageAt z d) :
    (config k extra depth t).start=heapEnd z d copies+initialFactor d k extra*2^z := by
  simp only [config,Bank.size,initialFactor,PurchaseInventory.footprint,pow_add]
  ring

theorem stock_end (base h : ℕ) {stages : ℕ} (stage : Fin stages) (j : Fin (2*k)) :
    (PurchaseInventory.bank base h stage j).base+(PurchaseInventory.bank base h stage j).size≤
      base+PurchaseInventory.footprint h stages k := by
  have stageLimit := Nat.mul_le_mul_right (2*k) stage.isLt
  rw [Nat.succ_mul] at stageLimit
  have digit := j.isLt
  have lanes : 1+stage.val*(2*k)+j.val+1 ≤ 1+stages*(2*k) := by omega
  have words := Nat.mul_le_mul_right (2^h) lanes
  rw [Nat.succ_mul] at words
  change base+(1+stage.val*(2*k)+j.val)*2^h+2^h≤base+((1+stages*(2*k))*2^h)
  omega

/-- One sufficiently large record height works simultaneously for every template
stage. The public stock-price table holds `2^extra * 2^z` possible stock counts. -/
theorem eventually_ready (d k extra depth : ℕ) (hd : 1≤d) (S : PurchaseSampler) :
    ∀ᶠ z : ℕ in atTop, ∀ t : StageAt z d, Ready S t (config k extra depth t) := by
  let K := 4^(rounds d+1)
  let factor := Layout.linearFactor K S.degree depth
  let C := initialFactor d k extra+factor+K
  filter_upwards [eventually_append_room d copies C,eventually_ge_atTop (max S.degree (2*k))] with z large hdim
  intro t
  let c := config k extra depth t
  let L := geom S t c
  let sh := stageAt z d t
  change Ready S t c
  simp only [C,Nat.add_mul] at large
  have npos : 0<2^z := Nat.two_pow_pos z
  let : Nonempty sh.Group := ⟨(advisedStage z d (Equiv.refl _) t).group 0⟩
  have groups : 0<Fintype.card sh.Group := Fintype.card_pos
  have mass := template_dyadic hd sh (List.get_mem ..)
  have sockets : 0<sh.span := (Nat.two_pow_pos _).trans_le mass.span_lower
  have area : Fintype.card sh.Group*sh.span≤K*2^z := mass.2
  have full := L.end_linear K npos groups sockets rfl area
  have initial := config_start k extra depth t
  have total : L.endAddress<2^(wordBits z d copies) := by
    change L.endAddress ≤ c.start+factor*2^z at full
    change c.start=heapEnd z d copies+initialFactor d k extra*2^z at initial
    omega
  have early : c.start≤L.endAddress := by
    change L.start≤L.endAddress
    obtain ⟨start,ids,mark,owner,scatter,source,gates,tape,limit⟩ := L.regions
    omega
  have cap := early.trans_lt total
  have «prefix» : c.threshold.base+c.threshold.size=c.start := rfl
  have heap : heapEnd z d copies ≤ c.threshold.base := Nat.le_add_right ..
  have rowsRoom : 2^z<2^wordBits z d copies := (height_extent z d).trans_lt (extent_word ..)
  have wide : 0<wordBits z d copies := by rw [wordBits_linear]; omega
  have banksBound (f : Fin 3) : (stageBank z d (stageNumber t) f).Fits (wordBits z d copies) c.start :=
    ⟨Nat.two_pow_pos _,by simpa [Bank.size,stageBank_bits] using rowsRoom,
      (stageBank_end z d (stageNumber t) f).trans (by omega)⟩
  have raw : 2^z ≤ c.threshold.base := by
    have count : 0 < 1+(2*rounds d+1)*(2*k) := by omega
    have b := Nat.mul_le_mul_right (2^z) count
    change 2^z ≤ heapEnd z d copies+(1+(2*rounds d+1)*(2*k))*2^z
    simpa only [Nat.one_mul] using b.trans (Nat.le_add_left ..)
  have byWord : max S.degree (2*k)<2^wordBits z d copies :=
    ((hdim.trans_lt Nat.lt_two_pow_self)).trans rowsRoom
  have shRoom : sh.span≤2^wordBits z d copies := by
    have le := Nat.mul_le_mul_right sh.span groups
    simp only [Nat.one_mul] at le
    omega
  have tableSize : c.threshold.size<2^wordBits z d copies := calc
    c.threshold.size ≤ c.threshold.base+c.threshold.size := Nat.le_add_left ..
    _ = c.start := «prefix»
    _ < 2^wordBits z d copies := cap
  refine ⟨heap,raw,?_,⟨Nat.two_pow_pos _,tableSize,«prefix».le⟩,⟨banksBound 0,banksBound 1,banksBound 2⟩,
    wide,(le_max_right ..).trans_lt byWord,((le_max_left ..).trans_lt byWord).le,shRoom,total⟩
  intro j
  exact ⟨Nat.le_add_right ..,Nat.two_pow_pos _,rowsRoom,stock_end _ _ (stageNumber t) j⟩

/-- Executable CT-and-purchase for every sufficiently large height, including
all word bounds, true stage fields, and the uniform fixed-parameter tick bound. -/
theorem eventual_run (d k extra depth : ℕ) (hd : 1≤d) (S : PurchaseSampler) :
    ∀ᶠ z : ℕ in atTop, ∀ (t : StageAt z d) (j : Fin (2*k)) (phase : PhasePrice) (T : ℝ)
      (kind : ℕ) (π : Equiv.Perm (Fin (2^z))) (raw : Memory (wordBits z d copies)),
      (∀ i : Fin (2^z),raw i.val=((π i).val:Word _)) →
      let c := config k extra depth t
      let L := PurchaseStage.layout (embedded S t c) (sign S t c) (2^z) depth
      let left := PurchaseMarks.stratum (n:=2^z) phase T kind c.threshold c.stock raw j
      ∃ out, (program S t c j).Exec (initial S t c phase T kind raw) out (costEnvelope d S.degree depth k 1*2^z) ∧
        (PurchaseStage.flags L out).count true=(advisedPurchases S π t depth left).1.length ∧
        ∀ r : Fin (2^z),out (L.work+4+r.val)=MarkTape.encode (wordBits z d copies)
          (decide (r∈(advisedPurchases S π t depth left).2)) := by
  filter_upwards [eventually_ready d k extra depth hd S] with z ready
  intro t j phase T kind π raw read
  let c := config k extra depth t
  obtain ⟨out,act,count,remaining⟩ := run S t c j phase T kind π raw read hd (ready t)
  exact ⟨out,ThreeFlat.RAM.PhysicalProcedure.Procedure.Spec.mono act
    (fun _ h=>h) (fun _ _ h=>h) (clock_linear S t c hd rfl),count,remaining⟩

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
