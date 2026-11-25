import OAI.Hierarchy.ProtocolRAMPurchaseCapacity
import OAI.Hierarchy.ProtocolRAMCalendarBootFrame

namespace OAI
/-! # Addresses for the calendar's failure, price and sampler words -/

namespace Hierarchy.ProtocolRAM.Calendar.Boot
open ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT Filter
open scoped Classical BigOperators
noncomputable section
variable {z d k jobs : ℕ}

/-- A job opens with its failed-row band, then its public threshold table, then
its sampler scratch and flags. All stages address the same inventory. -/
def place (spec : Market z d k) (stock base : ℕ) : Market z d k :=
  let floor := base+spec.failures.rows
  {spec with
    shelf := ⟨stock,floor,floor+2^spec.shelf.tableBits,spec.shelf.tableBits⟩
    failures := {spec.failures with base:=base}}

/-- The last flag belongs to this span, as do all true sampler cells and failure outputs. -/
def span (s : Market z d k) :=
  s.failures.rows+2^s.shelf.tableBits+count z d k*blockSize z d s.sampler.degree s.depth+
    2*(paths z s.sampler.degree s.depth+1)+count z d k*paths z s.sampler.degree s.depth

theorem last (s : Market z d k) (stock base : ℕ) :
    high (place s stock base)+(place s stock base).rows=base+span s := by
  simp [high,place,Market.flags,Market.rows,Shelf.flagsBase,span,Nat.add_assoc]

def placed (spec : Fin jobs→Market z d k) (stock : ℕ) (arena : Arena) (i : Fin jobs) :=
  place (spec i) stock (arena.first+i.val*arena.stride)

/-- A deterministic stride shared by the controller and the initial header. -/
def arena (spec : Fin jobs→Market z d k) (first tail : ℕ) : Arena :=
  ⟨first,Finset.univ.sup (fun i=>span (spec i))+tail⟩

theorem slot_le (spec : Fin jobs→Market z d k) (first tail : ℕ) (i : Fin jobs) :
    span (spec i)≤(arena spec first tail).stride :=
  (Finset.le_sup (f:=fun i=>span (spec i)) (Finset.mem_univ i)).trans (Nat.le_add_right ..)

theorem placed_layout (spec : Fin jobs→Market z d k) (stock first tail : ℕ)
    (heap : heapEnd z d copies≤first) :
    let a := arena spec first tail
    Layout (placed spec stock a) (first+jobs*a.stride) := by
  let a := arena spec first tail
  apply Layout.of_strides _ a heap le_rfl
  · intro i
    exact Nat.le_add_right ..
  · intro i
    have h := (last (spec i) stock (first+i.val*a.stride)).le
    have slot := slot_le spec first tail i
    change span (spec i)≤a.stride at slot
    change high (place (spec i) stock (first+i.val*a.stride))≤first+(i.val+1)*a.stride
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · intro i
    exact le_rfl

theorem failure_free (s : Market z d k) {stock base : ℕ} (afterCT : heapEnd z d copies≤base)
    (x : ℕ) (read : reads (place s stock base) x) :
    apart x (place s stock base).failures.base (place s stock base).failures.rows := by
  rcases read with lowAt|inJob
  · exact Or.inl (lowAt.trans_le afterCT)
  · exact Or.inr inJob.1

theorem inventory_end (s : Market z d k) (stock base : ℕ)
    (reserve : stock+PurchaseInventory.footprint z (2*rounds d+1) k≤base)
    (t : StageAt z d) (j : Fin (2*k)) :
    ((place s stock base).shelf.stock t j).base+((place s stock base).shelf.stock t j).size≤
      (place s stock base).shelf.firstBase :=
  (stock_end stock z (stageNumber t) j).trans
    (reserve.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))

/-- The word actually read at each placed commodity row after subdivision is the
integer stock encoded in the input bank, including repeated accesses at different jobs. -/
theorem inventory_read (spec : Fin jobs→Market z d k) (stock : ℕ) (a : Arena)
    {π : Equiv.Perm (Fin (2^z))} {raw mid : Tape z d}
    (receipt : Receipt (placed spec stock a) π raw mid) (heap : heapEnd z d copies≤ stock)
    (reserve : stock+PurchaseInventory.footprint z (2*rounds d+1) k≤a.first)
    (t : StageAt z d) (j : Fin (2*k)) (r : Computability.VPVNP.BurstRAM.Word (wordBits z d copies)) :
    (PurchaseInventory.bank stock z (stageNumber t) j).read mid r=
      (PurchaseInventory.bank stock z (stageNumber t) j).read raw r := by
  apply receipt.initial_stock _ r (heap.trans (Nat.le_add_right ..))
  intro i
  exact (stock_end stock z (stageNumber t) j).trans
    (reserve.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))

/-- All stage read and scratch addresses come from the physical layout and the final
extent of this slot. These are the numerical `Ready` fields used by the signed sweep. -/
theorem placed_dimensions (s : Market z d k) (stock base : ℕ) (hd : 1≤d)
    (inventory : heapEnd z d copies≤ stock)
    (reserve : stock+PurchaseInventory.footprint z (2*rounds d+1) k≤base)
    (capacity : base+span s<2^wordBits z d copies)
    (wide : 0<wordBits z d copies) (directions : 2*k<2^wordBits z d copies)
    (degree : s.sampler.degree≤2^wordBits z d copies)
    (sockets : ∀t : StageAt z d,(stageAt z d t).span≤2^wordBits z d copies) (i : Key z d k) :
    Ready s.sampler (stage i) ((place s stock base).shelf.cfg s.sampler s.depth i) := by
  let v := place s stock base
  have stockBase : stock≤base := (Nat.le_add_right ..).trans reserve
  have heap : heapEnd z d copies≤v.shelf.thresholdBase :=
    (inventory.trans stockBase).trans (Nat.le_add_right ..)
  have rows : 2^z≤heapEnd z d copies := by
    have small : 2^z≤extent z d := Nat.pow_le_pow_right (by decide) (by unfold roomBits; omega)
    have head := phase_in_heap (h:=z) (d:=d) (copies:=copies) (Nat.zero_le (rounds d))
    simp only [ProbeStage.Native.phase,Nat.zero_mul,Nat.add_zero] at head
    omega
  have headAt : v.shelf.thresholdBase+v.shelf.table.size=v.shelf.firstBase := rfl
  have firstEnd : v.shelf.firstBase≤base+span s := by
    change base+s.failures.rows+2^s.shelf.tableBits≤base+span s
    unfold span
    omega
  have headRoom : v.shelf.firstBase<2^wordBits z d copies := firstEnd.trans_lt capacity
  have rowsRoom : 2^z<2^wordBits z d copies := by omega
  have banksBound (c : Fin 3) :
      (stageBank z d (stageNumber (stage i)) c).Fits (wordBits z d copies) v.shelf.firstBase := by
    have ends := stageBank_end z d (stageNumber (stage i)) c
    have length : (stageBank z d (stageNumber (stage i)) c).size=2^z := by
      simp only [Bank.size,stageBank_bits]
    exact ⟨Nat.two_pow_pos _,length.trans_lt rowsRoom,ends.trans (by omega)⟩
  refine v.shelf.ready s.sampler s.depth i hd heap (rows.trans heap) ?_ ?_
    ⟨banksBound 0,banksBound 1,banksBound 2⟩ wide directions degree (sockets (stage i)) ?_
  · intro j
    exact ⟨inventory.trans (Nat.le_add_right ..),Nat.two_pow_pos _,rowsRoom,
      (stock_end stock z (stageNumber (stage i)) j).trans (reserve.trans (Nat.le_add_right ..))⟩
  · exact ⟨Nat.two_pow_pos _,by omega,headAt.le⟩
  · exact (last s stock base).trans_lt capacity

/-- With fixed mesh and sampler parameters the entire allocated region has linear
size in the number of permutation records. -/
theorem span_linear (s : Market z d k) (extra failFactor : ℕ)
    (tableBits : s.shelf.tableBits=z+extra) (errors : s.failures.rows≤failFactor*2^z) :
    span s ≤
      (failFactor + 2^extra + (2*rounds d+1)*(2*k)*factor d s.sampler.degree s.depth +
        2*(s.sampler.degree^s.depth+1) + (2*rounds d+1)*(2*k)*s.sampler.degree^s.depth)*2^z := by
  unfold span PurchaseFrozen.blockSize PurchaseFrozen.paths
  rw [count_eq,tableBits,pow_add]
  have positive := Nat.two_pow_pos z
  calc
    _ ≤ failFactor*2^z+2^z*2^extra+(2*rounds d+1)*(2*k)*(factor d s.sampler.degree s.depth*2^z)+
        2*(2^z*s.sampler.degree^s.depth+2^z)+(2*rounds d+1)*(2*k)*(2^z*s.sampler.degree^s.depth) := by
          gcongr; omega
    _ = _ := by ring

theorem arena_end_le (spec : Fin jobs→Market z d k) (first tail F T C : ℕ)
    (origin : first≤heapEnd z d copies+F*2^z) (spare : tail≤T*2^z)
    (slots : ∀i,span (spec i)≤C*2^z) :
    first+jobs*(arena spec first tail).stride≤heapEnd z d copies+(F+jobs*(C+T))*2^z := by
  have maximum : Finset.univ.sup (fun i=>span (spec i))≤C*2^z :=
    Finset.sup_le (fun i _=>slots i)
  have block : (arena spec first tail).stride≤(C+T)*2^z := by
    rw [Nat.add_mul]
    exact Nat.add_le_add maximum spare
  calc
    _ ≤ (heapEnd z d copies+F*2^z)+jobs*((C+T)*2^z) := Nat.add_le_add origin (Nat.mul_le_mul_left _ block)
    _ = _ := by ring

/-- The full initialized header and every later job fit at the authenticated CT
word width for sufficiently large heights, for any fixed mesh and linear slot bounds. -/
theorem eventual_arena_room (d k jobs F T C : ℕ) : ∀ᶠ z : ℕ in atTop,
    ∀ (spec : Fin jobs→Market z d k) (first tail : ℕ),
    first≤heapEnd z d copies+F*2^z → tail≤T*2^z →
    (∀i,span (spec i)≤C*2^z) →
    first+jobs*(arena spec first tail).stride<2^wordBits z d copies := by
  filter_upwards [eventually_append_room d copies (F+jobs*(C+T))] with z valid
  intro spec first tail origin spare slots
  exact (arena_end_le spec first tail F T C origin spare slots).trans_lt valid

end
end Hierarchy.ProtocolRAM.Calendar.Boot

end OAI
