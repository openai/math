import OAI.Hierarchy.ProtocolRAMCalendarGlobalTests
import OAI.Hierarchy.ProtocolRAMCalendarBoot

namespace OAI
/-! # Placing all finite-mesh score tables in the original finite header -/

namespace Hierarchy.ProtocolRAM.Calendar.GlobalTests
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open scoped Fin.CommRing
noncomputable section
variable {z d N k q w jobs : ℕ}

def length (l : Layout) (z N k : ℕ) := rows z N k+2*span l N k
def page (l : Layout) (z N k pageIndex : ℕ) : Layout :=
  {l with base:=l.base+pageIndex*length l z N k}

theorem page_stop (l : Layout) (z N k i : ℕ) :
    stop (page l z N k i) z N k=l.base+(i+1)*length l z N k := by
  simp only [stop,page,span,length,Nat.succ_mul]
  omega

theorem disjoint (l : Layout) (z N k q : ℕ) :
    ProtocolRAMStaticSlabs.Disjoint (fun i : Fin q=>(page l z N k i.val).base)
      (fun i=>stop (page l z N k i.val) z N k) := by
  apply ProtocolRAMStaticSlabs.disjoint_of_order
  intro i j ij
  rw [page_stop]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ij) _

def allPages (l : Layout) (z N k : ℕ) (phase : Fin q→PhasePrice) (m : Memory w) : Memory w :=
  ProtocolRAMStaticSlabs.mounted (fun i : Fin q=>(page l z N k i.val).base)
    (fun i=>stop (page l z N k i.val) z N k)
    (fun i=>mount (page l z N k i.val) z N k (phase i) m) m

theorem all_resident (l : Layout) (z N k : ℕ) (phase : Fin q→PhasePrice) (m : Memory w) (i : Fin q) :
    Resident (page l z N k i.val) z N k (phase i) (allPages l z N k phase m) := by
  apply (resident _ z N k (phase i) m).transport
  intro a lo hi
  exact ProtocolRAMStaticSlabs.cell_on _ _ (disjoint l z N k q) ⟨lo,hi⟩

theorem all_frame (l : Layout) (z N k : ℕ) (phase : Fin q→PhasePrice) (m : Memory w) (a : ℕ)
    (outside : a<l.base ∨ l.base+q*length l z N k≤a) : allPages l z N k phase m a=m a := by
  apply ProtocolRAMStaticSlabs.outside
  intro i inside
  obtain ⟨lo,hi⟩ := inside
  change l.base+i.val*length l z N k≤a at lo
  change a < stop (page l z N k i.val) z N k at hi
  rw [page_stop] at hi
  have upto : (i.val+1)*length l z N k ≤ q*length l z N k := Nat.mul_le_mul_right _ i.isLt
  rcases outside with low | high
  · exact (Nat.not_lt_of_ge ((Nat.le_add_right _ _).trans lo)) low
  · exact (Nat.not_lt_of_ge high) (hi.trans_le (Nat.add_le_add_left upto _))

/-- The complete finite collection costs at most a constant number of
words per site once the stock lookup range fits the data extent. -/
theorem pages_linear (l : Layout) (z N k q : ℕ) (stride : l.stride≤2^z) :
    q*length l z N k≤2^z*(3*q*kinds N k) := by
  have t := Nat.mul_le_mul_left (kinds N k) stride
  unfold length span
  rw [rowCount]
  calc
    _ ≤ q*(kinds N k*2^z+2*(kinds N k*2^z)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2 t) _)
    _ = _ := by ring

/-- A single height-linear mask accommodates all stock and score columns; its
bounded-lookup span is itself only a fixed multiple of the number of data sites. -/
def bits (z N k : ℕ) := z+kinds N k

theorem mask_room (z N k : ℕ) :
    rows z N k≤2^(bits z N k) ∧ 2^(bits z N k)=2^z*2^(kinds N k) := by
  rw [bits,pow_add,rowCount]
  constructor
  · rw [Nat.mul_comm (kinds N k)]
    exact Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n:=kinds N k)).le
  · rfl

theorem mask_values (l : Layout) (z N k : ℕ) (stride : l.stride≤2^z) :
    span l N k≤2^(bits z N k) :=
  (Nat.mul_le_mul_left (kinds N k) stride).trans (mask_room z N k).1

/-- Put the public score pages above the CT heap and below the first sampler page.
All later row scans read the very words originally supplied at boot. -/
theorem from_boot (l : Layout) (v : Fin jobs→Market z d k) (π : Equiv.Perm (Fin (2^z)))
    (phase : Fin q→PhasePrice) (m mid : Boot.Tape z d)
    (started : Boot.Receipt v π (allPages l z N k phase m) mid)
    (left : heapEnd z d copies≤l.base)
    (right : ∀j,l.base+q*length l z N k≤Boot.low (v j)) (i : Fin q) :
    Resident (page l z N k i.val) z N k (phase i) mid := by
  apply (all_resident l z N k phase m i).transport
  intro a lo hi
  apply started.kept
  · exact left.trans ((Nat.le_add_right _ _).trans lo)
  · intro j hit
    have upper : (i.val+1)*length l z N k≤q*length l z N k :=
      Nat.mul_le_mul_right _ i.isLt
    rw [page_stop] at hi
    exact Nat.not_lt_of_ge hit.1 (hi.trans_le ((Nat.add_le_add_left upper _).trans (right j)))

/-- The boot receipt is over the finite RAMMemory header. Thus the proof
uses a pointwise read below the header cutoff, even when its tail or the private
inputs surrounding these pages are nonzero before truncation. -/
theorem from_initial (l : Layout) (v : Fin jobs→Market z d k) (π : Equiv.Perm (Fin (2^z)))
    (phase : Fin q→PhasePrice) (m mid : Boot.Tape z d) (size : ℕ)
    (started : Boot.Receipt v π (Computability.VPVNP.RAMMemory.initialMemory size (allPages l z N k phase m)) mid)
    (left : heapEnd z d copies≤l.base) (fits : l.base+q*length l z N k≤ size)
    (right : ∀j,l.base+q*length l z N k≤Boot.low (v j)) (i : Fin q) :
    Resident (page l z N k i.val) z N k (phase i) mid := by
  apply (all_resident l z N k phase m i).transport
  intro a lo hi
  have reach : a<l.base+q*length l z N k := by
    rw [page_stop] at hi
    exact hi.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _)
  have raw := started.kept a (left.trans ((Nat.le_add_right _ _).trans lo))
    (fun j hit=>Nat.not_lt_of_ge hit.1 (reach.trans_le (right j)))
  simpa only [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (reach.trans_le fits)] using raw

end
end Hierarchy.ProtocolRAM.Calendar.GlobalTests

end OAI
