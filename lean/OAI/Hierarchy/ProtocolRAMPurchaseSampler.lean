import OAI.Hierarchy.ProtocolRAMPurchaseSuccessor
import OAI.Hierarchy.ProbeStageResident
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Fixed forward and reverse sampler directories

The first bank translates group IDs to socket offsets. Each sampler digit has
one bank of optional neighbors and one bank of reverse digits. All three
tables are functions of sampler geometry alone.
-/

namespace Hierarchy.ProtocolRAMPurchaseSampler
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w m D : ℕ}

def words (groups m D : ℕ) := span groups+(2*D)*span m

theorem words_bound (groups m D : ℕ) :
    words groups m D ≤ 2*(groups+1)+4*D*(m+1) := by
  have cap := Nat.mul_le_mul_left (2*D) (span_le m)
  calc
    _ ≤ 2*(groups+1)+(2*D)*(2*(m+1)) := Nat.add_le_add (span_le groups) cap
    _ = _ := by ring

theorem words_bound_pos {groups m : ℕ} (D : ℕ) (goodGroups : 0 < groups) (goodSockets : 0 < m) :
    words groups m D ≤ 4*groups+8*(D*m) := by
  have hi := Nat.mul_le_mul_left (4*D) (show m+1≤2*m by omega)
  calc
    _ ≤ 2*(groups+1)+4*D*(m+1) := words_bound ..
    _ ≤ 4*groups+(4*D)*(2*m) := Nat.add_le_add (by omega) hi
    _ = _ := by ring

def stride (base groups : ℕ) : Bank := ⟨base,bits groups⟩

def lane (base groups m l : ℕ) : Bank := ⟨base+span groups+l*span m,bits m⟩

def neighbor (base groups m : ℕ) (j : Fin D) := lane base groups m j.val

def backward (base groups m D : ℕ) (j : Fin D) := lane base groups m (D+j.val)

def sample (next : Fin m → List (Fin m)) (o : Fin m) (j : Fin D) := (next o)[j.val]?

def payload (next : Fin m → List (Fin m)) (back : Fin m → Fin D → Fin D) (l i : ℕ) : ℕ :=
  if ho : i < m then
    if hj : l < D then ProtocolRAMPurchaseOwners.portCode (sample next ⟨i,ho⟩ (⟨l,hj⟩ : Fin D))
    else if hj : l-D < D then (back ⟨i,ho⟩ ⟨l-D,hj⟩).val else 0
  else 0

/-- Public word at an offset from the first sampler bank. -/
def word (groups : ℕ) (next : Fin m → List (Fin m)) (back : Fin m → Fin D → Fin D)
    (offset : ℕ) : ℕ :=
  if offset<span groups then offset*m else
    payload next back ((offset-span groups)/span m) ((offset-span groups)%span m)

/-- The padded advice is an ordinary finite word list independent of external memory. -/
def advice (groups : ℕ) (next : Fin m → List (Fin m)) (back : Fin m → Fin D → Fin D) : List ℕ :=
  List.ofFn fun i : Fin (words groups m D) => word groups next back i.val

@[simp] theorem advice_length (groups : ℕ) (next : Fin m → List (Fin m)) (back : Fin m → Fin D → Fin D) :
    (advice groups next back).length=words groups m D := by simp [advice]

/-- Overlay the fixed finite advice segment onto arbitrary external memory. -/
def install (base groups : ℕ) (next : Fin m → List (Fin m)) (back : Fin m → Fin D → Fin D)
    (mem : Memory w) : Memory w :=
  fillSegment base (words groups m D) (fun a => (word groups next back (a-base):Word w)) mem

theorem frame (base groups : ℕ) (next : Fin m → List (Fin m)) (back : Fin m → Fin D → Fin D)
    (mem : Memory w) (a : ℕ) (away : a<base ∨ base+words groups m D≤a) :
    install base groups next back mem a=mem a := by
  simp [install,fillSegment,show ¬(base≤a ∧ a<base+words groups m D) by omega]

private theorem read_offset (base groups : ℕ) (next : Fin m → List (Fin m))
    (back : Fin m → Fin D → Fin D) (mem : Memory w) (q : ℕ) (hq : q<words groups m D) :
    install base groups next back mem (base+q)=(word groups next back q:Word w) := by
  have live : base≤base+q ∧ base+q<base+words groups m D := by omega
  simp [install,fillSegment,live]

theorem install_advice (base groups : ℕ) (next : Fin m → List (Fin m))
    (back : Fin m → Fin D → Fin D) (mem : Memory w) (q : Fin (words groups m D)) :
    install base groups next back mem (base+q.val) =
      (((advice groups next back)[q.val]'(by simp) : ℕ) : Word w) := by
  simpa [advice] using read_offset base groups next back mem q.val q.isLt

theorem stride_resident (base groups : ℕ) (next : Fin m → List (Fin m))
    (back : Fin m → Fin D → Fin D) (mem : Memory w) (room : groups≤2^w) :
    Native.Resident (stride base groups) (install base groups next back mem)
      (fun g : Fin groups => g.val*m) := by
  apply Native.Resident.of_cells _ _ _ (lt_span groups).le room
  intro g
  have lg := g.isLt.trans (lt_span groups)
  exact (read_offset base groups next back mem g.val (lt_of_lt_of_le lg (Nat.le_add_right ..))).trans
    (by simp [word,lg])

private theorem lane_end {m D l : ℕ} (hl : l<2*D) : l*span m+span m ≤ (2*D)*span m := by
  simpa only [Nat.succ_mul] using Nat.mul_le_mul_right (span m) hl

private theorem lane_resident (base groups : ℕ) (next : Fin m → List (Fin m))
    (back : Fin m → Fin D → Fin D) (mem : Memory w) (room : m≤2^w) (l : ℕ) (hl : l<2*D) :
    Native.Resident (lane base groups m l) (install base groups next back mem)
      (fun o : Fin m => payload next back l o.val) := by
  apply Native.Resident.of_cells _ _ _ (lt_span m).le room
  intro o
  let q := span groups+(l*span m+o.val)
  have small := o.isLt.trans (lt_span m)
  have last := lane_end (m:=m) hl
  have hq : q<words groups m D := by dsimp [q,words]; omega
  change install base groups next back mem (base+span groups+l*span m+o.val)=_
  rw [show base+span groups+l*span m+o.val=base+q by dsimp [q]; omega,
    read_offset base groups next back mem q hq]
  have div : (l*span m+o.val)/span m=l := by
    rw [Nat.mul_comm l, Nat.mul_add_div (show 0 < span m from Nat.two_pow_pos _), Nat.div_eq_of_lt small, Nat.add_zero]
  simp [q,word,div,Nat.mod_eq_of_lt small]

theorem neighbor_resident (base groups : ℕ) (next : Fin m → List (Fin m))
    (back : Fin m → Fin D → Fin D) (mem : Memory w) (room : m≤2^w) (j : Fin D) :
    Native.Resident (neighbor base groups m j) (install base groups next back mem)
      (fun o => ProtocolRAMPurchaseOwners.portCode (sample next o j)) := by
  intro o
  have read := lane_resident base groups next back mem room j.val (by have := j.isLt; omega) o
  simpa [neighbor,payload,o.isLt,j.isLt] using read

theorem reverse_resident (base groups : ℕ) (next : Fin m → List (Fin m))
    (back : Fin m → Fin D → Fin D) (mem : Memory w) (room : m≤2^w) (j : Fin D) :
    Native.Resident (backward base groups m D j) (install base groups next back mem)
      (fun o => (back o j).val) := by
  intro o
  have read := lane_resident base groups next back mem room (D+j.val) (by have := j.isLt; omega) o
  simpa [backward,payload,o.isLt,j.isLt] using read

theorem stride_fits (base groups m D : ℕ) (room : base+words groups m D<2^w) :
    (stride base groups).Fits w (base+words groups m D) := by
  change 0<span groups ∧ span groups<2^w ∧ base+span groups≤base+words groups m D
  have := lt_span groups
  dsimp [words] at room ⊢
  omega

theorem lane_fits (base groups : ℕ) (l : Fin (2*D)) (room : base+words groups m D<2^w) :
    (lane base groups m l.val).Fits w (base+words groups m D) := by
  change 0<span m ∧ span m<2^w ∧ base+span groups+l.val*span m+span m≤base+words groups m D
  have := lt_span m
  have := lane_end (m:=m) l.isLt
  dsimp [words] at room ⊢
  omega

theorem neighbor_fits (base groups : ℕ) (j : Fin D) (room : base+words groups m D<2^w) :
    (neighbor base groups m j).Fits w (base+words groups m D) :=
  lane_fits base groups ⟨j.val,by have := j.isLt; omega⟩ room

theorem backward_fits (base groups : ℕ) (j : Fin D) (room : base+words groups m D<2^w) :
    (backward base groups m D j).Fits w (base+words groups m D) :=
  lane_fits base groups ⟨D+j.val,by have := j.isLt; omega⟩ room


end Hierarchy.ProtocolRAMPurchaseSampler

end OAI
