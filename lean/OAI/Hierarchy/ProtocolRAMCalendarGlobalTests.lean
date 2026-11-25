import OAI.Hierarchy.ProtocolRAMNativeGlobalTests
import OAI.Hierarchy.ProtocolRAMStripTableTypes
import OAI.Hierarchy.ProtocolRAMCalendarScoreCut
import OAI.Hierarchy.ProtocolRAMRepairCommodity

namespace OAI
/-! # Native potential and payload sums over the physical inventory -/

namespace Hierarchy.ProtocolRAM.Calendar.GlobalTests
open Computability.VPVNP.BurstRAM PrivateRAM AttemptGate AdaptiveProbe
open ThreeFlat.RAM
open scoped Fin.CommRing Classical BigOperators
noncomputable section

variable {z N k w : ℕ}

def kind (i : Fin (rows z N k)) : Fin (kinds N k) :=
  ⟨PurchaseInventory.lane ((PurchaseInventory.slotEquiv z N k).symm i),PurchaseInventory.lane_lt _⟩

def value (s : PhasePrice) (payload : Bool) : ℕ→ℕ→ℝ :=
  if payload then payloadRow s (fun j=>decide (j=0)) else potentialRow s

/-- Public headers contain no information about the input permutation or its stock.
The first column is a lane offset, followed by two lookup tables, each shared across
all data rows. The numeric data height can change their addresses and word values. -/
def mount (l : Layout) (z N k : ℕ) (s : PhasePrice) (m : Memory w) : Memory w :=
  fillSegment l.base (rows z N k+2*span l N k) (fun a=>
    let i := a-l.base
    if i<rows z N k then ((i/(2^z))*l.stride:ℕ) else
      let v := i-rows z N k
      let p := decide (span l N k≤v)
      let j := v-(if p then span l N k else 0)
      (valueWord l.precision (value s p) (j/l.stride) (j%l.stride):Word w)) m

theorem frame (l : Layout) (z N k : ℕ) (s : PhasePrice) (m : Memory w) (a : ℕ)
    (ha : a<l.base ∨ stop l z N k≤a) : mount l z N k s m a=m a := by
  have away : ¬(l.base≤a ∧ a<l.base+(rows z N k+2*span l N k)) := by
    unfold stop at ha
    omega
  simp [mount,fillSegment,away]

theorem kind_eq (i : Fin (rows z N k)) : (kind i).val=i.val/(2^z) := by
  let c := (PurchaseInventory.slotEquiv z N k).symm i
  have hi : PurchaseInventory.slot c=i.val := by
    exact congrArg Fin.val ((PurchaseInventory.slotEquiv z N k).apply_symm_apply i)
  change PurchaseInventory.lane c=i.val/(2^z)
  rw [← hi,PurchaseInventory.slot,Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (PurchaseInventory.record c).isLt,
    Nat.zero_add]

structure Resident (l : Layout) (z N k : ℕ) (s : PhasePrice) (m : Memory w) : Prop where
  off : ∀ i : Fin (rows z N k), m (l.base+i.val)=((kind i).val*l.stride:ℕ)
  values : ∀ p (t : Fin (kinds N k)) (n : Fin l.stride),
    m ((table l z N k p).base+(t.val*l.stride+n.val))=(valueWord l.precision (value s p) t.val n.val:Word w)

private theorem index_lt (l : Layout) (t : Fin (kinds N k)) (n : Fin l.stride) :
    t.val*l.stride+n.val<span l N k := by
  have bound := Nat.mul_le_mul_right l.stride t.isLt
  rw [Nat.succ_mul] at bound
  unfold span
  omega

theorem resident (l : Layout) (z N k : ℕ) (s : PhasePrice) (m : Memory w) :
    Resident l z N k s (mount l z N k s m) := by
  constructor
  · intro i
    have inRange : l.base≤l.base+i.val ∧ l.base+i.val<l.base+(rows z N k+2*span l N k) := by
      have := i.isLt
      omega
    simp only [mount,fillSegment,ite_eq_left inRange,Nat.add_sub_cancel_left,ite_eq_left i.isLt,kind_eq]
  · intro p t n
    let j := t.val*l.stride+n.val
    have less : j<span l N k := index_lt l t n
    have q : j/l.stride=t.val := by
      have nz : 0<l.stride := Nat.zero_lt_of_lt n.isLt
      dsimp [j]
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ nz,Nat.div_eq_of_lt n.isLt,Nat.zero_add]
    have r : j%l.stride=n.val := Nat.mul_add_mod_of_lt n.isLt
    let shift := if p then span l N k else 0
    let off := rows z N k+(shift+j)
    have address : (table l z N k p).base+j=l.base+off := by
      simp only [table,off,shift,Nat.add_assoc]
    have fit : l.base≤l.base+off ∧ l.base+off<l.base+(rows z N k+2*span l N k) := by
      dsimp [off,shift]
      cases p <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
    have high : ¬off<rows z N k := by dsimp [off]; omega
    have rem : off-rows z N k=shift+j := Nat.add_sub_cancel_left ..
    have sel : decide (span l N k≤ shift+j)=p := by
      cases p <;> simp [shift,Nat.not_le_of_lt less]
    have last : shift+j-(if p then span l N k else 0)=j := Nat.add_sub_cancel_left ..
    change mount l z N k s m ((table l z N k p).base+j)=_
    rw [address]
    simp only [mount,fillSegment,ite_eq_left fit,Nat.add_sub_cancel_left,ite_eq_right high,rem,sel,last,q,r]

theorem Resident.transport {l : Layout} {s : PhasePrice} {m m' : Memory w}
    (R : Resident l z N k s m)
    (same : ∀a,l.base≤a→a<stop l z N k→m' a=m a) : Resident l z N k s m' := by
  constructor
  · intro i
    rw [same _ (by omega) (by unfold stop; have := i.isLt; omega)]
    exact R.off i
  · intro p t n
    have low := index_lt l t n
    rw [same _ (by cases p <;> simp [table] <;> omega)
      (by cases p <;> simp [table,stop] <;> omega)]
    exact R.values p t n

def words (l : Layout) (z N k : ℕ) (s : PhasePrice) (p : Bool) (out bound : ℕ)
    (stocks : Bank) (m : Memory w) (R : Resident l z N k s m)
    (rowRoom : rows z N k<2^w) (rowCap : rows z N k≤2^l.indexBits)
    (stockCap : rows z N k≤ stocks.size) (valueRoom : span l N k<2^w)
    (valueCap : span l N k≤2^l.indexBits)
    (limit : ∀i : Fin (rows z N k),(m (stocks.base+i.val)).val<l.stride)
    (width : ∀i : Fin (rows z N k),valueWord l.precision (value s p) (kind i).val
      (m (stocks.base+i.val)).val < 2^w) :
    ScoreWords (check l z N k p out bound stocks) m (value s p) l.precision where
  kinds := kinds N k
  stride := l.stride
  table := table l z N k p
  offsets := offsets l
  stocks := stocks
  kind := kind
  bits := fun i=>⟨(m (stocks.base+i.val)).val,limit i⟩
  code := rfl
  offset := fun i=>by
    simpa only [Bank.read,offsets,Bank.size,Fin.val_cast_of_lt (i.isLt.trans rowRoom),
      Nat.mod_eq_of_lt (i.isLt.trans_le rowCap)] using R.off i
  stock := fun i=>by
    simp only [Bank.read,Fin.val_cast_of_lt (i.isLt.trans rowRoom),Nat.mod_eq_of_lt (i.isLt.trans_le stockCap),
      Fin.cast_val_eq_self]
  rom := fun i=>by
    let n : Fin l.stride := ⟨(m (stocks.base+i.val)).val,limit i⟩
    have low := index_lt l (kind i) n
    change (table l z N k p).read m (((kind i).val*l.stride+n.val:ℕ):Word w)=_
    have fits : (kind i).val*l.stride+n.val<(table l z N k p).size := low.trans_le valueCap
    rw [Bank.read,Fin.val_cast_of_lt (low.trans valueRoom),Nat.mod_eq_of_lt fits]
    exact R.values p (kind i) n
  fits := width

theorem payload_lane (i : Fin (rows z N k)) :
    decide ((kind i).val=0)=
      (match (PurchaseInventory.slotEquiv z N k).symm i with | .inl _=>true | .inr _=>false) := by
  let c := (PurchaseInventory.slotEquiv z N k).symm i
  change decide (PurchaseInventory.lane c=0)=match c with | .inl _=>true | .inr _=>false
  cases c with
  | inl _ => rfl
  | inr c => rcases c with ⟨⟨i,t⟩,a⟩; simp [PurchaseInventory.lane]

end
end Hierarchy.ProtocolRAM.Calendar.GlobalTests

end OAI
