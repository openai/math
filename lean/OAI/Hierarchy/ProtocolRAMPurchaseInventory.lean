import OAI.Hierarchy.ProtocolRAMPurchaseMarks
import OAI.Hierarchy.ProbeExcess

namespace OAI
/-! # Addressing the actual payload and signed-altimeter stock

Each public source record has one stock word. Each triple of stage, signed
axis and source record has one additional stock word. The marking scan reads
the very same cells that index the commodity score.
-/

namespace Hierarchy.ProtocolRAM.PurchaseInventory
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe
open scoped Fin.CommRing Classical
noncomputable section
variable {w stageCount h k : ℕ}

abbrev Axis (k : ℕ) := Fin (2*k)

/-- The leading bank is the payload bank, followed by one bank per stage and signed direction. -/
def lane : Commodity (Fin (2^h)) stageCount k → ℕ
  | .inl _ => 0
  | .inr ((_,stage),axis) => 1+stage.val*(2*k)+((PurchaseMarks.signedDirection k).symm axis).val

def record : Commodity (Fin (2^h)) stageCount k → Fin (2^h)
  | .inl i => i
  | .inr ((i,_),_) => i

def slot (c : Commodity (Fin (2^h)) stageCount k) := lane c*2^h+(record c).val

def footprint (h stageCount k : ℕ) := (1+stageCount*(2*k))*2^h

def bank (base h : ℕ) (stage : Fin stageCount) (j : Axis k) : Bank :=
  ⟨base+(1+stage.val*(2*k)+j.val)*2^h,h⟩

def stock (base : ℕ) (mem : Memory w) (c : Commodity (Fin (2^h)) stageCount k) : ℕ :=
  (mem (base+slot c)).val

theorem lane_lt (c : Commodity (Fin (2^h)) stageCount k) : lane c<1+stageCount*(2*k) := by
  rcases c with i | ⟨⟨i,stage⟩,axis⟩
  · simp [lane]
  · have bound := Nat.mul_le_mul_right (2*k) stage.isLt
    rw [Nat.succ_mul] at bound
    have a := ((PurchaseMarks.signedDirection k).symm axis).isLt
    simp only [lane]; omega

theorem slot_lt (c : Commodity (Fin (2^h)) stageCount k) : slot c < footprint h stageCount k := by
  have bound := Nat.mul_le_mul_right (2^h) (lane_lt c)
  rw [Nat.succ_mul] at bound
  have small := (record c).isLt
  unfold slot footprint
  omega

theorem slot_injective : Function.Injective (slot (h:=h) (stageCount:=stageCount) (k:=k)) := by
  intro x y same
  have separate : lane x=lane y ∧ record x=record y := by
    have lx := (record x).isLt
    have ly := (record y).isLt
    have block (v : Commodity (Fin (2^h)) stageCount k) : slot v/(2^h)=lane v := by
      rw [slot,Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (record v).isLt,Nat.zero_add]
    have digit (v : Commodity (Fin (2^h)) stageCount k) : slot v%(2^h)=(record v).val :=
      Nat.mul_add_mod_of_lt (record v).isLt
    exact ⟨(block x).symm.trans ((congrArg (·/(2^h)) same).trans (block y)),
      Fin.ext ((digit x).symm.trans ((congrArg (·%(2^h)) same).trans (digit y)))⟩
  rcases separate with ⟨lo,ro⟩
  rcases x with i | ⟨⟨i,s⟩,a⟩ <;> rcases y with j | ⟨⟨j,t⟩,b⟩
  · exact congrArg Sum.inl ro
  · simp only [lane] at lo; omega
  · simp only [lane] at lo; omega
  · let ds := (PurchaseMarks.signedDirection k).symm
    have sd := (ds a).isLt
    have td := (ds b).isLt
    have pp : 0<2*k := by omega
    have ij : s.val*(2*k)+(ds a).val=t.val*(2*k)+(ds b).val := by simpa [lane,ds,Nat.add_assoc] using lo
    have div (v : Fin stageCount) (d : Axis k) : (v.val*(2*k)+d.val)/(2*k)=v.val := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ pp,Nat.div_eq_of_lt d.isLt,Nat.zero_add]
    have so : s=t := Fin.ext ((div s (ds a)).symm.trans ((congrArg (·/(2*k)) ij).trans (div t (ds b))))
    have ax : a=b := ds.injective (Fin.ext (by subst t; omega))
    change i=j at ro
    subst j; subst t; subst b; rfl

theorem read (base : ℕ) (stage : Fin stageCount) (j : Axis k) (i : Fin (2^h)) (mem : Memory w)
    (room : 2^h ≤ 2^w) :
    ((bank base h stage j).read mem (i.val:Word w)).val =
      stock base mem (.inr ((i,stage),PurchaseMarks.signedDirection k j)) := by
  simp [bank,Bank.read,Bank.size,stock,slot,lane,record,Nat.mod_eq_of_lt i.isLt,
    Fin.val_cast_of_lt (i.isLt.trans_le room),Nat.add_assoc]

/-- Every marked coordinate used by the native selector obeys the threshold on
its exact integer position in the global commodity stock array. -/
theorem qualifies (phase : PhasePrice) (T : ℝ) (kind base : ℕ) (table : Bank)
    (stage : Fin stageCount) (j : Axis k) (i : Fin (2^h)) (mem : Memory w) (room : 2^h≤2^w)
    (sel : i∈PurchaseMarks.stratum phase T kind table (bank base h stage) mem j)
    (cap : stock base mem (.inr ((i,stage),PurchaseMarks.signedDirection k j))<table.size) :
    1/(4*(k:ℝ))≤phase.time*(rise phase.M (phase.quote kind
      (stock base mem (.inr ((i,stage),PurchaseMarks.signedDirection k j))))/T)^2 := by
  have true_stock := read base stage j i mem room
  exact true_stock ▸ PurchaseMarks.qualifies_of_mem phase T kind table (bank base h stage) mem j i sel
    (true_stock.symm ▸ cap)

end
end Hierarchy.ProtocolRAM.PurchaseInventory

end OAI
