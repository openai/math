import OAI.Hierarchy.ProtocolRAMCalendarGlobalTests
import OAI.Hierarchy.ProtocolRAMCalendarInventory
import OAI.Hierarchy.ProbeCommodityBounds

namespace OAI
/-! # Closing the chronological score calibration using the actual resident price banks -/

namespace Hierarchy.ProtocolRAM.Calendar.GlobalTests
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank AttemptGate
open scoped BigOperators Classical
noncomputable section
variable {w z N k : ℕ}
abbrev Goods (z N k : ℕ) := Commodity (Fin (2^z)) N k

/-- A public native phase uses one bounded box per replicated kind and the actual
global reward on each signed altimeter. Payload and reserve stocks share the bit unit. -/
def price (A : AccountColumns (Goods z N k)) (t beta : ℝ) (cap : ℕ→ℝ) (precision : ℕ) : PhasePrice :=
  ⟨A.a,A.M,t,fun j=>if j=0 then 0 else beta,cap,A.payloadWidth,precision⟩

theorem lane_bonus (beta : ℝ) (i : Goods z N k) :
    (if PurchaseInventory.lane i=0 then 0 else beta)=bonus beta i := by
  cases i with
  | inl x => rfl
  | inr x =>
    rcases x with ⟨⟨p,j⟩,a⟩
    simp [PurchaseInventory.lane,bonus]

structure ReadStock (A : AccountColumns (Goods z N k)) (x : Inventory (Goods z N k))
    (l : Layout) (stocks : Bank) (s : PhasePrice) (m : Memory w) : Prop where
  resident : Resident l z N k s m
  rowRoom : rows z N k<2^w
  rowCap : rows z N k≤2^l.indexBits
  stockCap : rows z N k≤ stocks.size
  valueRoom : span l N k<2^w
  valueCap : span l N k≤2^l.indexBits
  limit : ∀i : Fin (rows z N k),(m (stocks.base+i.val)).val<l.stride
  fit : ∀ p (i : Fin (rows z N k)),valueWord l.precision (value s p) (kind i).val
    (m (stocks.base+i.val)).val<2^w
  bits : ∀ i : Fin (rows z N k),(m (stocks.base+i.val)).val=x.bits ((PurchaseInventory.slotEquiv z N k).symm i)

/-- The one-word archived-history guard and the native frozen candidate pass preserve
the immutable global table and the incoming retained stock throughout preparation. -/
theorem ReadStock.prepared {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {s : PhasePrice} {m : Memory w} (R : ReadStock A x l stocks s m)
    {q d : ℕ} (C : Chart w q d) (a : Attempt) (step : ready C (.attempt a) m)
    (guardROM : stop l z N k≤C.stopAt a) (guardStock : stocks.base+rows z N k≤C.stopAt a)
    (frozenROM : stop l z N k≤(C.frozen a).start)
    (frozenStock : stocks.base+rows z N k≤(C.frozen a).start) :
    ReadStock A x l stocks s (Calendar.prepared C a m) := by
  have stays (t : ℕ) (guardLo : t<C.stopAt a) (frozenLo : t<(C.frozen a).start) :
      Calendar.prepared C a m t=m t := by
    unfold Calendar.prepared
    rw [(C.frozen a).frame _ _ step.2.1 (Or.inl frozenLo)]
    simp [guard,Pass.apply,image,ThreeFlat.RAM.fillSegment,not_le.mpr guardLo]
  have stockEq (i : Fin (rows z N k)) :
      Calendar.prepared C a m (stocks.base+i.val)=m (stocks.base+i.val) := by
    have hi := i.isLt
    exact stays _ (by omega) (by omega)
  exact ⟨R.resident.transport (fun t _ ht=>stays t (ht.trans_le guardROM) (ht.trans_le frozenROM)),
    R.rowRoom,R.rowCap,R.stockCap,R.valueRoom,R.valueCap,fun i=>by rw [stockEq];exact R.limit i,
    fun p i=>by rw [stockEq];exact R.fit p i,fun i=>by rw [stockEq];exact R.bits i⟩

/-- The first sum writes only at and after its own fresh output. The later sum uses
the exact same installed public values and incoming stock. -/
theorem ReadStock.after_check {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {s : PhasePrice} {m : Memory w} (R : ReadStock A x l stocks s m)
    (Z : Check) (tableLo : stop l z N k≤Z.out) (stockLo : stocks.base+rows z N k≤Z.out) :
    ReadStock A x l stocks s (Z.after m) := by
  have stockUnchanged (i : Fin (rows z N k)) : Z.after m (stocks.base+i.val)=m (stocks.base+i.val) :=
    Z.frame m _ (by have := i.isLt; omega)
  exact ⟨R.resident.transport (fun a _ ha=>Z.frame m a (ha.trans_le tableLo)),R.rowRoom,R.rowCap,
    R.stockCap,R.valueRoom,R.valueCap,fun i=>by rw [stockUnchanged];exact R.limit i,
    fun p i=>by rw [stockUnchanged];exact R.fit p i,fun i=>by rw [stockUnchanged];exact R.bits i⟩

def ReadStock.wordRows {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {s : PhasePrice} {m : Memory w} (R : ReadStock A x l stocks s m)
    (payload : Bool) (out bnd : ℕ) := words l z N k s payload out bnd stocks m R.resident R.rowRoom
      R.rowCap R.stockCap R.valueRoom R.valueCap R.limit (R.fit payload)

theorem ReadStock.ledger {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {m : Memory w} {time beta : ℝ} {cap : ℕ→ℝ}
    (R : ReadStock A x l stocks (price A time beta cap l.precision) m) (payload : Bool) (out bnd : ℕ)
    (box : ∀i, A.box i=cap (PurchaseInventory.lane i)) (coeff : A.coefficient=bonus beta) :
    PriceKinds A.bank x A.payloadWidth (price A time beta cap l.precision) (PurchaseInventory.slotEquiv z N k).symm
      (R.wordRows payload out bnd).kind (R.wordRows payload out bnd).bits :=
  ⟨rfl,rfl,rfl,fun i=>(box _).symm,fun i=>by
    change (if PurchaseInventory.lane _=0 then 0 else beta)=A.coefficient _
    rw [coeff,lane_bonus],R.bits⟩

def ReadStock.payload {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {m : Memory w} {beta : ℝ} {cap : ℕ→ℝ}
    (R : ReadStock A x l stocks (price A 1 beta cap l.precision) m) (out : ℕ)
    (box : ∀i,A.box i=cap (PurchaseInventory.lane i)) (nonneg : ∀i,0≤A.box i)
    (coeff : A.coefficient=bonus beta) (unit : A.payload=payloadUnit) (ha : 0<A.a) (hb : 0≤beta) (hM : 0≤A.M)
    (precise : 0<l.precision) (room : 8*kinds N k≤l.precision) :
    SumCalibration (check l z N k true out (bound l z 1) stocks) m (pairing (fun i=>(A.payload i:ℝ))
      (maximizer A.a A.M 1 A.coefficient A.box (A.bank.units A.payloadWidth x))) ((3/2:ℝ)*(2^z:ℕ)) := by
  refine payload_calibration (fun j=>decide (j=0)) (R.wordRows true out (bound l z 1)) _
    (R.ledger true out _ box coeff) precise ?_ ha ?_ hM rfl nonneg (kinds N k) (rowCount z N k).le room rfl
  · change ∀ i : Fin (rows z N k), A.payload ((PurchaseInventory.slotEquiv z N k).symm i) =
      if decide ((kind i).val=0) then 1 else 0
    intro i
    rw [unit,payload_lane i]
    cases (PurchaseInventory.slotEquiv z N k).symm i <;> rfl
  · intro i
    change 0≤A.coefficient i
    rw [coeff]
    cases i <;> simp [bonus,hb]

def ReadStock.cool {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {m : Memory w} {time beta : ℝ} {cap : ℕ→ℝ}
    (R : ReadStock A x l stocks (price A time beta cap l.precision) m) (out : ℕ)
    (box : ∀i,A.box i=cap (PurchaseInventory.lane i)) (coeff : A.coefficient=bonus beta)
    (ha : 0≤A.a) (hb : 0≤beta) (scale r : ℝ) (hs : 0<time) (nn : 0≤ scale) (hr : 0<r)
    (precise : 0<l.precision) (room : 8*kinds N k≤l.precision) :
    SumCalibration (check l z N k false out (bound l z (scale*min (1/time) (1/r))) stocks) m
      (score A.a A.M A.coefficient (maximizer A.a A.M time A.coefficient A.box (A.bank.units A.payloadWidth x)))
      ((scale*min (1/time) (1/r)+1/2)*(2^z:ℕ)) := by
  refine cooling_calibration (R.wordRows false out (bound l z (scale*min (1/time) (1/r)))) _
    (R.ledger false out _ box coeff) precise ha ?_ scale r nn hs hr (kinds N k) (rowCount z N k).le room rfl
  intro i
  change 0≤A.coefficient i
  rw [coeff]
  cases i <;> simp [bonus,hb]

/-- Derivation of the second chronological global sum after the potential check.
Its public ROM is the same mounted resident table, and the debit/credit inventory
is unchanged at all the addresses interpreted as its input. -/
def ReadStock.board_payload {A : AccountColumns (Goods z N k)} {x : Inventory (Goods z N k)}
    {l : Layout} {stocks : Bank} {m : Memory w} {beta : ℝ} {cap : ℕ→ℝ} (old : TestBoard) (baseline : ℝ)
    (R : ReadStock A x l stocks (price A 1 beta cap l.precision) m)
    (tableLo : stop l z N k≤old.excess.out) (stockLo : stocks.base+rows z N k≤old.excess.out)
    (box : ∀i,A.box i=cap (PurchaseInventory.lane i)) (nonneg : ∀i,0≤A.box i)
    (coeff : A.coefficient=bonus beta) (unit : A.payload=payloadUnit) (ha : 0<A.a) (hb : 0≤beta) (hM : 0≤A.M)
    (precise : 0<l.precision) (room : 8*kinds N k≤l.precision) :
    let t := board l z N k old stocks baseline
    SumCalibration t.payload (t.excess.after m) (pairing (fun i=>(A.payload i:ℝ))
      (maximizer A.a A.M 1 A.coefficient A.box (A.bank.units A.payloadWidth x))) ((3/2:ℝ)*(2^z:ℕ)) :=
  (R.after_check (board l z N k old stocks baseline).excess tableLo stockLo).payload old.payload.out
    box nonneg coeff unit ha hb hM precise room

end
end Hierarchy.ProtocolRAM.Calendar.GlobalTests

end OAI
