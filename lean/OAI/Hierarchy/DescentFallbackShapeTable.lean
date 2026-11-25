import OAI.Hierarchy.DescentFallbackLeafScan
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentRosterOrder

namespace OAI
/-! # A public candidate-shape ROM, shared across all measured old hosts -/

namespace Hierarchy.DescentFallbackShapeTable
open DescentContacts DescentFallbackLeafScan DescentRosterOrder
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {Y w : ℕ}

def rows (r Y : ℕ) := ((r+1)*2^r)*(Y+1)

def cell (r : ℕ) (z : Endpoint Y) := (z.1.1*2^r+z.1.2)*(Y+1)+optionDigit z.2

def decode (r Y x : ℕ) : Endpoint Y :=
  let t:=x%(Y+1)
  ((x/(Y+1)/2^r,(x/(Y+1))%2^r),if h : 0<t then some ⟨t-1,by
    have := Nat.mod_lt x (Nat.zero_lt_succ Y)
    dsimp [t] at *;omega⟩ else none)

theorem option_fit (x : Option (Fin Y)) : optionDigit x<Y+1 := by
  cases x with
  | none=>exact Nat.succ_pos _
  | some j=>exact Nat.succ_lt_succ j.isLt

theorem cell_fit (r : ℕ) (z : Endpoint Y) (depth : z.1.1≤r) (fit : z.1.2<2^z.1.1) : cell r z<rows r Y := by
  have idFit:=fit.trans_le (Nat.pow_le_pow_right (by decide) depth)
  have interval : z.1.1*2^r+z.1.2<(r+1)*2^r := by
    calc
      _<z.1.1*2^r+2^r:=Nat.add_lt_add_left idFit _
      _=(z.1.1+1)*2^r:=(Nat.succ_mul ..).symm
      _≤_:=Nat.mul_le_mul_right _ (Nat.succ_le_succ depth)
  exact (Nat.add_lt_add_left (option_fit z.2) _).trans_le (by
    rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ interval)

theorem decode_cell (r : ℕ) (z : Endpoint Y) (depth : z.1.1≤r) (fit : z.1.2<2^z.1.1) : decode r Y (cell r z)=z := by
  have idFit:=fit.trans_le (Nat.pow_le_pow_right (by decide) depth)
  have p:=Nat.two_pow_pos r
  have byY (a b : ℕ) (h : b<Y+1) : (a*(Y+1)+b)/(Y+1)=a := by
    rw [Nat.mul_comm a (Y+1),Nat.mul_add_div (Nat.zero_lt_succ _),Nat.div_eq_of_lt h,Nat.add_zero]
  have byR (a b : ℕ) (h : b<2^r) : (a*2^r+b)/2^r=a := by
    rw [Nat.mul_comm a (2^r),Nat.mul_add_div p,Nat.div_eq_of_lt h,Nat.add_zero]
  rcases z with ⟨⟨d,i⟩,(_|j)⟩
  all_goals simp only [decode,cell,byY _ _ (option_fit _),byR _ _ idFit,Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt (option_fit _),Nat.mod_eq_of_lt idFit]
  · simp [show optionDigit (none : Option (Fin Y))=0 from rfl]
  · simp [show optionDigit (some j)=j.val+1 from rfl]

def shapeNumber (x : Endpoint Y) := Nat.pair (Nat.pair x.1.1 x.1.2) (optionDigit x.2)

theorem endpoint_read {V : Type} (host : V↪ℕ) (v : V) (x : Endpoint Y) :
    endpoint host (v,x)=Nat.pair (host v) (shapeNumber x) := rfl

def encode (x : Option (Endpoint Y)) := x.elim 0 (fun y=>shapeNumber y+1)

/-- Each directory entry is zero for padding, or one plus the paired local
shape. Neighbor host IDs, measured contact populations and the chosen basis
are all excluded from these mounted constants. -/
def table (r D g f Y cap a : ℕ) := if q : 0<cap then
  encode (localSlot (localShape r D g f (decode r Y (a/cap/2)) (a/cap%2==1))
    (⟨a%cap,Nat.mod_lt _ q⟩ : Fin cap)) else 0

def index (r : ℕ) (z : Endpoint Y) (hub : Bool) {cap : ℕ} (j : Fin cap) :=
  (2*cell r z+hub.toNat)*cap+j.val

theorem table_read (r D g f : ℕ) (z : Endpoint Y) (depth : z.1.1≤r) (fit : z.1.2<2^z.1.1)
    (hub : Bool) {cap : ℕ} (j : Fin cap) :
    table r D g f Y cap (index r z hub j)=encode (localSlot (localShape r D g f z hub) j) := by
  have jc : 0<cap := Nat.zero_lt_of_lt j.isLt
  let entry := 2*cell r z+hub.toNat
  have div : index r z hub j / cap=entry := by
    change (entry*cap+j.val)/cap=entry
    rw [Nat.mul_comm entry cap,Nat.mul_add_div jc,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have rem : index r z hub j % cap=j.val := by
    simp only [index,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  have address : (⟨index r z hub j%cap,Nat.mod_lt _ jc⟩ : Fin cap)=j := Fin.ext rem
  have half : entry/2=cell r z := by cases hub <;> simp only [entry,Bool.toNat_true,Bool.toNat_false] <;> omega
  have bit : (entry%2==1)=hub := by
    cases hub <;> simp [entry,Nat.add_mod]
  rw [table,dite_eq_left jc,div,half,bit,decode_cell r z depth fit,address]

def imageSize (r Y cap : ℕ) := 2*rows r Y*cap

theorem index_fit (r : ℕ) (z : Endpoint Y) (depth : z.1.1≤r) (fit : z.1.2<2^z.1.1)
    (hub : Bool) {cap : ℕ} (j : Fin cap) : index r z hub j < imageSize r Y cap := by
  have zn:=cell_fit r z depth fit
  have h : 2*cell r z+hub.toNat<2*rows r Y := by cases hub <;> simp_all; omega
  unfold index imageSize
  exact (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h)

theorem install (r D g f Y cap at₀ : ℕ) (m : Memory w) (fit : at₀+imageSize r Y cap<2^w) :
    let data:=table r D g f Y cap
    let out:=DescentStaticWordColumn.image at₀ data m (imageSize r Y cap)
    (DescentStaticWordColumn.program w at₀ data (imageSize r Y cap)).Exec m out (4+10*imageSize r Y cap) ∧
    ∀z : Endpoint Y, z.1.1≤r→z.1.2<2^z.1.1→∀(hub : Bool)(j : Fin cap),
      out (at₀+index r z hub j)=(encode (localSlot (localShape r D g f z hub) j):Word w) := by
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ fit,?_⟩
  intro z depth legal hub j
  rw [DescentStaticWordColumn.read _ _ _ _ (index_fit r z depth legal hub j),table_read r D g f z depth legal hub j]

end
end Hierarchy.DescentFallbackShapeTable

end OAI
