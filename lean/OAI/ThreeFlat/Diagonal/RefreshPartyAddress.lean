import OAI.ThreeFlat.Diagonal.RefreshPartyPorts
import OAI.ThreeFlat.Diagonal.RefreshDensePins
import OAI.ThreeFlat.Diagonal.RefreshDemandChoice

namespace OAI
/-! # Physical refresh-party pin lookup for the selected history node -/

namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows LinearAlgebra.SpectralBooks
open CompressorPacking.Native RefreshDemandRows RefreshTies MotifBinaryPacking
open scoped Classical BigOperators
noncomputable section

abbrev F := Formula 7

/-- One bit of an old child state or a fresh external half edge. -/
structure Location (A : Type) where
  scope : A
  child : A
  half : A
  bit : A

def Location.map {A B : Type} (f : A → B) (r : Location A) : Location B :=
  ⟨f r.scope,f r.child,f r.half,f r.bit⟩

/-- Width-word address, with both port and slot supplied at runtime. -/
def coordinates {n : ℕ} (radix : ℕ) (C : Columns (Formula n)) (remain block : Formula n)
    (back : Bool) (port slot : Formula n) : Formula n :=
  let base := Formula.op .div block remain
  let l := Formula.op .mod block remain
  let q := plus (.op .mul base (.lit radix)) slot
  let idx := if back then
    wordAddress radix remain (readColumn C.sourceBase q) (readColumn C.sourceSlot q)
      (.op .bitXor port (readColumn C.portShift q)) (.op .bitXor l (readColumn C.laneShift q))
    else wordAddress radix remain base slot port l
  plus C.widths idx

def stageField (k : ℕ) : F := .load (plus (.reg 0) (.lit k))
def inputs : Columns F :=
  let c (key i : ℕ) := plus (stageField key) (.op .mul (stageField 11) (.lit i))
  ⟨stageField 9,c 10 3,c 10 4,c 12 2,c 12 1⟩

/-- Consecutive width words differing only in their low-order old port.
The cutoff is recovered from the actual old source coordinate. -/
def bundleBefore {n : ℕ} (radix : ℕ) (oldBase address : Formula n) : Formula n :=
  let sourcePort := Formula.op .mod (.cut address oldBase) (.lit radix)
  let first := Formula.cut address sourcePort
  totals ((Finset.univ : Finset (Fin radix)).toList.map (fun q =>
    .select .lt (.lit q.val) sourcePort (.load (plus first (.lit q.val))) (.lit 0)))

def denseLoc (radix degree : ℕ) (dir side : Bool) (partner : F) : Location F :=
  let party : F := .reg 3
  let i := if side then partner else party
  let s := if side then party else partner
  let row := coordinates radix inputs (stageField 8) (.load (.reg 2)) dir i s
  let bit : F := .reg 5
  let oldHalf := plus partner (.lit (if dir then radix else 0))
  let scope := Formula.select .lt bit (.load row) (.lit (if side then 2 else 1)) (.lit 0)
  ⟨scope,.lit 0,if side then .lit (if dir then degree else 0) else oldHalf,
    if side then plus (bundleBefore radix inputs.widths row) bit else bit⟩

def sparseLoc (degree : ℕ) (side : Bool) (slot : F) : Location F :=
  let half := plus (.lit (1+(if side then degree else 0))) slot
  let flat := plus (.op .mul (.reg 1) (.lit (2*degree))) half
  let width := readColumn (stageField 40) (plus (.op .mul flat (.lit 4)) (.lit 2))
  let bit : F := .reg 5
  ⟨.select .lt bit width (.lit 2) (.lit 0),.lit 0,half,bit⟩

def member (r : Location F) : F :=
  .select .eq (.reg 6) (.lit 0) r.scope
    (.select .eq (.reg 6) (.lit 1) r.child (.select .eq (.reg 6) (.lit 2) r.half r.bit))

/-- Arguments are stage pointer, successor site ordinal, motif row pointer,
party, local half-ordinal, bit-index and result subfield. The demand order
is (direction,endpoint,partner). The sparse order is (direction,local). -/
def lookup (m h pad : ℕ) (supply : Bool) : F :=
  let degree := 1+h+pad
  let edge : F := .reg 4
  if supply then
    let slot := Formula.op .mod edge (.lit h)
    .select .lt edge (.lit h) (member (sparseLoc degree false slot)) (member (sparseLoc degree true slot))
  else
    let partner := Formula.op .mod edge (.lit m)
    .select .lt edge (.lit m) (member (denseLoc m degree false false partner))
      (.select .lt edge (.lit (2*m)) (member (denseLoc m degree false true partner))
        (.select .lt edge (.lit (3*m)) (member (denseLoc m degree true false partner))
          (member (denseLoc m degree true true partner))))

variable {W n v a t : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs

theorem coordinates_read (radix : ℕ) (C : Columns (Formula n)) (remaining block : Formula n)
    (dir : Bool) (i s : Formula n) :
    V (coordinates radix C remaining block dir i s) =
      absAddress radix (C.map V) mem (V remaining) (V block) dir (V i) (V s) := by
  cases dir <;> rfl

theorem fixed_sum {k : ℕ} (width : Fin k → ℕ) (p : Fin k) :
    (∑ j, if j.val<p.val then width j else 0)=∑ i : Fin p.val,width (Fin.castLE p.isLt.le i) := by
  classical
  let e : {j : Fin k // j.val<p.val} ≃ Fin p.val :=
    ⟨fun j=>⟨j.val.val,j.property⟩,fun i=>⟨Fin.castLE p.isLt.le i,i.isLt⟩,fun _=>rfl,fun _=>rfl⟩
  rw [←Finset.sum_filter]
  calc
    _ = ∑ j : {j : Fin k // j.val<p.val},width j.val :=
      Finset.sum_subtype _ (fun _=>by simp) _
    _ = _ := e.sum_comp (fun i=>width (Fin.castLE p.isLt.le i))

/-- All earlier fields in the bundle are looked up at their original source
port, including when this party is at the incoming end. -/
theorem bundle_read (C : Columns (Formula n)) (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (w : Address' v a t → ℕ) (st : Stored G (C.map V) mem w)
    (e : Address' v a t) (address : Formula n) (atWord : V address=V C.widths+index e) :
    V (bundleBefore (mPort a) C.widths address) =
      ∑ j : Fin e.2.1.val, w (e.1,Fin.castLE e.2.1.isLt.le j,e.2.2) := by
  let i := e.2.1
  let first := V C.widths+(e.1.1.val*mPort a+e.2.2.val)*(mPort a*2^t)+mPort a*(tagOrdinal t e.1.2).val
  have dec (j : Fin (mPort a)) : V C.widths+index (e.1,j,e.2.2)=first+j.val := by
    dsimp [index,ordinal,first]; ac_rfl
  have src : (V address-V C.widths)%mPort a=i.val := by
    rw [atWord,Nat.add_sub_cancel_left]
    have eq : index e=mPort a*((e.1.1.val*mPort a+e.2.2.val)*2^t+(tagOrdinal t e.1.2).val)+i.val := by
      dsimp [index,ordinal,i]; ring
    rw [eq,Nat.mul_add_mod,Nat.mod_eq_of_lt i.isLt]
  have start : V address-i.val=first := by
    have position : V C.widths+index e=first+i.val := dec i
    rw [atWord,position,Nat.add_sub_cancel]
  have readWidth (j : Fin (mPort a)) : mem (first+j.val)=w (e.1,j,e.2.2) := by
    rw [←dec j]
    exact st.width (e.1,j,e.2.2)
  calc
    _ = ∑ j : Fin (mPort a), if j.val < i.val then w (e.1,j,e.2.2) else 0 := by
      simp only [bundleBefore,totals_value,List.map_map,Finset.sum_map_toList]
      apply Finset.sum_congr rfl
      intro j _
      change (if decide (j.val<(V address-V C.widths)%mPort a) then
        mem (V address-(V address-V C.widths)%mPort a+j.val) else 0)=_
      simp only [src,start,readWidth,decide_eq_true_eq]
    _ = _ := fixed_sum (fun j=>w (e.1,j,e.2.2)) i

end
end ThreeFlat.Diagonal.RefreshParty

end OAI
