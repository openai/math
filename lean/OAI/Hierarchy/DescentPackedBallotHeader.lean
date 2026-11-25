import OAI.Hierarchy.DescentColonies
import OAI.Hierarchy.DescentSeedCableWords
import OAI.Hierarchy.DescentSeedHeaderCharge
import OAI.Hierarchy.DescentSeedIncidenceLoad
import OAI.Hierarchy.DescentSeedRawBallot
import OAI.Hierarchy.DescentSeedRootJoinWords

namespace OAI
/-! # One copy of the seed graph and short packed census fields for all stacked copies -/
namespace Hierarchy.DescentPackedSeed
open DescentSeedRoot DescentInitialHost
open ThreeFlat Routing Catalyst Diagonal TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) {R s : ℕ}
local notation "V₀" => Fintype.card (Vertex X)
local notation "E₀" => Fintype.card (Cable X)
local notation "H" => Fintype.card (Old X)

def laneKey (v : Fin H) (z : Fin (R*8)) : Option (CountKey X R) :=
  let u:=(Fintype.equivFin (Old X)).symm v
  let (j,t):=finProdFinEquiv.symm z
  (lookup X u t).map (fun pat=>(j,⟨u,pat⟩))

def cells (sel : Select X R s→Bool) (v : Fin H) (z : Fin (R*8)) : DescentSIMDLookup.Cell (digitsNeeded s) :=
  (laneKey X v z).elim 0 (rawCount X sel)

@[simp] theorem cells_at (sel : Select X R s→Bool) (j : Fin R) (v : Old X) (pat : LocalPattern X v) :
    cells X sel ((Fintype.equivFin _) v) (finProdFinEquiv (j,code X pat))=rawCount X sel (j,⟨v,pat⟩) := by
  let order := Fintype.equivFin (Old X)
  obtain ⟨i,rfl⟩ := order.symm.surjective v
  change cells X sel (order (order.symm i)) _ = _
  rw [order.apply_symm_apply]
  simp [cells,laneKey,order]

theorem valid_iff (sel : Select X R s→Bool) :
    valid X sel ↔ ∀v z,(cells X sel v z).val≤ s := by
  constructor
  · intro ok v z
    unfold cells
    cases laneKey X v z with
    | none=>simp
    | some key=>exact ok key
  · rintro hs ⟨j,v,pat⟩
    simpa using hs ((Fintype.equivFin _) v) (finProdFinEquiv (j,code X pat))

theorem multiplicity_pos {w s : ℕ} (wide : 2*digitsNeeded s≤w) : 0< multiplicity w s := by
  have pos:0<digitsNeeded s:=Nat.zero_lt_succ _
  unfold multiplicity
  split
  · rename_i room
    have live:=DescentSIMDLookup.occupancy w (8*digitsNeeded s) (by omega) (by omega)
    omega
  · exact (DescentSIMDLookup.occupancy w (digitsNeeded s) pos wide).1

abbrev PackedRow (R s w : ℕ) := DescentSIMDLookup.Row H (R*8) (multiplicity w s)
def packedWord (w : ℕ) (sel : Select X R s→Bool) (i : Fin (rows X R s w)) : Word w :=
  ((DescentSIMDLookup.data (cells X sel) ((DescentSIMDLookup.row _ _ _).symm i)).val:ℕ)

/-- Six global scalars give the stacked site and edge counts and the original
shape. Each original vertex and each original cable then contributes eight
fixed words once, independently of the number of copies. -/
abbrev Shape := Vertex X ⊕ Cable X
def shapeOrder : Shape X ≃ Fin (V₀+E₀) :=
  ((Fintype.equivFin _).sumCongr (Fintype.equivFin _)).trans finSumFinEquiv
def shapeCell (v : Shape X) (t : Fin 8) : Fin (publicWords X) :=
  finSumFinEquiv (.inr (finProdFinEquiv (shapeOrder X v,t)))
def scalar (R s : ℕ) : Fin 6→ℕ := ![R*V₀,R*E₀,V₀,E₀,R,s]
/-- Ordinals refer to the immutable original cable or external bank. The two
cable tags distinguish its outgoing and incoming endpoint. -/
def legCode (v : Vertex X) : LocalBoundary X v→ℕ
  | .inl e=>1+3*index e.val+(if source X.network.copyGraph e.val=v then 0 else 1)
  | .inr i=>1+3*i.val.val+2

def legWord (v : Vertex X) (j : Fin 3) : ℕ :=
  if h : j.val<legArity X v then legCode X v (leg X v ⟨j.val,h⟩) else 0

def shapeWords (s : ℕ) : Shape X→Fin 8→ℕ
  | .inl v=>![index v,(hubFlag X.network.copyGraph v).toNat,Sum.elim index Fin.val v,legWord X v 0,
    legWord X v 1,legWord X v 2,legArity X v,0]
  | .inr e=>cableWords X s (0:Fin 1) e

def publicWord (R s w : ℕ) (i : Fin (publicWords X)) : Word w :=
  match (finSumFinEquiv (m:=6) (n:=(V₀+E₀)*8)).symm i with
  | .inl t=>(scalar X R s t:ℕ)
  | .inr q=>
    let (v,t):=finProdFinEquiv.symm q
    (shapeWords X s ((shapeOrder X).symm v) t:ℕ)

def base (w : ℕ) (sel : Select X R s→Bool) : ℕ→Word w :=
  joinWords (publicWord X R s w) (packedWord X w sel)

theorem public_at (w : ℕ) (sel : Select X R s→Bool) (i : Fin (publicWords X)) :
    initialMemory (headerWords X R s w) (base X w sel) i.val=publicWord X R s w i :=
  join_left _ _ i

theorem shape_at (w : ℕ) (sel : Select X R s→Bool) (v : Shape X) (q : Fin 8) :
    initialMemory (headerWords X R s w) (base X w sel) (shapeCell X v q).val=(shapeWords X s v q:ℕ) := by
  rw [public_at]
  simp [shapeCell,publicWord]

def legColumn (j : Fin 3) : Fin 8 := ⟨3+j.val,by have:=j.isLt;omega⟩

theorem leg_at (w : ℕ) (sel : Select X R s→Bool) (v : Vertex X) (j : Fin 3) :
    initialMemory (headerWords X R s w) (base X w sel) (shapeCell X (.inl v) (legColumn j)).val=(legWord X v j:ℕ) := by
  rw [shape_at]
  fin_cases j <;> rfl

theorem arity_at (w : ℕ) (sel : Select X R s→Bool) (v : Vertex X) :
    initialMemory (headerWords X R s w) (base X w sel) (shapeCell X (.inl v) 6).val=(legArity X v:ℕ) := by
  rw [shape_at]
  rfl

theorem site_count (w : ℕ) (sel : Select X R s→Bool) :
    initialMemory (headerWords X R s w) (base X w sel) 0=(R*V₀:ℕ) := by
  let i : Fin (publicWords X) := finSumFinEquiv (Sum.inl (0 : Fin 6) : Fin 6 ⊕ Fin ((V₀+E₀)*8))
  apply (public_at X w sel i).trans
  simp only [i,publicWord,Equiv.symm_apply_apply]
  rfl

def canonicalDigits (groups k : ℕ) : Fin (groups*2^k) ≃ Fin groups × DescentColonies.Block k := finProdFinEquiv.symm

theorem canonical_group {groups k : ℕ} (j : Fin (groups*2^k)) :
    (canonicalDigits groups k j).1.val=j.val/2^k := rfl
theorem canonical_block {groups k : ℕ} (j : Fin (groups*2^k)) :
    (canonicalDigits groups k j).2.val=j.val%2^k := rfl

/-- Recover a stacked cable's literal legacy row from the single installed
original cable row. No table of per-copy endpoints or widths occurs. -/
def cableField (w : ℕ) (sel : Select X R s→Bool) (j : Fin R) (e : Cable X) (q : Fin 8) : Word w :=
  let field:=initialMemory (headerWords X R s w) (base X w sel) (shapeCell X (.inr e) q).val
  if q.val=0 then (j.val:ℕ)
  else if q.val=1 then ((j.val*E₀:ℕ):Word w)+field
  else if q.val=2 ∨ q.val=3 then ((j.val*V₀:ℕ):Word w)+field else field

theorem cableField_read (w : ℕ) (sel : Select X R s→Bool) (j : Fin R) (e : Cable X) (q : Fin 8) :
    cableField X w sel j e q=(cableWords X s j e q:ℕ) := by
  unfold cableField
  rw [shape_at]
  have offset (n t : ℕ) : ((j.val*n:ℕ):Word w)+((0*n+t:ℕ):Word w)=((j.val*n+t:ℕ):Word w) := by
    rw [Nat.zero_mul,Nat.zero_add,Nat.cast_add]
  fin_cases q
  · rfl
  · exact offset _ (index e)
  · exact offset _ (index (source X.network.copyGraph e))
  · exact offset _ (index (target X.network.copyGraph e))
  all_goals rfl

theorem vertex_fields (w : ℕ) (sel : Select X R s→Bool) (j : Fin R) (v : Vertex X) :
    let mem:=initialMemory (headerWords X R s w) (base X w sel)
    ((j.val*V₀:ℕ):Word w)+mem (shapeCell X (.inl v) 0).val=(vertexID X j v:Word w) ∧
      mem (shapeCell X (.inl v) 1).val=((hubFlag X.network.copyGraph v).toNat:ℕ) := by
  dsimp only
  rw [shape_at,shape_at]
  exact ⟨(Nat.cast_add (R:=Word w) (j.val*V₀) (index v)).symm,rfl⟩

theorem data_at (w : ℕ) (sel : Select X R s→Bool) (a : PackedRow X R s w) :
    initialMemory (headerWords X R s w) (base X w sel)
      (publicWords X+(DescentSIMDLookup.row _ _ _ a).val)=
      ((DescentSIMDLookup.data (cells X sel) a).val:ℕ) := by
  unfold headerWords base
  exact (join_right (publicWord X R s w) (packedWord X w sel) (DescentSIMDLookup.row _ _ _ a)).trans
    (by simp only [packedWord,Equiv.symm_apply_apply])

theorem lane_fit (w s : ℕ) : digitsNeeded s*multiplicity w s≤w := by
  unfold multiplicity
  split
  · have fit:=DescentSIMDLookup.lanes_fit w (8*digitsNeeded s)
    calc digitsNeeded s*(DescentSIMDLookup.lanes w (8*digitsNeeded s)*8)
          =DescentSIMDLookup.lanes w (8*digitsNeeded s)*(8*digitsNeeded s):=by ring
      _ ≤w:=fit.trans (Nat.div_le_self ..)
  · simpa only [Nat.mul_comm (digitsNeeded s)] using (DescentSIMDLookup.lanes_fit w (digitsNeeded s)).trans (Nat.div_le_self ..)

/-- Reading the actual old site's real pattern needs only one window in its
packed vector, at the explicit quotient of the mixed-radix copy/slot ordinal. -/
theorem slot_read (w : ℕ) (sel : Select X R s→Bool) (room : 0 < multiplicity w s)
    (j : Fin R) (v : Old X) (q : LocalPattern X v) :
    let rank:=finProdFinEquiv (j,code X q)
    let host:=(Fintype.equivFin (Old X)) v
    let a:=DescentSIMDLookup.position host rank room
    DescentSIMDLookup.digit (digitsNeeded s) (DescentSIMDLookup.lane rank room).val
      (initialMemory (headerWords X R s w) (base X w sel) (publicWords X+(DescentSIMDLookup.row _ _ _ a).val)).val=
      (rawCount X sel (j,⟨v,q⟩)).val := by
  let rank:Fin (R*8):=finProdFinEquiv (j,code X q)
  let host:Fin H:=(Fintype.equivFin _) v
  let a:=DescentSIMDLookup.position host rank room
  let i:=DescentSIMDLookup.lane rank room
  have addr : a.2.val*multiplicity w s+i.val=rank.val := Nat.div_add_mod' ..
  have live : a.2.val*multiplicity w s+i.val<R*8:=addr.trans_lt rank.isLt
  have same : (⟨_,live⟩:Fin (R*8))=rank:=Fin.ext addr
  have fit : (DescentSIMDLookup.data (cells X sel) a).val<2^w :=
    (DescentSIMDLookup.data (cells X sel) a).isLt.trans_le (Nat.pow_le_pow_right (by decide) (lane_fit w s))
  change DescentSIMDLookup.digit (digitsNeeded s) i.val
    (initialMemory (headerWords X R s w) (base X w sel) (publicWords X+(DescentSIMDLookup.row _ _ _ a).val)).val=_
  rw [data_at,Fin.val_cast_of_lt fit]
  unfold DescentSIMDLookup.data
  rw [DescentSIMDLookup.digit_encode,dite_eq_left live]
  exact (congrArg (fun r=> (cells X sel host r).val) same).trans (congrArg Fin.val (cells_at X sel j v q))

def cellPin (v : Fin H) (pos : Fin (R*8)) (j : Fin (digitsNeeded s)) : Select X R s ⊕ Bool :=
  match laneKey X v pos with
  | none => .inr false
  | some key=>.inl (key,j)

theorem cellPin_at (sel : Select X R s→Bool) (v : Fin H) (pos : Fin (R*8)) (j : Fin (digitsNeeded s)) :
    Sum.elim sel id (cellPin X v pos j)=wordBits (digitsNeeded s) (cells X sel v pos) j := by
  rw [←Computability.VPVNP.LiveHeader.testBit_wordBits]
  unfold cellPin cells
  cases laneKey X v pos with
  | none=>simp
  | some key=>exact (raw_digits X sel key j).symm

def shortPin (w : ℕ) (a : PackedRow X R s w) (i : Fin w) : Select X R s ⊕ Bool :=
  let d:=digitsNeeded s
  let M:=multiplicity w s
  if i.val<d*M then
    if h : a.2.val*M+i.val/d<R*8 then
      cellPin X a.1 ⟨_,h⟩ ⟨i.val%d,Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
    else .inr false
  else .inr false

theorem shortPin_at (w : ℕ) (sel : Select X R s→Bool) (a : PackedRow X R s w) (i : Fin w) :
    Sum.elim sel id (shortPin X w a i)=DescentSIMDLookup.sourcePin (cells X sel) a i := by
  change Sum.elim sel id (if i.val<digitsNeeded s*multiplicity w s then
    if live : a.2.val*multiplicity w s+i.val/digitsNeeded s<R*8 then
      cellPin X a.1 ⟨_,live⟩ ⟨i.val%digitsNeeded s,Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
    else .inr false
    else .inr false)=_
  by_cases inside : i.val<digitsNeeded s*multiplicity w s
  · by_cases live : a.2.val*multiplicity w s+i.val/digitsNeeded s<R*8
    · simpa only [DescentSIMDLookup.sourcePin,inside,live,ite_eq_left,dite_eq_left] using
        (cellPin_at X sel a.1 ⟨_,live⟩ ⟨i.val%digitsNeeded s,Nat.mod_lt _ (Nat.zero_lt_succ _)⟩)
    · simp [DescentSIMDLookup.sourcePin,inside,live]
  · simp [DescentSIMDLookup.sourcePin,inside]

def dataPin (w : ℕ) (t : Fin (rows X R s w) × Fin (w+1)) : Select X R s ⊕ Bool :=
  if h : t.2.val<w then
    shortPin X w ((DescentSIMDLookup.row _ _ _).symm t.1) ⟨t.2.val,h⟩
  else .inr false

theorem dataPin_at (w : ℕ) (sel : Select X R s→Bool) (t : Fin (rows X R s w)×Fin (w+1)) :
    Sum.elim sel id (dataPin X w t)=TraceWords.bits (wide (packedWord X w sel t.1)) t.2 := by
  by_cases lo : t.2.val<w
  · rw [dataPin,dite_eq_left lo,shortPin_at,←DescentSIMDLookup.source_pin (fit:=lane_fit w s),
      ←Computability.VPVNP.LiveHeader.testBit_wordBits]
    rfl
  · have high : (packedWord X w sel t.1).val<2^t.2.val :=
      (packedWord X w sel t.1).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [dataPin,lo,TraceWords.bits,wide,Nat.testBit_lt_two_pow high]

def headerPin (R s w : ℕ) : Fin (headerWords X R s w)×Fin (w+1)→Select X R s ⊕ Bool :=
  joinPins (fun t : Fin (publicWords X)×Fin (w+1)=>.inr (TraceWords.bits (wide (publicWord X R s w t.1)) t.2))
    (dataPin X w)

theorem headerPin_at (w : ℕ) (sel : Select X R s→Bool) (t : Fin (headerWords X R s w)×Fin (w+1)) :
    Sum.elim sel id (headerPin X R s w t)=TraceWords.bits (wide (base X w sel t.1.val)) t.2 :=
  join_agrees (Sum.elim sel id) (publicWord X R s w) (packedWord X w sel) _ _ (fun _=>rfl) (dataPin_at X w sel) t


end
end Hierarchy.DescentPackedSeed

end OAI
