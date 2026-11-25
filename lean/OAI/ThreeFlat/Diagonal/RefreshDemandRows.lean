import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import OAI.ThreeFlat.Diagonal.RefreshArrival
import OAI.ThreeFlat.RAM.MotifRows

namespace OAI
/-! # Physical addresses of both families of dense refresh demand rows -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks RAM.PhysicalPinsExpr
open CompressorPacking.Native RefreshTies
open scoped Classical BigOperators
noncomputable section

structure Columns (A : Type) where
  widths : A
  sourceBase : A
  sourceSlot : A
  portShift : A
  laneShift : A

def Columns.map {A B : Type} (f : A → B) (C : Columns A) : Columns B :=
  ⟨f C.widths,f C.sourceBase,f C.sourceSlot,f C.portShift,f C.laneShift⟩

variable {n : ℕ}

/-- Base-slot-major order, with the consumed port in the low lane bits. -/
def ordinal (m remaining base slot port lane : ℕ) : ℕ :=
  (base*m+slot)*(m*remaining)+(port+m*lane)

def wordAddress (m : ℕ) (remaining base slot port lane : Formula n) : Formula n :=
  .op .add (.op .mul (.op .add (.op .mul base (.lit m)) slot) (.op .mul (.lit m) remaining))
    (.op .add port (.op .mul (.lit m) lane))

def readColumn (base row : Formula n) : Formula n := .load (.op .add base row)

/-- Lookup for one tie: old source coordinates are used directly on outgoing
ties, and recovered with four reverse columns on incoming ties. -/
def demand (m : ℕ) (C : Columns (Formula n)) (remaining block : Formula n) (dir : Bool)
    (i s : ℕ) : Formula n :=
  let v := Formula.op .div block remaining
  let l := Formula.op .mod block remaining
  let p := Formula.op .add (.op .mul v (.lit m)) (.lit s)
  if dir then
    readColumn C.widths (wordAddress m remaining (readColumn C.sourceBase p) (readColumn C.sourceSlot p)
      (.op .bitXor (.lit i) (readColumn C.portShift p)) (.op .bitXor l (readColumn C.laneShift p)))
  else readColumn C.widths (wordAddress m remaining v (.lit s) (.lit i) l)

def absAddress (m : ℕ) (C : Columns ℕ) (mem : ℕ → ℕ) (remaining block : ℕ) (dir : Bool) (i s : ℕ) : ℕ :=
  let v := block/remaining
  let l := block%remaining
  let p := v*m+s
  if dir then C.widths+ordinal m remaining (mem (C.sourceBase+p)) (mem (C.sourceSlot+p))
    (i ^^^ mem (C.portShift+p)) (l ^^^ mem (C.laneShift+p))
  else C.widths+ordinal m remaining v s i l

theorem demand_value (k : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
    (m : ℕ) (C : Columns (Formula n)) (remaining block : Formula n) (dir : Bool) (i s : ℕ) :
    let V := Formula.natural k data mem vs
    V (demand m C remaining block dir i s) = mem (absAddress m (C.map V) mem (V remaining) (V block) dir i s) := by
  cases dir <;> rfl

variable {a t v : ℕ}

abbrev mPort (a : ℕ) := 2^a
abbrev Block (v t : ℕ) := Fin v × BitWord t
abbrev Address' (v a t : ℕ) := Address (Block v t) (mPort a)

def index (e : Address' v a t) := ordinal (mPort a) (2^t) e.1.1.val e.2.2.val e.2.1.val (tagOrdinal t e.1.2).val
def blockId (u : Block v t) := u.1.val*2^t+(tagOrdinal t u.2).val

private theorem ordinal_sub {b : ℕ} (x y : BitWord b) :
    (tagOrdinal b (x-y)).val = (tagOrdinal b x).val ^^^ (tagOrdinal b y).val := by
  have neg : -y = y := by funext i; exact (by decide : ∀ z : Fin 2, -z=z) (y i)
  rw [sub_eq_add_neg,neg,tagOrdinal_add]

variable (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))

/-- Meanings of the reverse slot columns in the current stage's public memory. -/
structure Stored (C : Columns ℕ) (mem : ℕ → ℕ) (w : Address' v a t → ℕ) : Prop where
  width : ∀ e, mem (C.widths+index e) = w e
  src : ∀ (i : Fin v) (s : Fin (mPort a)), mem (C.sourceBase+(i.val*mPort a+s.val)) = (G.base.target.symm (i,s)).1.val
  slot : ∀ (i : Fin v) (s : Fin (mPort a)), mem (C.sourceSlot+(i.val*mPort a+s.val)) = (G.base.target.symm (i,s)).2.val
  consumed : ∀ (i : Fin v) (s : Fin (mPort a)), mem (C.portShift+(i.val*mPort a+s.val)) =
    (tagOrdinal a (G.displacement (G.base.target.symm (i,s))).1).val
  remaining : ∀ (i : Fin v) (s : Fin (mPort a)), mem (C.laneShift+(i.val*mPort a+s.val)) =
    (tagOrdinal t (G.displacement (G.base.target.symm (i,s))).2).val

/-- The native absolute address is exactly the source-coordinate old-graph
field read by the algebraic refresh kernel, even on incoming ties. -/
theorem demand_address {C : Columns ℕ} {mem : ℕ → ℕ} {w : Address' v a t → ℕ}
    (stored : Stored G C mem w) (u : Block v t) (dir : Bool) (i s : Fin (mPort a)) :
    absAddress (mPort a) C mem (2^t) (blockId u) dir i.val s.val =
      C.widths+index (addr (arrival G (tagOrdinal a).symm) u (dir,i,s)) := by
  obtain ⟨b,x⟩ := u
  have div : blockId (b,x) / 2^t = b.val := by
    simp only [blockId,Nat.mul_comm b.val (2^t),Nat.mul_add_div (by positivity : 0<2^t),Nat.div_eq_of_lt (tagOrdinal t x).isLt,Nat.add_zero]
  have mod : blockId (b,x) % 2^t = (tagOrdinal t x).val := by
    simp only [blockId,Nat.mul_comm b.val (2^t),Nat.mul_add_mod,Nat.mod_eq_of_lt (tagOrdinal t x).isLt]
  cases dir with
  | false => simp [absAddress,div,mod,addr,index]
  | true =>
    have hin : (arrival G (tagOrdinal a).symm).symm ((b,x),i,s) =
        (((G.base.target.symm (b,s)).1, x-(G.displacement (G.base.target.symm (b,s))).2),
          tagOrdinal a ((tagOrdinal a).symm i-(G.displacement (G.base.target.symm (b,s))).1),
          (G.base.target.symm (b,s)).2) := rfl
    simp only [absAddress,div,mod,ite_true,addr,hin,index,
      stored.src,stored.slot,stored.consumed,stored.remaining,ordinal_sub,Equiv.apply_symm_apply]

theorem demand_read {C : Columns ℕ} {mem : ℕ → ℕ} {w : Address' v a t → ℕ}
    (stored : Stored G C mem w) (u : Block v t) (dir : Bool) (i s : Fin (mPort a)) :
    mem (absAddress (mPort a) C mem (2^t) (blockId u) dir i.val s.val) =
      w (addr (arrival G (tagOrdinal a).symm) u (dir,i,s)) := by
  rw [demand_address G stored,stored.width]

end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
