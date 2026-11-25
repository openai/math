import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Reading the opposite raw trunk terminal inside the compact actor directory -/
namespace Hierarchy.DescentResetTrunkCompactPointer
open DescentPackedZip DescentSixParty.Chronology
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H P N w out : ℕ}

structure Banks where
  here : Bank
  turn : Bank
  number : Bank
  total : Bank

def alternate (B : Banks) (H P : ℕ) : Expr :=
  let src:=Expr.lookup B.here .row
  let next:=Expr.lookup B.turn src
  .branch .lt .row (.lookup B.total (.lit 0))
    (.branch .lt next (.lit P) (.lookup B.number next) (.lit H)) (.lit H)

structure Room (B : Banks) (N H P w out : ℕ) : Prop where
  here : B.here.Fits w out
  turn : B.turn.Fits w out
  number : B.number.Fits w out
  total : B.total.Fits w out
  dense : N≤B.here.size
  raw : P≤B.turn.size
  «prefix» : P≤B.number.size
  count : H<2^w
  palette : P<2^w

/-- All three directory reads refer to the same measured compact actor.
The public turn table may use its numerical sentinel when no trunk is present. -/
structure Measured (B : Banks) (name : Fin N→Fin P) (opposite : Fin N→Option (Fin N)) (m : Memory w) : Prop where
  count : m B.total.base=(N:Word w)
  here : ∀i,m (B.here.base+i.val)=((name i).val:Word w)
  turn : ∀i,m (B.turn.base+(name i).val)=(((opposite i).elim P (fun j=>(name j).val):ℕ):Word w)
  number : ∀i,m (B.number.base+(name i).val)=(i.val:Word w)

theorem Room.weaken {B : Banks} (r : Room B N H P w out) {next : ℕ} (before : out≤next) :
    Room B N H P w next := by
  have up (k : Bank) (f : k.Fits w out) : k.Fits w next:=⟨f.1,f.2.1,f.2.2.trans before⟩
  exact ⟨up _ r.here,up _ r.turn,up _ r.number,up _ r.total,r.dense,r.raw,r.prefix,r.count,r.palette⟩

/-- The same acquired prefix, inverse, count and right-palette values survive
every later pass that preserves memory below the beginning of its output. -/
theorem Measured.keep {B : Banks} {name : Fin N→Fin P} {opposite : Fin N→Option (Fin N)}
    {m m' : Memory w} (s : Measured B name opposite m) (r : Room B N H P w out)
    (preserved : ∀a,a<out→m' a=m a) : Measured B name opposite m' := by
  have origin : B.total.base<out:=(Nat.lt_add_of_pos_right r.total.1).trans_le r.total.2.2
  refine ⟨(preserved _ origin).trans s.count,?_,?_,?_⟩
  · intro i
    have below:=(Nat.add_lt_add_left (i.isLt.trans_le r.dense) B.here.base).trans_le r.here.2.2
    exact (preserved _ below).trans (s.here i)
  · intro i
    have below:=(Nat.add_lt_add_left ((name i).isLt.trans_le r.raw) B.turn.base).trans_le r.turn.2.2
    exact (preserved _ below).trans (s.turn i)
  · intro i
    have below:=(Nat.add_lt_add_left ((name i).isLt.trans_le r.prefix) B.number.base).trans_le r.number.2.2
    exact (preserved _ below).trans (s.number i)

def pointer (bounded : N≤H) (opposite : Fin N→Option (Fin N)) (h : Fin H) : Option (Fin H) :=
  if yes : h.val<N then (opposite ⟨h.val,yes⟩).map (Fin.castLE bounded) else none

theorem fits (B : Banks) (space : Room B N H P w out) : (alternate B H P).Fits w out :=
  ⟨trivial,⟨space.total,trivial⟩,⟨⟨space.turn,space.here,trivial⟩,trivial,
    ⟨space.number,space.turn,space.here,trivial⟩,trivial⟩,trivial⟩

private theorem compare_lt {a b : ℕ} (x : a<2^w) (y : b<2^w) :
    Comparison.lt.test (a:Word w) (b:Word w)=decide (a<b) := by
  simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt x,Fin.val_cast_of_lt y]

theorem sample (B : Banks) (name : Fin N→Fin P) (opposite : Fin N→Option (Fin N)) (bounded : N≤H)
    (m : Memory w) (space : Room B N H P w out) (stored : Measured B name opposite m) (h : Fin H) :
    (alternate B H P).eval m (h.val:Word w)=(((pointer bounded opposite h).elim H Fin.val:ℕ):Word w) := by
  have total : B.total.read m ((0:ℕ):Word w)=(N:Word w):=by
    rw [bank_read B.total m space.total.1 space.total,Nat.add_zero,stored.count]
  have fixed (i : Fin N) : B.here.read m (i.val:Word w)=((name i).val:Word w):=
    (bank_read B.here m (i.isLt.trans_le space.dense) space.here).trans (stored.here i)
  have peer (i : Fin N) : B.turn.read m ((name i).val:Word w)=
      (((opposite i).elim P (fun j=>(name j).val):ℕ):Word w):=
    (bank_read B.turn m ((name i).isLt.trans_le space.raw) space.turn).trans (stored.turn i)
  have compact (i : Fin N) : B.number.read m ((name i).val:Word w)=(i.val:Word w):=
    (bank_read B.number m ((name i).isLt.trans_le space.prefix) space.number).trans (stored.number i)
  have nc:=bounded.trans_lt space.count
  simp only [alternate,Expr.eval,total,compare_lt (h.isLt.trans space.count) nc,decide_eq_true_eq]
  by_cases real_ : h.val<N
  · let i : Fin N:=⟨h.val,real_⟩
    have where_ : B.here.read m (h.val:Word w)=((name i).val:Word w):=fixed i
    have selected : pointer bounded opposite h=(opposite i).map (Fin.castLE bounded) := by
      rw [pointer,dite_eq_left real_]
    let numbered (code : Word w) : Word w :=
      if Comparison.lt.test code (P:Word w) then B.number.read m code else (H:Word w)
    have turned := (congrArg (B.turn.read m) where_).trans (peer i)
    rw [ite_eq_left real_,selected]
    change numbered (B.turn.read m (B.here.read m (h.val:Word w))) = _
    refine (congrArg numbered turned).trans ?_
    cases chosen : opposite i with
    | none=>simp [numbered,compare_lt space.palette space.palette]
    | some v=>
      have nv:=((name v).isLt).trans space.palette
      simp [numbered,compare_lt nv space.palette,(name v).isLt,compact v]
  · simp only [ite_eq_right real_,pointer,dite_eq_right real_,Option.elim_none]

def phase (w out H P : ℕ) (B : Banks) : NativePhase w :=
  let e:=alternate B H P
  ⟨scan w out H e,4+H*(2*e.work+4),image out H e,scan_cheap w out H e⟩

theorem any (B : Banks) (out : ℕ) (m : Memory w) (space : Room B N H P w out) (room : out+H<2^w) :
    let p:=phase w out H P B
    p.Runs m ∧ ∀a,a<out ∨ out+H≤a→p.image m a=m a :=
  ⟨scan_exec _ _ _ _ (fits B space) room,ProtocolRAMGeneratedWrite.frame_image _ _ _ _⟩

theorem run (B : Banks) (name : Fin N→Fin P) (opposite : Fin N→Option (Fin N)) (bounded : N≤H)
    (out : ℕ) (m : Memory w) (space : Room B N H P w out) (stored : Measured B name opposite m)
    (room : out+H<2^w) :
    let p:=phase w out H P B
    p.Runs m ∧ (∀h : Fin H,p.image m (out+h.val)=(((pointer bounded opposite h).elim H Fin.val:ℕ):Word w)) ∧
      (∀a,a<out ∨ out+H≤a→p.image m a=m a) := by
  refine ⟨scan_exec _ _ _ _ (fits B space) room,?_,ProtocolRAMGeneratedWrite.frame_image _ _ _ _⟩
  intro h
  exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ h).trans (sample B name opposite bounded m space stored h)

theorem cost (B : Banks) : (alternate B H P).work=42 := rfl

end
end Hierarchy.DescentResetTrunkCompactPointer

end OAI
