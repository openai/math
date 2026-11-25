import OAI.Hierarchy.DescentClosedHaloChip
import OAI.Hierarchy.DescentFixedRowProgram
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Four current compact neighbors, measured in the full predecessor halo -/
namespace Hierarchy.DescentResetPeerJointRAM
open DescentDyadicSpan DescentSixParty.Chronology DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H P D O N w : ℕ}

/-- The previous roster uses old-host-major rows of arbitrary degree D.
The current four ports, the current live count and its dense-to-raw inverse
are all read from the same prior memory. -/
structure Sources where
  count : Bank
  inverse : Bank
  current : Bank
  prior : Bank

def radix (D : ℕ) := 2^Nat.clog 2 (D+2)
def outputBase (base P : ℕ) := base+3*span P
def jointBank (base H P : ℕ) (j : Fin 4) : Bank := ⟨outputBase base P+j.val*H,Nat.clog 2 H⟩
def endAddress (base H P : ℕ) := outputBase base P+4*H+span H

def table (base P j : ℕ) : Bank := ⟨base+j*span P,Nat.clog 2 P⟩
def field (width D f x : ℕ) := if f=0 then x/width else if f=1 then (x%width)*radix D else (x/width)*D
def literal (P width D a : ℕ) := field width D (a/span P) (a%span P)
def deck (w base P width D : ℕ) : NativePhase w :=
  let f:=literal P width D
  let n:=3*span P
  ⟨DescentStaticWordColumn.program w base f n,4+10*n,fun m=>DescentStaticWordColumn.image base f m n,
    DescentStaticWordColumn.cheap w base f n⟩

/-- Four range tests guard empty receivers, missing current ports and unused old
roots. The old address and scaled local shape are public functions of an
authenticated raw name. -/
def term (A : Sources) (base P O D v j : ℕ) : Expr :=
  let num:=Expr.lookup A.count (.lit 0)
  let here:=Expr.lookup A.inverse (.lit v)
  let twice:=Expr.op .add here here
  let there:=Expr.lookup A.current (.op .add (.op .add twice twice) (.lit j))
  let left:=Expr.lookup (table base P 0) here
  let right:=Expr.lookup (table base P 0) there
  let start:=Expr.lookup (table base P 2) here
  let shape:=Expr.lookup (table base P 1) there
  let port:=fun i : Fin D => Expr.lookup A.prior (.op .add start (.lit i.val))
  .branch .lt (.lit v) num (.branch .lt there (.lit P) (.branch .lt left (.lit O)
    (.branch .lt right (.lit O) (DescentClosedHaloChip.chip port left right shape) (.lit 0)) (.lit 0)) (.lit 0)) (.lit 0)

def row (A : Sources) (base H P O D a : ℕ) := term A base P O D (a%H) (a/H)
def writer (w base H P O D : ℕ) (A : Sources) : NativePhase w :=
  let e:=row A base H P O D
  let dst:=outputBase base P
  ⟨DescentFixedRowProgram.program w dst e (4*H),DescentFixedRowProgram.clock e (4*H),
    fun m=>DescentFixedRowProgram.image dst e m (4*H),DescentFixedRowProgram.cheap w dst (4*H) e⟩
def phase (w base H P O width D : ℕ) (A : Sources) : NativePhase w :=
  (deck w base P width D).seq (writer w base H P O D A)

structure Room (A : Sources) (base H P O D w : ℕ) : Prop where
  count : A.count.Fits w base
  inverse : A.inverse.Fits w base
  current : A.current.Fits w base
  prior : A.prior.Fits w base
  four : P*4≤A.current.size
  oldRows : O*D≤A.prior.size
  oldWidth : O<2^w
  newWidth : H<2^w
  stop : endAddress base H P<2^w

theorem table_fits (base H P : ℕ) {j : ℕ} (small : j<3) (roof : endAddress base H P<2^w) :
    (table base P j).Fits w (outputBase base P) := by
  have before : outputBase base P ≤ outputBase base P+4*H := Nat.le_add_right ..
  have last : outputBase base P+4*H ≤ endAddress base H P := Nat.le_add_right ..
  have lim := (before.trans last).trans_lt roof
  have up:=Nat.mul_le_mul_right (span P) small
  rw [Nat.succ_mul] at up
  have enough : base+j*span P+span P≤outputBase base P:=by dsimp [outputBase];omega
  exact ⟨span_pos _,(Nat.le_add_left ..).trans_lt (enough.trans_lt lim),enough⟩

theorem fits (A : Sources) (base H P O D v j : ℕ) (s : Room A base H P O D w) :
    (term A base P O D v j).Fits w (outputBase base P) := by
  have up (b : Bank) (f : b.Fits w base) : b.Fits w (outputBase base P):=
    ⟨f.1,f.2.1,f.2.2.trans (Nat.le_add_right ..)⟩
  have first:=table_fits base H P (j:=0) (by decide) s.stop
  have shape:=table_fits base H P (j:=1) (by decide) s.stop
  have offsets:=table_fits base H P (j:=2) (by decide) s.stop
  have ct:=up A.count s.count
  have inv:=up A.inverse s.inverse
  have now:=up A.current s.current
  have old:=up A.prior s.prior
  let here:=Expr.lookup A.inverse (.lit v)
  let twice:=Expr.op .add here here
  let dst:=Expr.lookup A.current (.op .add (.op .add twice twice) (.lit j))
  have first_ : here.Fits w (outputBase base P):=⟨inv,trivial⟩
  have twice_ : twice.Fits w (outputBase base P):=⟨first_,first_⟩
  have next_ : dst.Fits w (outputBase base P):=⟨now,⟨twice_,twice_⟩,trivial⟩
  refine ⟨trivial,⟨ct,trivial⟩,⟨next_,trivial,⟨⟨first,first_⟩,trivial,⟨⟨first,next_⟩,trivial,?_,trivial⟩,trivial⟩,trivial⟩,trivial⟩
  exact DescentClosedHaloChip.fits (fun _=>⟨old,⟨offsets,first_⟩,trivial⟩)
    ⟨first,first_⟩ ⟨first,next_⟩ ⟨shape,next_⟩

theorem any (base H P O width D : ℕ) (A : Sources) (m : Memory w) (s : Room A base H P O D w) :
    let p:=phase w base H P O width D A
    p.Runs m ∧ ∀a,a<base ∨ endAddress base H P≤a→p.image m a=m a := by
  intro p
  let q:=deck w base P width D
  let r := writer w base H P O D A
  have before : base ≤ outputBase base P := Nat.le_add_right ..
  have tableEnd : outputBase base P ≤ outputBase base P+4*H := Nat.le_add_right ..
  have writerEnd : outputBase base P+4*H ≤ endAddress base H P := Nat.le_add_right ..
  have last := writerEnd.trans_lt s.stop
  have decks : q.Runs m := by
    intro labels regs pubs machine
    exact DescentStaticWordColumn.mount base (3*span P) (literal P width D) m (tableEnd.trans_lt last) machine
  have writes : r.Runs (q.image m) := by
    intro labels regs pubs machine
    exact DescentFixedRowProgram.run (outputBase base P) (4*H) (row A base H P O D) (q.image m)
      (fun a _ => fits A base H P O D (a%H) (a/H) s) last machine
  refine ⟨NativePhase.seq_runs q r m (@decks) (@writes),?_⟩
  intro a outside
  have kept : r.image (q.image m) a=q.image m a :=
    DescentFixedRowProgram.frame (outputBase base P) (4*H) (row A base H P O D) (q.image m) a
      (outside.imp (fun h => h.trans_le before) (fun h => writerEnd.trans h))
  exact kept.trans (DescentStaticWordColumn.frame base (3*span P) (literal P width D) m a
    (outside.imp_right (fun h => (tableEnd.trans writerEnd).trans h)))

theorem field_read (base H P width D : ℕ) (m : Memory w) (roof : endAddress base H P<2^w) (f : Fin 3) (x : Fin P) :
    (table base P f.val).read ((deck w base P width D).image m) (x.val:Word w)=
      (field width D f.val x.val:Word w) := by
  have sx:=x.isLt.trans_le (span_ge P)
  have pi:=span_pos P
  have enough : f.val*span P+x.val<3*span P:=by
    have b:=Nat.mul_le_mul_right (span P) f.isLt
    rw [Nat.succ_mul] at b;omega
  have bankWord := bank_read (table base P f.val) ((deck w base P width D).image m) (i:=x.val)
    sx (table_fits base H P f.isLt roof)
  refine bankWord.trans ?_
  change DescentStaticWordColumn.image base _ m _ (base+f.val*span P+x.val)=_
  rw [Nat.add_assoc,DescentStaticWordColumn.read base _ _ m enough]
  have div : (f.val*span P+x.val)/span P=f.val:=by
    rw [Nat.mul_comm f.val _,Nat.mul_add_div pi,Nat.div_eq_of_lt sx,Nat.add_zero]
  have mod_ : (f.val*span P+x.val)%span P=x.val:=by
    rw [Nat.mul_comm f.val _,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt sx]
  simp only [literal,div,mod_]

def value (oldH width D : ℕ) (p : Fin oldH→Fin D→Option (Fin oldH)) (N : ℕ) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (v : Fin H) (j : Fin 4) :=
  if live:v.val<N then
    let raw:=name ⟨v.val,live⟩
    (now raw j).elim 0 fun z=>
      if both : raw.val/width<oldH ∧ z.val/width<oldH then
        DescentClosedHaloChip.value (p ⟨raw.val/width,both.1⟩) ⟨raw.val/width,both.1⟩
          ⟨z.val/width,both.2⟩ ((z.val%width)*radix D)
      else 0
  else 0

theorem extent (base H P : ℕ) : endAddress base H P≤base+5*H+6*P+4+H:=by
  have a:=span_le P
  have b:=span_le H
  dsimp [endAddress,outputBase]
  omega

theorem bank_fits (base H P : ℕ) (j : Fin 4) (room : endAddress base H P<2^w) :
    (jointBank base H P j).Fits w (endAddress base H P) ∧ H≤(jointBank base H P j).size := by
  have u:=Nat.mul_le_mul_right H j.isLt.le
  have enough : outputBase base P+j.val*H+span H≤endAddress base H P:=by dsimp [endAddress];omega
  exact ⟨⟨span_pos _,(Nat.le_add_left ..).trans_lt (enough.trans_lt room),enough⟩,span_ge _⟩

end
end Hierarchy.DescentResetPeerJointRAM

end OAI
