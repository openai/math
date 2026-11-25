import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentScalarBookReshape
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Return the compactor's original donor ordinals to stored successor groups -/

namespace Hierarchy.DescentOrdinaryOriginReshape
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Layout where
  hosts : ℕ
  lows : ℕ
  groups : ℕ
  blocks : ℕ
  bits : ℕ
  lanes : ℕ

namespace Layout
variable (L : Layout)
local notation "H" => L.hosts
local notation "Q" => L.lows
local notation "J" => L.groups
local notation "r" => L.blocks
local notation "a" => L.bits
local notation "M" => L.lanes
def rows := H*chunks J M
def nextRows := (H*Q)*chunks J M
def raw (base : ℕ) : Bank := ⟨base,Nat.clog 2 (Q*L.rows)⟩
def transpose (base : ℕ) := base+(L.raw base).size
def out (base : ℕ) := DescentScalarBookReshape.output (L.transpose base) H Q J r a M
def returned (base : ℕ) (block : Fin r) : Bank :=
  ⟨DescentScalarBookReshape.dest H Q J M (L.out base) block,Nat.clog 2 L.nextRows⟩
def finish (base : ℕ) := L.out base+r*L.nextRows+2^Nat.clog 2 L.nextRows
def preparationWords := L.finish 0

theorem affine (base : ℕ) : L.finish base=base+L.preparationWords :=by
  simp [finish,out,preparationWords,DescentScalarBookReshape.output,transpose,raw,Bank.size,Nat.add_assoc]

def query (expr : Fin Q→Expr) (i : ℕ) : Expr := if inside : i<Q then expr ⟨i,inside⟩ else .lit 0
def scans (base : ℕ) (expr : Fin Q→Expr) :=
  DescentPackedFlowBatch.passes base L.rows L.rows (L.query expr) 0 Q
def program (w base : ℕ) (expr : Fin Q→Expr) :=
  (ProtocolRAM.program w (L.scans base expr)).seq
    (DescentScalarBookReshape.program H Q J r a M (L.transpose base) (L.out base) w (L.raw base))
def image {w} (base : ℕ) (expr : Fin Q→Expr) (m : Memory w) :=
  DescentScalarBookReshape.result H Q J r a M (L.transpose base) (L.out base) (L.raw base)
    (ProtocolRAM.result (L.scans base expr) m)
def ticks (base : ℕ) (expr : Fin Q→Expr) :=
  clock (L.scans base expr)+((4+10*DescentScalarBookReshape.cells H Q J r a M)+(4+r*L.nextRows*54))

theorem cheap (w base : ℕ) (expr : Fin Q→Expr) : CheapCode (L.program w base expr) :=
  cheap_seq (ProtocolRAM.program_cheap w (L.scans base expr))
    (cheap_seq (DescentStaticWordColumn.cheap w (L.transpose base) _ _)
      (scan_cheap w (L.out base) _ _))

def phase (base : ℕ) (expr : Fin Q→Expr) (w : ℕ) : NativePhase w :=
  ⟨L.program w base expr,L.ticks base expr,L.image base expr,L.cheap w base expr⟩

theorem allocation (base : ℕ) :
    base+Q*L.rows≤L.transpose base ∧ L.transpose base+DescentScalarBookReshape.cells H Q J r a M≤L.out base ∧
    L.out base+r*L.nextRows≤L.finish base :=by
  refine ⟨Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _,?_,Nat.le_add_right ..⟩
  exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

theorem room {w} (base : ℕ) (space : L.finish base<2^w) :
    DescentScalarBookReshape.Room H Q J r a M w (L.transpose base) (L.out base) (L.raw base) := by
  have ax:=L.allocation base
  have stop:=ax.2.2.trans_lt space
  apply DescentScalarBookReshape.arranged (L.transpose base) (L.raw base) _ (Nat.le_pow_clog (by decide) _) stop
  refine ⟨Nat.two_pow_pos _,?_,le_rfl⟩
  have t:L.transpose base≤L.out base:=(Nat.le_add_right ..).trans ax.2.1
  have b:(L.raw base).size≤L.transpose base:=Nat.le_add_left ..
  omega

theorem framed {w} (base : ℕ) (expr : Fin Q→Expr) (m : Memory w)
    (fits : ∀l,(expr l).Fits w base) (space : L.finish base<2^w) :
    (L.phase base expr w).Runs m ∧ ∀i, i < base ∨ L.finish base ≤ i → L.image base expr m i=m i :=by
  have ar:=L.allocation base
  have lo:L.transpose base≤L.out base:=(Nat.le_add_right ..).trans ar.2.1
  have low:base≤L.transpose base:=Nat.le_add_right ..
  have bound:=ar.2.2.trans_lt space
  have actual:=DescentPackedFlowBatch.execute base L.rows L.rows Q (L.query expr) m
    (fun j hj=>by simpa only [query,dite_eq_left hj] using fits ⟨j,hj⟩)
    (ar.1.trans_lt ((lo.trans (Nat.le_add_right ..)).trans_lt bound)) le_rfl
  let mid:=ProtocolRAM.result (L.scans base expr) m
  have exec : (DescentScalarBookReshape.program H Q J r a M (L.transpose base) (L.out base) w (L.raw base)).Exec
      mid (DescentScalarBookReshape.result H Q J r a M (L.transpose base) (L.out base) (L.raw base) mid)
      ((4+10*DescentScalarBookReshape.cells H Q J r a M)+(4+r*L.nextRows*54)) :=
    DescentScalarBookReshape.exec (L.transpose base) (L.out base) (L.raw base) mid (L.room base space)
  refine ⟨?_,?_⟩
  · intro P R K mach pc reg pub stop rom advice cfg raw enter same
    exact Procedure.Exec.then actual.1 exec mach pc reg pub stop rom advice cfg raw enter same
  intro i away
  have prior : mid i=m i :=by
    rcases away with lt|gt
    · exact actual.2.2 i lt
    · apply DescentPackedFlowBatch.above base L.rows L.rows (L.query expr) m 0 Q i le_rfl
      simp only [Nat.zero_add]
      omega
  have shelf:=DescentStaticWordColumn.frame (L.transpose base) (DescentScalarBookReshape.cells H Q J r a M)
    (DescentScalarBookReshape.words H Q J r a M) mid i
  let loaded:=DescentScalarBookReshape.mounted (L.transpose base) H Q J r a M mid
  let e:=DescentScalarBookReshape.expression (DescentScalarBookReshape.layout H Q J r a M (L.transpose base) (L.raw base))
  change ProtocolRAM.image (L.out base) (r*L.nextRows) e loaded i=m i
  rcases away with lt|gt
  · have outside : i<L.out base:=lt.trans_le (low.trans lo)
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ e loaded i (.inl outside)).trans
      ((shelf (.inl (lt.trans_le low))).trans prior)
  · have past : L.out base+r*L.nextRows ≤ i :=ar.2.2.trans gt
    have earlier:=shelf (.inr (ar.2.1.trans ((Nat.le_add_right ..).trans past)))
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ e loaded i (.inr past)).trans (earlier.trans prior)

theorem originReturned {w} (base : ℕ) (expr : Fin Q→Expr) (m : Memory w)
    (fits : ∀l,(expr l).Fits w base) (space : L.finish base<2^w) (hm : 0<M) (hr : 0<r)
    (x : Fin Q→Fin H→Fin (J*r)→Cell a) (source : ∀l,Source (expr l) (x l) (M*r) m) :
    ∀b : Fin r,Reads (L.returned base b) (DescentScalarBookReshape.book x b) M (L.image base expr m) :=by
  have ar:=L.allocation base
  have lo:L.transpose base≤L.out base:=(Nat.le_add_right ..).trans ar.2.1
  have bound:=ar.2.2.trans_lt space
  have actual:=DescentPackedFlowBatch.execute base L.rows L.rows Q (L.query expr) m
    (fun j hj=>by simpa only [query,dite_eq_left hj] using fits ⟨j,hj⟩)
    (ar.1.trans_lt ((lo.trans (Nat.le_add_right ..)).trans_lt bound)) le_rfl
  have aligned (l : Fin Q) (p : Row H (J*r) (M*r)) :
      ProtocolRAM.result (L.scans base expr) m (base+l.val*L.rows+(row H (J*r) (M*r) p).val)=((data (x l) p).val:Word w) :=by
    let j:=row H (J*r) (M*r) p
    have fitj:j.val<L.rows:=by simpa only [rows,chunks_group J M r hm hr] using j.isLt
    exact (actual.2.1 l ⟨j.val,fitj⟩).trans (by simpa only [query,dite_eq_left l.isLt,Fin.eta] using source l p)
  exact (DescentScalarBookReshape.run (L.transpose base) (L.out base) (L.raw base) _ x hm hr
    (L.room base space) aligned).2.1

theorem returned_fits {w} (base : ℕ) (b : Fin r) (space : L.finish base<2^w) :
    (L.returned base b).Fits w (L.finish base) ∧ L.nextRows≤(L.returned base b).size :=by
  have reach:=Nat.mul_le_mul_right L.nextRows (Nat.le_of_lt b.isLt)
  have high:(L.returned base b).base+(L.returned base b).size≤L.finish base:=by
    change L.out base+b.val*L.nextRows+2^Nat.clog 2 L.nextRows≤L.out base+r*L.nextRows+2^Nat.clog 2 L.nextRows
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (high.trans_lt space),high⟩,Nat.le_pow_clog (by decide) _⟩

end Layout
end
end Hierarchy.DescentOrdinaryOriginReshape

end OAI
