import OAI.Hierarchy.DescentPackedMatchProfileTable
import OAI.Hierarchy.DescentPackedProfileCursor
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Resolving all lane-local profile references in one native two-word lookup per chunk -/

namespace Hierarchy.DescentPacking.PackedMatch.ProfileTable
open DescentSIMDLookup DescentPackedProfileWindow ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

structure Tables where
  topology : Bank
  offset : Bank
  low : Bank
  result : Bank

def programExpr (T : Tables) (topo raw : Bank) (ptr remainder : Expr) : Expr :=
  let top := Expr.lookup T.topology (.lookup topo .row)
  let off := Expr.lookup T.offset remainder
  let lo := Expr.lookup T.low (.lookup raw ptr)
  let hi := Expr.lookup raw (.op .add ptr (.lit 1))
  .lookup T.result (.op .add top (.op .add off (.op .add lo hi)))

def pointer (c : Bank) : Expr := .lookup c (.op .add .row .row)
def rem_ (c : Bank) : Expr := .lookup c (.op .add (.op .add .row .row) (.lit 1))

def static (s : Shape) (M R : ℕ) (T : Tables) (m : Memory w) : Prop :=
  let a:=s.outputBits*M
  let b:=s.digit*R
  (∀x : Cell a,m (T.topology.base+x.val)=((2^(b+(b+b))*x.val:ℕ):Word w)) ∧
  (∀v : Cell b,m (T.offset.base+v.val)=((2^(b+b)*v.val:ℕ):Word w)) ∧
  (∀x : Cell b,m (T.low.base+x.val)=((2^b*x.val:ℕ):Word w)) ∧
  ∀k : Cell (bits a b),m (T.result.base+k.val)=((table s M R k).val:Word w)

structure Fits (s : Shape) (M R n w out : ℕ) (T : Tables) (topo raw : Bank) (ptr rem_ : Expr) : Prop where
  topology : T.topology.Fits w out
  offset : T.offset.Fits w out
  low : T.low.Fits w out
  result : T.result.Fits w out
  source : topo.Fits w out
  tape : raw.Fits w out
  quotient : ptr.Fits w out
  remainder : rem_.Fits w out
  groups : n≤topo.size
  keyT : T.topology.bits=s.outputBits*M
  keyO : T.offset.bits=s.digit*R
  keyL : T.low.bits=s.digit*R
  keyR : T.result.bits=bits (s.outputBits*M) (s.digit*R)
  space : out+n<2^w

theorem read (s : Shape) {M R n out : ℕ} (T : Tables) (topo raw : Bank) (ptr rem_ : Expr)
    (r : Fits s M R n w out T topo raw ptr rem_) (m : Memory w) (fixed : static s M R T m)
    (i : Fin n) (key : Cell (s.outputBits*M)) (offset : Fin R) (origin : ℕ) (lo hi : Cell (s.digit*R))
    (grain : R≤2^(s.digit*R)) (source : m (topo.base+i.val)=(key.val:Word w))
    (position : ptr.eval m (i.val:Word w)=(origin:Word w)) (remainder : rem_.eval m (i.val:Word w)=(offset.val:Word w))
    (onTape : origin+1<raw.size) (left : m (raw.base+origin)=(lo.val:Word w))
    (right : m (raw.base+(origin+1))=(hi.val:Word w)) :
    (programExpr T topo raw ptr rem_).eval m (i.val:Word w)=
      ((localProfile s.digit s.pairs M R (laneCounts s M key) offset lo hi).val:Word w) := by
  let b:=s.digit*R
  let o : Cell b := ⟨offset.val,offset.isLt.trans_le grain⟩
  let z:=ProfileTable.key key o lo hi
  have a : key.val<T.topology.size := by simpa only [Bank.size,r.keyT] using key.isLt
  have e : o.val<T.offset.size := by simpa only [Bank.size,r.keyO] using o.isLt
  have low : lo.val<T.low.size := by simpa only [Bank.size,r.keyL] using lo.isLt
  have end_ : z.val<T.result.size := by simpa only [Bank.size,r.keyR] using z.isLt
  have off : rem_.eval m (i.val:Word w)=(o.val:Word w) := remainder
  have highRead : raw.read m ((origin : Word w) + ((1 : ℕ) : Word w)) = (hi.val : Word w) := by
    calc
      raw.read m ((origin : Word w) + ((1 : ℕ) : Word w)) =
          raw.read m ((origin + 1 : ℕ) : Word w) :=
        congrArg (raw.read m) (Nat.cast_add origin 1).symm
      _ = m (raw.base + (origin + 1)) := DescentPackedZip.bank_read raw m onTape r.tape
      _ = (hi.val : Word w) := right
  have address :
      ((2^(b+(b+b))*key.val:ℕ):Word w)+
        (((2^(b+b)*o.val:ℕ):Word w)+(((2^b*lo.val:ℕ):Word w)+(hi.val:Word w)))=(z.val:Word w) := by
    rw [show z.val=_ from key_val key o lo hi]
    simp only [Nat.cast_add]
  simp only [programExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,position,off]
  rw [DescentPackedZip.bank_read topo m (i.isLt.trans_le r.groups) r.source,source,
    DescentPackedZip.bank_read T.topology m a r.topology,fixed.1 key,
    DescentPackedZip.bank_read T.offset m e r.offset,fixed.2.1 o,
    DescentPackedZip.bank_read raw m (Nat.lt_of_succ_lt onTape) r.tape,left,
    DescentPackedZip.bank_read T.low m low r.low,fixed.2.2.1 lo,
    highRead,address,
    DescentPackedZip.bank_read T.result m end_ r.result,fixed.2.2.2 z]
  exact congrArg (fun p : Cell (s.digit*(M*s.pairs))=>(p.val:Word w)) (decode s M R key o lo hi offset.isLt)

theorem exec (s : Shape) {M R n out : ℕ} (T : Tables) (topo raw : Bank) (ptr rem_ : Expr)
    (r : Fits s M R n w out T topo raw ptr rem_) (m : Memory w) :
    let e:=programExpr T topo raw ptr rem_
    (scan w out n e).Exec m (image out n e m) (4+n*(2*e.work+4)) ∧ CheapCode (scan w out n e) := by
  have fit : (programExpr T topo raw ptr rem_).Fits w out :=
    ⟨r.result,⟨r.topology,r.source,trivial⟩,⟨r.offset,r.remainder⟩,⟨r.low,r.tape,r.quotient⟩,r.tape,r.quotient,trivial⟩
  exact ⟨scan_exec _ _ _ _ fit r.space,@scan_cheap _ _ _ _⟩

theorem work (T : Tables) (topo raw c : Bank) :
    (programExpr T topo raw (pointer c) (rem_ c)).work=74 := rfl

end
end Hierarchy.DescentPacking.PackedMatch.ProfileTable

end OAI
