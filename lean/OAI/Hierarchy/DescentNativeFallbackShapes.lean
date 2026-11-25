import OAI.Hierarchy.DescentFallbackRankRAM
import OAI.Hierarchy.DescentIssuedTerminalId

namespace OAI
/-! # Sparse ROM queries from a measured old terminal to its candidate neighbor leaves -/

namespace Hierarchy.DescentNativeFallbackShapes
open DescentContacts DescentRosterOrder DescentFallbackShapeTable DescentIssuedTerminalId DescentFallbackLeafScan
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {Y cap w : ℕ}

structure Banks where
  depth : Bank
  offset : Bank
  row : Bank
  entry : Bank

def strides (r Y cap : ℕ) := (2^r*((Y+1)*(2*cap)), (Y+1)*(2*cap), 2*cap)

def address (S : Banks) (cap : ℕ) (d i rowExpr hub : Expr) (j : ℕ) : Expr :=
  .op .add (.op .add (.op .add (.lookup S.depth d) (.lookup S.offset i)) (.lookup S.row rowExpr))
    (.branch .eq hub (.lit 0) (.lit j) (.lit (cap+j)))

def query (S : Banks) (cap : ℕ) (d i rowExpr hub : Expr) (j : ℕ) :=
  Expr.lookup S.entry (address S cap d i rowExpr hub j)

structure Stored (S : Banks) (r D g f Y cap : ℕ) (m : Memory w) : Prop where
  depthRoom : r+1≤S.depth.size
  offsetRoom : 2^r≤S.offset.size
  rowRoom : Y+1≤S.row.size
  entryRoom : imageSize r Y cap≤S.entry.size
  wide : ∀b∈[S.depth,S.offset,S.row,S.entry], b.size<2^w
  depths : ∀i≤r,m (S.depth.base+i)=(i*(strides r Y cap).1:ℕ)
  offsets : ∀i<2^r,m (S.offset.base+i)=(i*(strides r Y cap).2.1:ℕ)
  rows : ∀i<Y+1,m (S.row.base+i)=(i*(strides r Y cap).2.2:ℕ)
  entries : ∀a < imageSize r Y cap,m (S.entry.base+a)=(table r D g f Y cap a:Word w)

theorem query_read (S : Banks) (r D g f : ℕ) (m : Memory w) (x : Word w)
    (d i rowExpr h : Expr) (z : Endpoint Y) (depth : z.1.1≤r) (valid : z.1.2<2^z.1.1)
    (hub : Bool) (j : Fin cap) (data : Stored S r D g f Y cap m) (pos : 0<w)
    (rd : d.eval m x=(z.1.1:Word w)) (ri : i.eval m x=(z.1.2:Word w))
    (rr : rowExpr.eval m x=(optionDigit z.2:Word w)) (rh : h.eval m x=(hub.toNat:Word w)) :
    (query S cap d i rowExpr h j.val).eval m x=(encode (localSlot (localShape r D g f z hub) j):Word w) := by
  have df:=lookup_nat S.depth m x d _ rd (lt_of_lt_of_le (Nat.lt_succ_of_le depth) data.depthRoom)
    (data.wide _ (by simp))
  have idBound:=valid.trans_le (Nat.pow_le_pow_right (by decide) depth)
  have off:=lookup_nat S.offset m x i _ ri (idBound.trans_le data.offsetRoom) (data.wide _ (by simp))
  have ro:=lookup_nat S.row m x rowExpr _ rr ((option_fit z.2).trans_le data.rowRoom) (data.wide _ (by simp))
  have nz : (1:Word w)≠0 := by
    intro eqn
    have v:=congrArg Fin.val eqn
    have wfit:=Nat.one_lt_two_pow pos.ne'
    simp [Nat.mod_eq_of_lt wfit] at v
  have ix : (address S cap d i rowExpr h j.val).eval m x=(index r z hub j:Word w) := by
    change (Expr.lookup S.depth d).eval m x+(Expr.lookup S.offset i).eval m x+
      (Expr.lookup S.row rowExpr).eval m x+(Expr.branch .eq h (.lit 0) (.lit j.val) (.lit (cap+j.val))).eval m x=_
    rw [df,off,ro,data.depths _ depth,data.offsets _ idBound,data.rows _ (option_fit z.2)]
    cases hub <;> simp [Expr.eval,DescriptorExpr.Comparison.test,rh,nz,index,cell,strides] <;> ring
  change (Expr.lookup S.entry _).eval m x=_
  rw [lookup_nat _ _ _ _ _ ix ((index_fit r z depth valid hub j).trans_le data.entryRoom)
    (data.wide _ (by simp)),data.entries _ (index_fit r z depth valid hub j),table_read _ _ _ _ _ depth valid]

end
end Hierarchy.DescentNativeFallbackShapes

end OAI
