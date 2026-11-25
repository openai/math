import OAI.Hierarchy.DescentOrdinaryDonorSources
import OAI.Hierarchy.DescentOrdinaryDonorPathWord
import OAI.Hierarchy.DescentParentFilterSource

namespace OAI
/-! The two original one-based path words are the only selector bits for
all five geometric fields in an ordinary donor. A zero gate stays absent. -/
namespace Hierarchy.DescentOrdinaryDonorSources.PathKeys
open DescentSIMDLookup DescentSharedCableNames DescentHaloWalkRAM DescentParallelBase.ParentFilter DescentPackedZip
open DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D H Q K L b M G a w:ℕ} {R : Fin H→Fin D→Option (Fin H)}
local notation "P" => breadth D

def selectedPath (r:Option (Fused.Raw R Q K L b)) (side:Bool):ℕ:=
  r.elim 0 (fun x=>(if side then x.parent.dst.path else x.parent.src.path).val+1)

def issuedPath (r:Option (Fused.Raw R Q K L b)):ℕ:=r.elim 0 (fun x=>x.path.val)

def merge (radix:ℕ) (p:Cell b) (q:Cell b):Cell a:=if q.val=0 then 0 else (p.val*radix+q.val:ℕ)
theorem missing :merge P (0:Cell b) (0:Cell b)=(0:Cell a):=by simp [merge]

def side (i:Fin 5):Bool:=decide (i.val=2 ∨ i.val=4)

/-- The emitted path word of the original donor is definitionally the source
socket of the true physically programmed parent, on both signs. -/
theorem programmed_path {k g slots:ℕ} (pos:0<slots) (trace:DescentPacking.PackedMatch.Local.Walk×DescentPacking.PackedMatch.Local.Walk)
    (hs ht up:Bool) (ticket:Fin K) (mass:Fin (L+1)) (z:Fused.Raw R (2^(k+1)*slots) K L b)
    (parent:z.parent=programmed (k:=k) (g:=g) pos trace hs ht up ticket mass) (right:Bool):
    (DescentPacking.PackedMatch.Local.ParentIncidence.pathCell D right (some trace)).val=selectedPath (some z) right:=by
  cases right <;> simp [selectedPath,parent,programmed,printed,DescentPacking.PackedMatch.Local.ParentIncidence.pathCell]

theorem absent_path (right:Bool):
    (DescentPacking.PackedMatch.Local.ParentIncidence.pathCell D right none).val=selectedPath (R:=R) (none:Option (Fused.Raw R Q K L b)) right:=rfl

theorem value (R:Fin H→Fin D→Option (Fin H)) (r:Option (Fused.Raw R Q K L b)) (i:Fin 5) (p q:Cell b)
    (prev:p.val=issuedPath r) (endpoint:q.val=selectedPath r (side i)) (size:P*P<2^a):
    (merge P p q:Cell a).val=key R r i:=by
  cases r with
  | none=>simp [selectedPath] at endpoint;simp [key,merge,endpoint]
  | some z=>
    let x:=if i.val=2 ∨ i.val=4 then z.parent.dst.path else z.parent.src.path
    have qp:q.val=x.val+1:=by simpa [x,selectedPath,side] using endpoint
    have path:p.val=z.path.val:=prev
    have bound:(PairRanks.pair z.path x).val+1<2^a:=(Nat.succ_le_of_lt (PairRanks.pair z.path x).isLt).trans_lt size
    have val:(PairRanks.pair z.path x).val=z.path.val*P+x.val:=by simp [PairRanks.pair,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    rw [val] at bound
    have positive : q.val ≠ 0 := by omega
    unfold merge
    rw [ite_eq_right positive]
    change ((↑(p.val*P+q.val) : Cell a).val) = (PairRanks.pair z.path x).val+1
    rw [path, qp, val, ←Nat.add_assoc, Fin.val_cast_of_lt bound]

def width (b M:ℕ):=(b+b)*M
def pages (D a b M:ℕ):=binary (merge (breadth D) (a:=a) (b:=b)) M
def table (base D a b M:ℕ):=joined (pages D a b M) (width b M) base id
def endAddress (base b M:ℕ):=base+2*2^width b M

theorem setup (base D a b M:ℕ) (m:Memory w) (room:endAddress base b M<2^w):
    let f:=pages D a b M;let wd:=width b M;let mid:=after f wd base m
    (mount f wd w base).Exec m mid (4+10*(2*2^wd)) ∧ Static (table base D a b M) (merge (breadth D) (b:=b) (a:=a)) M mid ∧
    (∀u,u<base ∨ endAddress base b M≤u→mid u=m u) ∧ CheapCode (mount f wd w base):=by
  intro f wd mid
  refine ⟨(run f wd base m room).1,binary_mounted _ M f wd base m ?_ id (fun _=>rfl),frame f wd base m,@cheap _ f wd w base⟩
  intro j;fin_cases j <;> change _*M≤_*M <;> apply Nat.mul_le_mul_right <;> omega

theorem packed {hosts:ℕ} (R:Fin H→Fin D→Option (Fin H)) (raw:Fin hosts→Fin G→Option (Fused.Raw R Q K L b)) (i:Fin 5)
    (av:Fin hosts→Fin G→Cell b) (qv:Bool→Fin hosts→Fin G→Cell b) (aa:Expr) (qq:Bool→Expr)
    (T:Tables) (out:ℕ) (m:Memory w) (wide:P*P<2^a)
    (good:∀v g,(av v g).val=issuedPath (raw v g)) (endpoints:∀s v g,(qv s v g).val=selectedPath (raw v g) s)
    (valid:Fits T aa (qq (side i)) b b M out w) (fixed:Static T (merge P (b:=b) (a:=a)) M m)
    (pa:DescentPackedZip.Source aa av M m) (pq:∀s,DescentPackedZip.Source (qq s) (qv s) M m):
    DescentPackedZip.Source (T.read aa (qq (side i))) (fun v g=>(key R (raw v g) i:Cell a)) M m:=by
  have answer (v g):merge P (av v g) (qv (side i) v g)=(key R (raw v g) i:Cell a):=by
    have numer:=value R (raw v g) i (av v g) (qv (side i) v g) (good v g) (endpoints _ v g) wide
    apply Fin.ext
    rw [←numer,Fin.val_cast_of_lt (merge P (av v g) (qv (side i) v g):Cell a).isLt]
  simpa only [answer] using read_data T aa (qq (side i)) out valid (merge P (a:=a)) missing m fixed av (qv (side i)) pa (pq (side i))

end
end Hierarchy.DescentOrdinaryDonorSources.PathKeys

end OAI
