import OAI.Hierarchy.DescentOrdinaryRankKeys
import OAI.Hierarchy.DescentOrdinaryRankSweep

namespace OAI
/-! The five numeric donor ranks are the outputs of the one fixed sweep of
all original path queries, including the complete final padded group word. -/
namespace Hierarchy.DescentOrdinaryRankSweep
open DescentSIMDLookup DescentSharedCableNames DescentHaloWalkRAM DescentParallelBase.ParentFilter DescentPackedColony DescentPackedZip
open DescentOrdinaryDonorRankDirectory DescentOrdinaryDonorSources
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {M H G D Q K L a b w mset :ℕ} (R:Fin H→Fin D→Option (Fin H))
local notation "P" => breadth D
local notation "J" => mset*5
def item (u:Fin mset) (i:Fin 5):Fin J:=finProdFinEquiv (u,i)
def projection (T:Tables) (path:Fin mset→Expr) (endpoint:Fin mset→Bool→Expr) (dir:Field→Bank):Chart J where
  directory j:=dir (tag (finProdFinEquiv.symm j).2)
  query j:=let p:Fin mset×Fin 5:=finProdFinEquiv.symm j
           T.read (path p.1) (endpoint p.1 (PathKeys.side p.2))

theorem issued (base rowBits:ℕ) (T:Tables) (path:Fin mset→Expr) (endpoint:Fin mset→Bool→Expr) (dir:Field→Bank)
    (raw:Fin mset→Fin H→Fin G→Option (Fused.Raw R Q K L b))
    (m:Memory w) (wide:P*P<2^a) (fits:P*P<2^b) (valid:∀u h g,Correct R h (raw u h g))
    (sourcePath:Fin mset→Fin H→Fin G→Cell b) (ends:Fin mset→Bool→Fin H→Fin G→Cell b)
    (origin:∀u h g,(sourcePath u h g).val=PathKeys.issuedPath (raw u h g))
    (old:∀u s h g,(ends u s h g).val=PathKeys.selectedPath (raw u h g) s)
    (buckets:∀f,(dir f).base+H*(P*P)≤base)
    (words:∀f h j,m ((dir f).base+(h.val*(P*P)+j.val))=((directory R fits f h j).val:Word w))
    (static:Static T (PathKeys.merge P (a:=a) (b:=b)) M m)
    (keys:∀u i,Fits T (path u) (endpoint u (PathKeys.side i)) b b M base w)
    (ps:∀u,Source (path u) (sourcePath u) M m) (qs:∀u s,Source (endpoint u s) (ends u s) M m)
    (fit:Chart.Fitted (projection T path endpoint dir) base (P*P) a b M H G rowBits w)
    (space:Chart.roof (jobs:=J) base (P*P) a b M H G<2^w):
    let Z:=projection T path endpoint dir
    let done:=Chart.done Z base (P*P) a b M H G rowBits m
    (Chart.program Z base (P*P) a b M H G rowBits w).Exec m done (Chart.time Z base (P*P) a b M H G rowBits) ∧
    (∀u i,Reads (Chart.page base (P*P) a b M H G (item u i)) (fun h g=>geometry R fits (raw u h g) i) M done) ∧
    (∀v,v<base ∨ Chart.roof (jobs:=J) base (P*P) a b M H G≤v→done v=m v) ∧ CheapCode (Chart.program Z base (P*P) a b M H G rowBits w):=by
  intro Z done
  have main:=Chart.run Z base (P*P) a b M H G rowBits m fit space
  refine ⟨main.1,?_,main.2.2⟩
  let values (j:Fin J) :=directory R fits (tag (finProdFinEquiv.symm j).2)
  let queries (j:Fin J) (h:Fin H) (g:Fin G):Cell a:=
    let t:Fin mset×Fin 5:=finProdFinEquiv.symm j
    (key R (raw t.1 h g) t.2:ℕ)
  have keySource (j:Fin J): Source (Z.query j) (queries j) M m:=by
    obtain ⟨⟨u,i⟩,rfl⟩:=finProdFinEquiv.surjective j
    simpa only [Z,projection,queries,Equiv.symm_apply_apply] using PathKeys.packed R (raw u) i (sourcePath u) (ends u) (path u) (endpoint u) T base m wide (origin u) (old u) (keys u i) static (ps u) (qs u)
  have early (j:Fin J):(Z.query j).Fits w base:=by
    let t:Fin mset×Fin 5:=finProdFinEquiv.symm j
    have a₀:=keys t.1 t.2
    exact ⟨a₀.apply,a₀.right,a₀.shift,a₀.left⟩
  intro u i p
  have reading:=Chart.sourced Z base (P*P) a b M H G rowBits m fit space values queries
    (fun j=>buckets _) early (fun j=>words _) keySource (item u i) p
  have cell (h:Fin H) (g:Fin G):
      DescentPackedChildNeighbor.SIMD.lookup (values (item u i) h) (queries (item u i) h g) (List.finRange (P*P))=geometry R fits (raw u h g) i:=by
    have size:key R (raw u h g) i<2^a:=by
      cases rr:raw u h g with
      | none=>exact Nat.two_pow_pos a
      | some v=>
        change (PairRanks.pair _ _).val+1<2^a
        exact (Nat.succ_le_of_lt (Fin.isLt _)).trans_lt wide
    simp only [values, item, Equiv.symm_apply_apply]
    apply looked_up R fits _ _ i (valid u h g) _
    simp only [queries,Equiv.symm_apply_apply,Fin.val_cast_of_lt size]
  exact reading.trans (by simp only [cell])

end
end Hierarchy.DescentOrdinaryRankSweep

end OAI
