import OAI.Hierarchy.DescentDonorSourceReturnRAM
import OAI.Hierarchy.DescentHaloRebaseRAM
import OAI.Hierarchy.DescentPackedChildNeighborSIMDROM

namespace OAI
/-! # Three short digits identify the source's prior-role window without a wide halo LUT -/
namespace Hierarchy.DescentParallelBase.SourceReturn.Query
open DescentHaloWalkRAM DescentSharedCableNames DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D H Q G M w P : ℕ}
local notation "bits"=>Packed.bits
local notation "SIMD"=>DescentPackedChildNeighbor.SIMD.lookup

/-- Native shared endpoint lookup returns the actual short reverse path at
the old root, one candidate choice per packed lane. The input header comes
straight from `Rebase.run .path`, in its physical old-rack major order. -/
def route (R:Fin H→Fin D→Option (Fin H)) (v:Fin H) (i:Fin (breadth D)):Cell (bits (breadth D)):=
  ⟨Rebase.value R .path v i,(Nat.lt_succ_of_le (Rebase.value_le R .path v i)).trans_le (Nat.le_pow_clog (by decide) _)⟩

def packedRoute (R:Fin H→Fin D→Option (Fin H)) (v:Fin H) (q:Option (Fin (breadth D))):Cell (bits (breadth D)):=
  SIMD (route R v) (Packed.token q) (List.finRange (breadth D))

theorem at_path (R:Fin H→Fin D→Option (Fin H)) (v:Fin H) (p:Fin (breadth D)):(packedRoute R v (some p)).val=Rebase.value R .path v p:=by
  rw [packedRoute,DescentPackedChildNeighbor.SIMD.lookup_at _ _ p (show (Packed.token (some p)).val=p.val+1 from rfl),ite_eq_left (List.mem_finRange p)];rfl

theorem raw_reads (R:Fin H→Fin D→Option (Fin H)) (bank:Bank) (m:Memory w)
    (ordered:∀v p,m (bank.base+(DescentHaloWalkRAM.row v p).val)=(Rebase.value R .path v p:Word w)):
    ∀v p,m (bank.base+(v.val*breadth D+p.val))=((route R v p).val:Word w):=by
  intro v p
  have index : (DescentHaloWalkRAM.row v p).val = v.val * breadth D + p.val := by
    simp [DescentHaloWalkRAM.row, finProdFinEquiv_apply_val]; ring
  simpa only [index, route] using ordered v p

/-- First combine literal forward-path presence with its physical new-source
heap/pack digits, then append the checked return path produced above. -/
def forward (P Q:ℕ) (p:Cell (bits P)) (low:Cell (bits Q)):Cell (bits (P*Q)):=Packed.token (do
  let f←Packed.readToken P p
  if ok:low.val<Q then some (finProdFinEquiv (f,⟨low.val,ok⟩)) else none)

def finish (P Q:ℕ) (u:Cell (bits (P*Q))) (r:Cell (bits P)):Cell (bits (P*(Q*P))):=Packed.token (do
  let a←Packed.readToken (P*Q) u
  if ok:r.val<P then some (RAM.key (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 ⟨r.val,ok⟩) else none)

theorem certified (p:Fin P) (l:Fin Q) (r:Fin P) (lo:Cell (bits Q)) (back:Cell (bits P)) (eqLo:lo.val=l.val) (eqBack:back.val=r.val):
    finish P Q (forward P Q (Packed.token (some p)) lo) back=Packed.token (some (RAM.key p l r)):=by
  have lok:lo.val<Q:=eqLo.symm ▸ l.isLt;have rok:back.val<P:=eqBack.symm ▸ r.isLt
  have lowEq : (⟨lo.val,lok⟩ : Fin Q) = l := Fin.ext eqLo
  have revEq : (⟨back.val,rok⟩ : Fin P) = r := Fin.ext eqBack
  simp [forward, finish, Packed.token_back, lok, rok, lowEq, revEq]
  change Packed.token (some (RAM.key (finProdFinEquiv.symm (finProdFinEquiv (p,l))).1
    (finProdFinEquiv.symm (finProdFinEquiv (p,l))).2 r)) = _
  rw [Equiv.symm_apply_apply]

def expr (ts tr:Tables) (p low rev:Expr):=tr.read (ts.read p low) rev

theorem source (ts tr:Tables) (p low rev:Expr) (out:ℕ) (m:Memory w)
    (px:Fin H→Fin G→Cell (bits P)) (lx:Fin H→Fin G→Cell (bits Q)) (rx:Fin H→Fin G→Cell (bits P))
    (fit₁:DescentPackedZip.Fits ts p low (bits P) (bits Q) M out w)
    (fit₂:DescentPackedZip.Fits tr (ts.read p low) rev (bits (P*Q)) (bits P) M out w)
    (table₁:Static ts (forward P Q) M m) (table₂:Static tr (finish P Q) M m)
    (left:Source p px M m) (mid:Source low lx M m) (right:Source rev rx M m):
    Source (expr ts tr p low rev) (fun v g=>finish P Q (forward P Q (px v g) (lx v g)) (rx v g)) M m:=by
  have stage:=read_data ts p low out fit₁ (forward P Q) (by simp [forward,Packed.readToken,Packed.token]) m table₁ px lx left mid
  exact read_data tr _ rev out fit₂ (finish P Q) (by simp [finish,Packed.readToken,Packed.token]) m table₂ _ _ stage right

end
end Hierarchy.DescentParallelBase.SourceReturn.Query

end OAI
