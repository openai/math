import OAI.Hierarchy.DescentPacketFactorShape
import OAI.Hierarchy.DescentRetainedTargetPlacementTariff
import OAI.Hierarchy.DescentRetainedControlTariff

namespace OAI
/-! # Actual packed scan rows and clipped tables in retained placement and donor routing -/
namespace Hierarchy.DescentPlacedInvoiceVolume
open DescentSIMDLookup DescentPackedZip ThreeFlat.Routing
open DescentResetRetainedPlacement
noncomputable section

theorem groups_fit {G A : ℕ} (ha : 0<A) : G≤chunks G A*A:=by
  have full:=Nat.div_add_mod (G+A-1) A
  have rest:=Nat.mod_lt (G+A-1) ha
  change G≤((G+A-1)/A)*A
  rw [Nat.mul_comm];omega

theorem chunks_bound {G A t : ℕ} (ha : 0<A) (fit : G≤t*A) : chunks G A≤t:=by
  apply Nat.lt_succ_iff.mp
  change (G+A-1)/A<t.succ
  apply (Nat.div_lt_iff_lt_mul ha).mpr
  rw [Nat.succ_mul];omega

theorem pieces_price (G A B a h : ℕ) (ha : 0<A) (limA : A≤h) (limB : B≤h)
    (width : a*A≤h/2) :
    (Overlap.pieces G A B+1)*(A+1)*2^(a*A)≤2*((h+1)^3*2^(h/2)):=by
  have fit : B≤B*A:=Nat.le_mul_of_pos_right _ ha
  have b:Overlap.pieces G A B≤h+1:=(min_le_right ..).trans (Nat.add_le_add_right ((chunks_bound ha fit).trans limB) _)
  have t : (Overlap.pieces G A B+1)*(A+1)*2^(a*A)≤(h+2)*(h+1)*2^(h/2):=by
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right b 1) (Nat.add_le_add_right limA 1))
      (Nat.pow_le_pow_right (by decide) width)
  apply t.trans
  ring_nf
  omega

private theorem rounded (n : ℕ) : 2^Nat.clog 2 n≤2*n+1:=by
  by_cases small : n≤1
  · interval_cases n <;> decide
  have low:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
  have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
  cases eqn : Nat.clog 2 n with
  | zero=>omega
  | succ j=>rw [eqn] at low;simp only [Nat.pred_succ] at low;rw [Nat.pow_succ];omega

theorem projection (N H G X a A M h T : ℕ) (ha : 0<A) (hm : 0<M) (hx : 0<X)
    (limA : A≤h) (limB : M*X≤h) (source : a*A≤h/2) (dest : (a*X)*M≤h/2)
    (original : H*chunks (G*X) A≤T) (position : H*chunks G M≤T)
    (shelf : (h+1)^3*2^(h/2)≤T) :
    DescentResetStemProject.volume N H G X a A M≤volumeFactor N X*(T+1):=by
  have p:=pieces_price (G*X) A (M*X) a h ha limA limB source
  have scaled : chunks (G*X) (M*X)≤chunks G M:=by
    apply chunks_bound (Nat.mul_pos hm hx)
    calc
      G*X≤(chunks G M*M)*X:=Nat.mul_le_mul_right _ (groups_fit hm)
      _=_:=Nat.mul_assoc ..
  have last:H*chunks (G*X) (M*X)≤T:=(Nat.mul_le_mul_left H scaled).trans position
  have lut : 2^((a*X)*M)≤T:=(Nat.pow_le_pow_right (by decide) dest).trans
    ((Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans shelf)
  unfold DescentResetStemProject.volume Overlap.rows DescentVectorBookReshape.dictionaryWords DescentVectorBookReshape.rows
  dsimp only
  rw [Nat.mul_assoc N H,Nat.mul_assoc N H,Nat.mul_one H]
  apply le_trans (b:=N+N*T+N*T+2*T+X*T+N*(X*T)+T+1)
  · have overlap_bound := p.trans (Nat.mul_le_mul_left 2 shelf)
    repeat first | assumption | exact le_rfl | apply Nat.add_le_add | apply Nat.mul_le_mul_left
  · unfold volumeFactor;ring_nf;omega

structure ScanRoom (v : Chart) (b : Batch) (h T : ℕ) : Prop where
  oldPos : 0<b.inputLanes
  newPos : 0<v.lanes
  blocks : 0<v.blocks
  oldPitch : b.inputLanes≤h
  newPitch : v.lanes*v.blocks≤h
  oldWord : b.bits*b.inputLanes≤h/2
  newWord : b.bits*v.blocks*v.lanes≤h/2
  oldRows : v.oldHosts*chunks (v.groups*v.blocks) b.inputLanes≤T
  remixed : v.oldHosts*chunks v.groups v.lanes≤T
  oldHosts : v.oldHosts≤T
  newRows : v.rows≤T
  tables : (h+1)^3*2^(h/2)≤T

def stemFactor (N X U : ℕ) :=4096*volumeFactor N X+4+N*(4+(2*U+4))+7*(15+N*(11+4*U))
theorem stem (v : Chart) (b : Batch) (h T U : ℕ) (r : ScanRoom v b h T) :
    v.stemInvoice b U≤ stemFactor b.fields v.blocks U*(T+1):=by
  have p:=projection b.fields v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes h T r.oldPos r.newPos r.blocks
    r.oldPitch r.newPitch r.oldWord r.newWord r.oldRows r.remixed r.tables
  unfold Chart.stemInvoice
  apply le_trans (b:=4096*(volumeFactor b.fields v.blocks*(T+1))+
    (4+b.fields*(4+T*(2*U+4)))+7*(15+b.fields*(11+4*U)))
  · gcongr;exact r.oldRows
  · unfold stemFactor;ring_nf;omega

def suffixFactor (S N X : ℕ) :=2*(4+10*(6+2*S)+7*(15*(7+2*S)))+
  4+N*X*(4+(2*(19+26*24)+4))+7*(15+N*X*(11+4*(19+26*24)))

private theorem suffix (S N X T routeCells dirCells rows : ℕ)
    (a : routeCells≤(6+2*S)*(T+1)) (b : dirCells≤(6+2*S)*(T+1)) (c : rows≤T) :
    (4+10*routeCells+7*(15*(routeCells+1)))+(4+10*dirCells+7*(15*(dirCells+1)))+
    (4+N*X*(4+rows*(2*(19+26*24)+4)))+7*(15+N*X*(11+4*(19+26*24)))≤
    suffixFactor S N X*(T+1):=by
  apply le_trans (b:=2*(4+10*((6+2*S)*(T+1))+7*(15*((6+2*S)*(T+1)+1)))+
      (4+N*X*(4+T*(2*(19+26*24)+4)))+7*(15+N*X*(11+4*(19+26*24))))
  · rw [two_mul]; gcongr; omega
  · unfold suffixFactor;ring_nf;omega

private theorem routes (v : Chart) (b : Batch) (h T : ℕ) (r : ScanRoom v b h T) :
    2^Nat.clog 2 (v.sparse*v.parts+1)≤(6+2*v.shapes)*(T+1) ∧
    2*2^Nat.clog 2 v.rows+2^Nat.clog 2 v.sparse≤(6+2*v.shapes)*(T+1):=by
  have a:v.sparse*v.parts=v.shapes*(v.oldHosts*chunks v.groups v.lanes):=by unfold Chart.sparse Chart.parts;ring
  have c:v.sparse≤T*v.shapes:=Nat.mul_le_mul_right _ r.oldHosts
  have m:=rounded (v.sparse*v.parts+1)
  have n:=rounded v.rows
  have k:=rounded v.sparse
  have f: v.sparse*v.parts≤v.shapes*T:=by rw [a];exact Nat.mul_le_mul_left _ r.remixed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,rows,_⟩:=r
  constructor <;> nlinarith

private theorem invoice_add (a b c d T : ℕ) (h₁ : a≤c*(T+1)) (h₂ : b≤d*(T+1)) :
    a+b≤(c+d)*(T+1):=by rw [Nat.add_mul];exact Nat.add_le_add h₁ h₂

theorem placement (v : Chart) (b : Batch) (h T U : ℕ) (r : ScanRoom v b h T) :
    v.invoice b U≤(stemFactor b.fields v.blocks U+suffixFactor v.shapes b.fields v.blocks)*(T+1):=by
  have ⟨a,c⟩:=routes v b h T r
  have post:=suffix v.shapes b.fields v.blocks T (v.route b 0).size (v.dir b 0).size v.rows a c r.newRows
  simpa only [Chart.invoice,Nat.add_assoc] using
    (invoice_add _ _ _ _ T (stem v b h T U r) post)

theorem target (v : Chart) (b : Batch) (h T U : ℕ) (r : ScanRoom v b h T) :
    DescentRetainedTargetPlacement.Chart.invoice v b U≤
    (stemFactor (b.fields*v.shapes) v.blocks U+suffixFactor v.shapes b.fields v.blocks)*(T+1):=by
  let wide:=DescentRetainedTargetPlacement.Chart.expanded v b
  have ⟨a,c⟩:=routes v b h T r
  have post:=suffix v.shapes b.fields v.blocks T (DescentRetainedTargetPlacement.Chart.route v b 0).size
    (DescentRetainedTargetPlacement.Chart.dir v b 0).size v.rows a c r.newRows
  simpa only [wide,DescentRetainedTargetPlacement.Chart.expanded,DescentRetainedTargetPlacement.Chart.invoice,Nat.add_assoc] using
    (invoice_add _ _ _ _ T (stem v wide h T U ⟨r.oldPos,r.newPos,r.blocks,r.oldPitch,r.newPitch,
      r.oldWord,r.newWord,r.oldRows,r.remixed,r.oldHosts,r.newRows,r.tables⟩) post)

end
end Hierarchy.DescentPlacedInvoiceVolume

end OAI
