import OAI.Hierarchy.DescentPackedWalshLocal
import OAI.Hierarchy.DescentPackedWalshTotalColumn

namespace OAI
/-! # One measured depth, from a retained integer Walsh spectrum to the central integer bank -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b c g w : ℕ}
local notation "k" => u+l

structure DepthShelf where
  weights : Weight.Header
  reduce : ℕ
  extract : ℕ
  first : ℕ
  out : ℕ

namespace DepthShelf
variable (D : DepthShelf) (P : Plan)

def code (w H u j : ℕ) : Procedure w :=
  (scan w D.first (H*2^u) (Weight.expr D.weights j)).seq
    (Column.publishCode P w D.reduce D.first D.extract D.out)

def clock (H u : ℕ) :=
  4+94*(H*2^u)+Column.publishTime P D.reduce D.first D.extract

def after (H u j : ℕ) (mem : Memory w) :=
  Column.publishMem P D.reduce D.first D.extract D.out (image D.first (H*2^u) (Weight.expr D.weights j) mem)

end DepthShelf

theorem measured_depth (D : DepthShelf) (h j : ℕ) (hc : 0<c) (mem rom : Memory w)
    (lev : Fin H→ℕ) (gain : Fin H→Cell g) (x : Fin H→DescentGL.Bits k→ℕ)
    (B : ℕ) (bound : ∀v a,x v a≤B) (precision : 2^(3*k)*B^2<2^b)
    (lanes : laneBits k h c=l) (bnd : ∀v,lev v<2^w) (jBound : j<2^w)
    (room : Weight.Room D.weights D.first H u l b g w) (header : Weight.Fixed D.weights u l b c g H mem)
    (levels : ∀v,mem (D.weights.depth.base+v.val)=(lev v:Word w))
    (gains : ∀v,mem (D.weights.gain.base+v.val)=((gain v).val:Word w))
    (num : Installed D.weights.numer.base (spectrum (b:=b) x) mem)
    (paid : ∀v d,bill j lev gain x v d<2^c) :
    let P:=reduction H u l c h hc
    let t:=P.depth
    let dig:=P.bits+t
    let low:=P.laneBits t
    let permutation:=centralOrder u l
    P.headerAt D.reduce t≤D.first → D.extract+Column.size k dig low≤D.first →
    P.dataAt D.first (t+1)≤D.out → D.out+2^k<2^w → h≤w → dig≤w →
    (∀a,D.reduce≤a→a<P.headerAt D.reduce t→mem a=P.mount D.reduce rom t a) →
    (∀a<Column.size k dig low,mem (D.extract+a)=Column.fixedRow
      (Column.chunkAt P ∘permutation) (Column.laneAt P ∘permutation) dig a) →
    let dst:=D.after P H u j mem
    (D.code P w H u j).Exec mem dst (D.clock P H u) ∧
      (∀i : Fin (2^k),dst (D.out+i.val)=((∑v,bill j lev gain x v (permutation i)):Word w)) ∧
      (∀z<D.first,dst z=mem z) ∧ ∀z,D.out+2^k≤z→dst z=mem z := by
  dsimp only
  intro rootEnd selectorEnd later endBound width word reductionHeader selector
  let P:=reduction H u l c h hc
  obtain ⟨go,seed,unchanged,future⟩:=real_weight_seed D.weights h D.first j hc mem lev gain x B bound
    precision lanes bnd jBound room header levels gains num
  have previous:=Column.collected P D.reduce D.first D.extract D.out _ rom (bill j lev gain x) paid
    (centralOrder u l) rootEnd selectorEnd later endBound width word
    (fun a ha hEnd=>(unchanged a (hEnd.trans_le rootEnd)).trans (reductionHeader a ha hEnd))
    (fun a ha=>(unchanged _ ((Nat.add_lt_add_left ha D.extract).trans_le selectorEnd)).trans
      (selector a ha)) seed
  obtain ⟨next,atEnd,lower,upper⟩:=previous
  have scope : D.first+H*2^u≤D.out := by
    have initial := P.real_le
    have eqLow : P.laneBits 0=l:=by simpa only [P,reduction,Plan.laneBits,Nat.add_zero,laneBits] using lanes
    have numChunks : P.chunks 0=2^u:=by
      change 2^((u+l)-P.laneBits 0)=2^u
      rw [eqLow,Nat.add_sub_cancel]
    have step := (P.data_mono D.first (show 1≤P.depth+1 by omega)).trans later
    change D.first+P.hosts 0*P.chunks 0≤D.out at step
    rw [numChunks] at step
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right (2^u) initial) D.first).trans step
  refine ⟨?_,atEnd,fun z hz=>(lower z hz).trans (unchanged z hz),
    fun z hz=>(upper z hz).trans (future z (scope.trans ((Nat.le_add_right D.out (2^k)).trans hz)))⟩
  intro pc reg ports machine
  exact Procedure.Exec.then go next machine

end
end Hierarchy.DescentPackedWalsh

end OAI
