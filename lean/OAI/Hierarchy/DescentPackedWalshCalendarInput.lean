import OAI.Hierarchy.DescentPackedWalshCalendar
import OAI.Hierarchy.DescentPackedWalshCanonical

namespace OAI
/-! # One shared set of physical measurement inputs throughout the complete depth issuer -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b c g w : ℕ}
local notation "k" => u+l

structure DepthInput (D : DepthShelf) (limit h b c g : ℕ) (hc : 0<c)
    (lev : Fin H→ℕ) (gain : Fin H→Cell g) (x : Fin H→DescentGL.Bits k→ℕ)
    (mem rom : Memory w) : Prop where
  weights : Weight.Room D.weights D.first H u l b g w
  ports : ∀A∈[D.weights.owner,D.weights.depth,D.weights.gain,D.weights.shift,D.weights.numer,D.weights.results],
    A.base+A.size≤limit
  fixed : Weight.Fixed D.weights u l b c g H mem
  levels : ∀v,mem (D.weights.depth.base+v.val)=(lev v:Word w)
  gains : ∀v,mem (D.weights.gain.base+v.val)=((gain v).val:Word w)
  spectrum : Installed D.weights.numer.base (DescentPackedWalsh.spectrum (b:=b) x) mem
  reductionEnd : let P:=reduction H u l c h hc; P.headerAt D.reduce P.depth≤limit
  extractEnd : let P:=reduction H u l c h hc;D.extract+Column.size k (c+P.depth) (P.laneBits P.depth)≤limit
  beforeOutput : let P:=reduction H u l c h hc;P.dataAt D.first (P.depth+1)≤D.out
  outputRoom : D.out+2^k<2^w
  reducePins : let P:=reduction H u l c h hc;∀a,D.reduce≤a→a<P.headerAt D.reduce P.depth→
    mem a=P.mount D.reduce rom P.depth a
  orderPins : let P:=reduction H u l c h hc;
    ∀a<Column.size k (c+P.depth) (P.laneBits P.depth),mem (D.extract+a)=Column.fixedRow
      (Column.chunkAt P ∘centralOrder u l) (Column.laneAt P ∘centralOrder u l) (c+P.depth) a

theorem DepthInput.inherit {D : DepthShelf} {limit h : ℕ} {hc : 0<c} {lev : Fin H→ℕ} {gain : Fin H→Cell g}
    {x : Fin H→DescentGL.Bits k→ℕ} {mem rom cur : Memory w}
    (A : DepthInput D limit h b c g hc lev gain x mem rom) (low : ∀z<limit,cur z=mem z) :
    DepthInput D limit h b c g hc lev gain x cur rom := by
  have read (S : Bank) (belongs : S∈[D.weights.owner,D.weights.depth,D.weights.gain,D.weights.shift,
      D.weights.numer,D.weights.results]) (v : ℕ) (fits : v<S.size) : cur (S.base+v)=mem (S.base+v) :=
    low _ ((Nat.add_lt_add_left fits _).trans_le (A.ports S belongs))
  refine ⟨A.weights,A.ports,?_,?_,?_,?_,A.reductionEnd,A.extractEnd,A.beforeOutput,A.outputRoom,?_,?_⟩
  · constructor
    · intro v p
      exact (read _ (by simp) _ ((row v p).isLt.trans_le A.weights.groups.1)).trans (A.fixed.owner v p)
    · intro a
      exact (read _ (by simp) _ (a.isLt.trans_le A.weights.gainKey)).trans (A.fixed.shift a)
    · intro a
      exact (read _ (by simp) _ (a.isLt.trans_le A.weights.resultKey)).trans (A.fixed.result a)
  · intro v;exact (read _ (by simp) _ (v.isLt.trans_le A.weights.hosts.1)).trans (A.levels v)
  · intro v;exact (read _ (by simp) _ (v.isLt.trans_le A.weights.hosts.2)).trans (A.gains v)
  · intro v p
    exact (read _ (by simp) _ ((row v p).isLt.trans_le A.weights.groups.2)).trans (A.spectrum v p)
  · dsimp only
    intro a lo hi
    exact (low _ (hi.trans_le A.reductionEnd)).trans (A.reducePins a lo hi)
  · dsimp only
    intro a ha
    exact (low _ ((Nat.add_lt_add_left ha D.extract).trans_le A.extractEnd)).trans (A.orderPins a ha)

/-- No native optimization or input row is passed in as an unexplained witness. -/
theorem measured_calendar (C : Calendar k) (h : ℕ) (hc : 0<c) (mem rom : Memory w)
    (lev : Fin H→ℕ) (gain : Fin H→Cell g) (x : Fin H→DescentGL.Bits k→ℕ)
    (B : ℕ) (bound : ∀v a,x v a≤B) (numSize : 2^(3*k)*B^2<2^b) (lanes : laneBits k h c=l)
    (lv : ∀v,lev v<2^w) (stage : k+1≤2^w) (enough : C.limit<2^w)
    (width : h≤w) (prec : c+Nat.clog 2 H≤w)
    (billSize : ∀j<k+1,∀v d,bill j lev gain x v d<2^c)
    (given : ∀j<k+1,DepthInput (C.atDepth j) C.limit h b c g hc lev gain x mem rom) :
    let P:=reduction H u l c h hc
    let dst:=C.state P H mem (k+1)
    (C.code P w H (k+1)).Exec mem dst (C.ticks P H (k+1)) ∧
      (∀j<k+1,∀i : Fin (2^k),dst ((C.atDepth j).out+i.val)=
        ((∑v,bill j lev gain x v (centralOrder u l i)):Word w)) ∧ ∀z<C.limit,dst z=mem z := by
  let P:=reduction H u l c h hc
  dsimp only
  simp only [← Nat.cast_sum]
  apply C.folded (H:=H) P mem (fun j i=>∑v,bill j lev gain x v (centralOrder u l i)) enough (k+1)
  intro j hj earlier saved
  let a:=(given j hj).inherit saved
  obtain ⟨run,columns,low,_⟩:=measured_depth (C.atDepth j) h j hc earlier rom lev gain x B bound numSize
    lanes lv (hj.trans_le stage) a.weights a.fixed a.levels a.gains a.spectrum (billSize j hj)
    (a.reductionEnd.trans (C.pre j)) (a.extractEnd.trans (C.pre j)) a.beforeOutput a.outputRoom width prec
    a.reducePins a.orderPins
  exact ⟨@run,fun i=>by simpa only [Nat.cast_sum] using columns i,low⟩

end
end Hierarchy.DescentPackedWalsh

end OAI
