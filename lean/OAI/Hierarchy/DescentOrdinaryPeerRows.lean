import OAI.Hierarchy.DescentOrdinaryPeerSlots
import OAI.Hierarchy.DescentTenHopRAM

namespace OAI
/-! # Emitting the full ordinary successor adjacency from the old physical bank -/
namespace Hierarchy.DescentOrdinaryPeerRows
open DescentSixParty.Chronology DescentDyadicSpan DescentOrdinaryPeerLifts
open DescentOrdinaryPeerSlots DescentTenHopRoster
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H D S R E w : ℕ}

def reach (w base H D : ℕ) (source : Bank) : NativePhase w :=
  ⟨DescentTenHopRAM.native source H D w base,DescentTenHopRAM.ticks source H D,
    DescentTenHopRAM.finish source H D base,DescentTenHopRAM.cheap source H D w base⟩

def reached (base H D : ℕ) : Bank := ⟨base,Nat.clog 2 (H*DescentTenHopRAM.paths D)⟩
def fixed (base H D : ℕ) := base+span (H*DescentTenHopRAM.paths D)
def peers (base H D R E : ℕ) : Bank := ⟨DescentOrdinaryPeerChart.out (fixed base H D) H (R*E),Nat.clog 2 (R*E)⟩
def endAddress (base H D R E : ℕ) := DescentOrdinaryPeerChart.top (fixed base H D) H (R*E)

def phase (w base H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) : NativePhase w :=
  let cols:=request (H:=H) (P:=DescentTenHopRAM.paths D) (R:=R) (D:=E) shapes
  (reach w base H D source).seq (DescentOrdinaryPeerChart.program w (fixed base H D) R count (reached base H D) cols)

private theorem cuts (base H D R E : ℕ) :
    base ≤ fixed base H D ∧ fixed base H D ≤ endAddress base H D R E ∧
      base+H*DescentTenHopRAM.paths D≤fixed base H D := by
  refine ⟨Nat.le_add_right ..,?_,Nat.add_le_add_left (span_ge _) _⟩
  exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

set_option maxHeartbeats 1000000 in
theorem any (base H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) (m : Memory w)
    (cf : count.Fits w base) (src : source.Fits w base) (host : H<2^w) (end_ : endAddress base H D R E<2^w) :
    let p:=phase w base H D R E count source shapes
    p.Runs m ∧ ∀a,a<base ∨ endAddress base H D R E≤a→p.image m a=m a := by
  intro p
  let r:=reach w base H D source
  let req:=request (H:=H) (P:=DescentTenHopRAM.paths D) (R:=R) (D:=E) shapes
  let q:=DescentOrdinaryPeerChart.program w (fixed base H D) R count (reached base H D) req
  have cord:=cuts base H D R E
  have safe:=cord.2.1.trans_lt end_
  have fit : (reached base H D).Fits w (fixed base H D):=
    ⟨span_pos _,(Nat.le_add_left ..).trans_lt safe,le_rfl⟩
  have got : r.Runs m:=DescentTenHopRAM.run source H D base m src (cord.2.2.trans_lt safe)
  have below : count.Fits w (fixed base H D):=⟨cf.1,cf.2.1,cf.2.2.trans cord.1⟩
  have out:=DescentOrdinaryPeerChart.any (fixed base H D) R count (reached base H D) req
    (r.image m) below fit (span_ge (H*DescentTenHopRAM.paths D)) host end_
  change (r.seq q).Runs m ∧ ∀ a, a<base ∨ endAddress base H D R E≤a →
    (r.seq q).image m a = m a
  refine ⟨NativePhase.seq_runs r q m got out.1,?_⟩
  intro a away
  exact NativePhase.seq_keeps r q m a
    (DescentTenHopRAM.frame source H D base m a (away.imp_right ((cord.2.2.trans cord.2.1).trans ·)))
    (out.2 a (away.imp_left (·.trans_le cord.1)))

set_option maxHeartbeats 1000000 in
theorem read (base N : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S))
    (old : Fin H→Fin D→Option (Fin H)) (m : Memory w) (Nle : N≤H) (cf : count.Fits w base)
    (src : source.Fits w base) (cap : H*D≤ source.size) (host : H<2^w)
    (end_ : endAddress base H D R E<2^w) (size : m count.base=(N:Word w))
    (stored : ∀v j,m (source.base+v.val*D+j.val)=(DescentHaloWalkRAM.number (old v j):Word w))
    (x : Fin R) (i : Fin E) :
    (phase w base H D R E count source shapes).image m ((peers base H D R E).base+x.val*E+i.val)=
      (result N R S (oldWithin old) (atRow (P:=DescentTenHopRAM.paths D) shapes x i):Word w) := by
  let r:=reach w base H D source
  let req:=request (H:=H) (P:=DescentTenHopRAM.paths D) (R:=R) (D:=E) shapes
  let q:=DescentOrdinaryPeerChart.program w (fixed base H D) R count (reached base H D) req
  have cord:=cuts base H D R E
  have safe:=cord.2.1.trans_lt end_
  have fit : (reached base H D).Fits w (fixed base H D):=
    ⟨span_pos _,(Nat.le_add_left ..).trans_lt safe,le_rfl⟩
  have below : count.Fits w (fixed base H D):=⟨cf.1,cf.2.1,cf.2.2.trans cord.1⟩
  have size_ : r.image m count.base=(N:Word w):=
    (DescentTenHopRAM.frame source H D base m count.base (.inl ((Nat.lt_add_of_pos_right cf.1).trans_le cf.2.2))).trans size
  have vals (v : Fin H) (j : Fin (DescentTenHopRAM.paths D)) :
      r.image m ((reached base H D).base+(finProdFinEquiv (v,j)).val)=(((oldWithin old v j).elim H Fin.val : ℕ):Word w):=by
    have bound : H*DescentTenHopRAM.paths D < 2^w:=(Nat.le_add_left _ base).trans_lt (cord.2.2.trans_lt safe)
    have paths : DescentTenHopRAM.paths D<2^w:=(Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt v.isLt)).trans_lt bound
    change DescentTenHopRAM.finish source H D base m (base+(finProdFinEquiv (v,j)).val) =
      (DescentHaloWalkRAM.number (oldWithin old v j):Word w)
    rw [show (finProdFinEquiv (v,j)).val = v.val*DescentTenHopRAM.paths D+j.val from code_val v j]
    exact DescentTenHopRAM.read source base old m src cap host paths stored v j
  let idx:=finProdFinEquiv (x,i)
  have row : req idx = atRow (H:=H) (P:=DescentTenHopRAM.paths D) shapes x i := by
    simp only [req,idx,request,Equiv.symm_apply_apply]
  let out:=DescentOrdinaryPeerChart.out (fixed base H D) H (R*E)
  have got : q.image (r.image m) (out+idx.val) = (result N R S (oldWithin old) (req idx):Word w) :=
    DescentOrdinaryPeerChart.read (fixed base H D) N R count (reached base H D) req
      (oldWithin old) (r.image m) Nle below fit (span_ge (H*DescentTenHopRAM.paths D))
      host end_ size_ vals idx
  change q.image (r.image m) (out+x.val*E+i.val) = _
  rw [Nat.add_assoc out,←show idx.val=x.val*E+i.val from code_val x i,←row]
  exact got

theorem extent (base H D R E : ℕ) :
    endAddress base H D R E ≤ base+2*(H*DescentTenHopRAM.paths D)+8*(R*E)+2*H+6 := by
  have x:=DescentOrdinaryPeerChart.extent (fixed base H D) H (R*E)
  have y:=span_le (H*DescentTenHopRAM.paths D)
  apply x.trans
  unfold fixed
  omega

theorem price (base H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) :
    let p:=phase w base H D R E count source shapes
    p.ticks+DescentStaticWordColumn.names p.program ≤
      15000*(H+1)*(D+12)^50+300*(R*E)+50*H+610 := by
  intro p
  let req:=request (H:=H) (P:=DescentTenHopRAM.paths D) (R:=R) (D:=E) shapes
  let q:=DescentOrdinaryPeerChart.program w (fixed base H D) R count (reached base H D) req
  have a:=DescentTenHopRAM.price source H D w base
  obtain ⟨bt,bn⟩ : q.ticks ≤ 200*((R*E)+1)+20*H+10 ∧
      DescentStaticWordColumn.names q.program ≤ 400+100*(R*E)+30*H :=
    DescentOrdinaryPeerChart.price (w:=w) (fixed base H D) R count (reached base H D) req
  change (DescentTenHopRAM.ticks source H D + q.ticks) +
    DescentStaticWordColumn.names ((DescentTenHopRAM.native source H D w base).seq q.program) ≤ _
  rw [DescentStaticWordColumn.names_seq]
  omega


end
end Hierarchy.DescentOrdinaryPeerRows

end OAI
