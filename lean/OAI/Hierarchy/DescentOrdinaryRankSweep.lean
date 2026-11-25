import OAI.Hierarchy.DescentOrdinaryDonorSources
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! One shared ROM for all five rank gathers and every public source slot.
Only the scalar directory and the packed query may vary between passes. -/
namespace Hierarchy.DescentOrdinaryRankSweep
open DescentSIMDLookup DescentDyadicSpan DescentPackedZip DescentPackedColony DescentPackedChildNeighbor.SIMD
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w jobs T H G a b M:ℕ}
structure Chart (jobs:ℕ) where
  directory:Fin jobs→Bank
  query:Fin jobs→Expr

namespace Chart
variable (Z:Chart jobs) (base T a b M H G rowBits:ℕ)
def first :=base+ROM.cells T a b M H G
def roof:=first base T a b M H G+jobs*span (H*chunks G M)
def operation (i:ℕ):Expr:=if hi:i<jobs then
  body (ROM.layout base T a b M rowBits (Z.directory ⟨i,hi⟩)) (Z.query ⟨i,hi⟩) (List.finRange T) else .lit 0
local notation "N" => H*chunks G M
local notation "first₀" => first base T a b M H G
local notation "body₀" => operation Z base T a b M rowBits
def passes:=DescentPackedFlowBatch.passes first₀ N (span N) body₀ 0 jobs
def program (w:ℕ):=(ROM.program base T a b M H G w).seq (ProtocolRAM.program w (passes Z base T a b M H G rowBits))
def done (m:Memory w):=result (passes Z base T a b M H G rowBits) (ROM.after base T a b M H G m)
def time:=4+10*ROM.cells T a b M H G+clock (passes Z base T a b M H G rowBits)
def page (i:Fin jobs):Bank:=⟨first₀+i.val*span N,Nat.clog 2 N⟩
def Fitted (w:ℕ):Prop:=∀i,Room (ROM.layout base T a b M rowBits (Z.directory i)) (Z.query i) H G a b M w first₀

theorem run (m:Memory w) (fitted:Fitted Z base T a b M H G rowBits w)
    (space:roof (jobs:=jobs) base T a b M H G<2^w):
    (program Z base T a b M H G rowBits w).Exec m (done Z base T a b M H G rowBits m) (time Z base T a b M H G rowBits) ∧
    (∀i:Fin jobs,∀p:Row H G M,done Z base T a b M H G rowBits m ((page (T:=T) base a b M H G i).base+(row H G M p).val)=
      (body₀ i.val).eval (ROM.after base T a b M H G m) ((row H G M p).val:Word w)) ∧
    (∀u,u<base ∨ roof (jobs:=jobs) base T a b M H G≤u→done Z base T a b M H G rowBits m u=m u) ∧ CheapCode (program Z base T a b M H G rowBits w):=by
  have lower:base≤first₀:=Nat.le_add_right ..
  have bound:first₀≤roof (jobs:=jobs) base T a b M H G:=Nat.le_add_right ..
  have mount : (ROM.program base T a b M H G w).Exec m (ROM.after base T a b M H G m) (4+10*ROM.cells T a b M H G) :=DescentStaticWordColumn.mount base (ROM.cells T a b M H G) (ROM.numbers T a b M H G) m (lt_of_le_of_lt bound space)
  have fits (i:ℕ) (hi:i<jobs):(body₀ i).Fits w first₀:=by
    simp only [operation,dite_eq_left hi]
    exact DescentPackedChildNeighbor.SIMD.fitted _ _ (fitted ⟨i,hi⟩) _
  have literal (n:ℕ):CheapCode (DescentStaticWordColumn.program w base (ROM.numbers T a b M H G) n):=by
    induction n with
    | zero=>apply scan_cheap
    | succ n ih=>exact cheap_seq ih (@scan_cheap _ _ _ _)
  have gap:N≤ span N:=span_ge N
  obtain ⟨ran,printed,lowerFrame⟩:=DescentPackedFlowBatch.execute first₀ N (span N) jobs body₀ (ROM.after base T a b M H G m) fits space gap
  refine ⟨mount.then ran,fun i p=>printed i (row H G M p),?_,cheap_seq (literal _) (@ProtocolRAM.program_cheap _ _)⟩
  intro u outside
  have kept:done Z base T a b M H G rowBits m u=ROM.after base T a b M H G m u:=by
    rcases outside with h|h
    · exact lowerFrame u (h.trans_le lower)
    · exact DescentPackedFlowBatch.above first₀ N (span N) body₀ _ 0 jobs u gap (by simpa only [roof,Nat.zero_add] using h)
  exact kept.trans (DescentStaticWordColumn.frame _ _ _ _ _ (outside.imp id (bound.trans ·)))

theorem sourced (m:Memory w) (fitted:Fitted Z base T a b M H G rowBits w)
    (space:roof (jobs:=jobs) base T a b M H G<2^w)
    (values:Fin jobs→Fin H→Fin T→Cell b) (qs:Fin jobs→Fin H→Fin G→Cell a)
    (early:∀i,(Z.directory i).base+H*T≤base) (old:∀i,(Z.query i).Fits w base)
    (read:∀i h j,m ((Z.directory i).base+(h.val*T+j.val))=((values i h j).val:Word w))
    (queries:∀i,Source (Z.query i) (qs i) M m)
    (i:Fin jobs) (p:Row H G M):
    (done Z base T a b M H G rowBits m) ((page (T:=T) base a b M H G i).base+(row H G M p).val)=
      ((data (fun h g=>lookup (values i h) (qs i h g) (List.finRange T)) p).val:Word w):=by
  rw [(run Z base T a b M H G rowBits m fitted space).2.1 i p]
  simp only [operation,dite_eq_left i.isLt]
  apply measures (ROM.layout base T a b M rowBits (Z.directory i)) (Z.query i) first₀ (fitted i) (values i) _
    (ROM.stored (Z.directory i) base rowBits (values i) m (early i) (read i)) (qs i) _ (List.finRange T) p
  intro u
  exact (eval_below _ _ m _ (old i) (fun x hx=>DescentStaticWordColumn.frame _ _ _ _ _ (.inl hx))).trans (queries i u)

theorem clock_bound (lim:ℕ) (bounded:∀i,(Z.query i).work≤lim):
    time Z base T a b M H G rowBits≤4+10*ROM.cells T a b M H G+(4+jobs*(4+N*(2*(1+T*(lim+36))+4))):=by
  apply Nat.add_le_add_left
  apply DescentPackedFlowBatch.tariff
  intro j hj
  simp only [operation,dite_eq_left hj,DescentPackedChildNeighbor.SIMD.work,List.length_finRange]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (bounded ⟨j,hj⟩) 36)) 1

end Chart
end
end Hierarchy.DescentOrdinaryRankSweep

end OAI
