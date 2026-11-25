import OAI.Hierarchy.DescentPrimitiveCheckpointShape
import OAI.Hierarchy.DescentResetPrimitivePage
import OAI.Hierarchy.DescentResetNodeBooks
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # One permanent physical primitive-role bank for each successor block -/
namespace Hierarchy.DescentResetPrimitiveCheckpoint.Shape
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty DescentPrimitivePalette
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec)
variable (v : DescentResetPrimitiveCheckpoint.Shape) {w : ℕ}
set_option quotPrecheck false
local notation "c" => v.chart
local notation "M" => (c).lanes
local notation "r" => v.rawBits
local notation "t" => printedBits G s Z op
abbrev Input :=Fin (c).blocks→Fin (c).nodes→Expr
structure Inputs where
  retained : v.Input
  fresh : v.Input
  relay : v.Input

variable (base : ℕ) (src : v.Inputs)
local notation "k" => v.gateEnd base
local notation "u" => v.scalarEnd base
def operation (j : Fin ((c).blocks*(c).nodes)) : Expr :=
  let p : Fin (c).blocks×Fin (c).nodes:=finProdFinEquiv.symm j
  DescentResetPrimitivePage.expr G s Z op base r M (src.retained p.1 p.2) (src.fresh p.1 p.2) (src.relay p.1 p.2)
local notation "act" => v.operation G s Z op base src
def scan :=ProbeStage.Native.columns (c).rows k (List.ofFn act)
def gates :=DescentResetPrimitivePage.program G s Z op base r M w
def pack :=DescentResetNodeBooks.program u k (c).blocks (c).nodes (c).hosts (c).groups (c).bits M w
def program (w : ℕ) :=((v.gates G s Z op base (w:=w)).seq (ProtocolRAM.program w (v.scan G s Z op base src))).seq (v.pack base (w:=w))
def clock :=DescentResetPrimitivePage.clock r M+ProtocolRAM.clock (v.scan G s Z op base src)+
  DescentResetNodeBooks.ticks u k (c).blocks (c).nodes (c).hosts (c).groups (c).bits M
def firstMem (m : Memory w) :=DescentResetPrimitivePage.image G s Z op base r M m
def secondMem (m : Memory w) :=result (v.scan G s Z op base src) (v.firstMem G s Z op base m)
def finalMem (m : Memory w) :=DescentResetNodeBooks.image u k (c).blocks (c).nodes (c).hosts (c).groups (c).bits M
  (v.secondMem G s Z op base src m)

def Fits (w : ℕ) :=∀x n,(src.retained x n).Fits w base ∧ (src.fresh x n).Fits w base ∧ (src.relay x n).Fits w base

private theorem bounds : base≤k ∧ k≤u ∧ u≤v.endAddress base:=by
  refine ⟨(Nat.le_add_right ..).trans (Nat.le_add_right ..),Nat.le_add_right ..,?_⟩
  exact ((Nat.le_add_right _ (max (c).dictionary (c).rounded)).trans (Nat.le_add_right _ ((c).blocks*(c).rows))).trans (Nat.le_add_right ..)

private theorem terms_fit (safe : v.Fits base src w) (room : v.endAddress base<2^w) :
    ∀e∈List.ofFn act,e.Fits w k:=by
  intro e h;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
  exact DescentResetPrimitivePage.fitted G s Z op base r M _ _ _ (safe _ _) (((v.bounds base).2.1.trans (v.bounds base).2.2).trans_lt room)

theorem any (m : Memory w) (safe : v.Fits base src w) (room : v.endAddress base<2^w) :
    (v.program G s Z op base src w).Exec m (v.finalMem G s Z op base src m) (v.clock G s Z op base src) ∧
    CheapCode (v.program G s Z op base src w) ∧ ∀i,i<base ∨ v.endAddress base≤ i→v.finalMem G s Z op base src m i=m i:=by
  let tr:=List.ofFn act
  have b:=v.bounds base
  have len : tr.length=(c).blocks*(c).nodes:=List.length_ofFn
  have reserve : k+tr.length*(c).rows<2^w:=by rw [len];exact b.2.2.trans_lt room
  have top : k<2^w:=(b.2.1.trans b.2.2).trans_lt room
  have first:=DescentResetPrimitivePage.any G s Z op base r M m top
  have next : (ProtocolRAM.program w (v.scan G s Z op base src)).Exec (v.firstMem G s Z op base m)
      (v.secondMem G s Z op base src m) (ProtocolRAM.clock (v.scan G s Z op base src)) :=
    ProbeStage.Native.columns_exec tr (v.firstMem G s Z op base m)
    (ProbeStage.Native.columns_safe (n:=(c).rows) tr (le_refl k) (v.terms_fit G s Z op base src safe room) reserve)
  have end_:=DescentResetNodeBooks.any u k (c).blocks (c).nodes (c).hosts (c).groups (c).bits M (v.secondMem G s Z op base src m) le_rfl room
  refine ⟨Procedure.Exec.then (Procedure.Exec.then first.1 next) end_.1,cheap_seq (cheap_seq first.2.1 (@ProtocolRAM.program_cheap _ _)) (DescentResetNodeBooks.cheap u k (c).blocks (c).nodes (c).hosts (c).groups (c).bits M w),?_⟩
  intro i away
  have before : i<u ∨ v.endAddress base≤ i:=away.imp_left (fun h=>h.trans_le (b.1.trans b.2.1))
  have outside : i<k ∨ k+tr.length*(c).rows≤ i:=by rw [len];exact away.imp (fun h=>h.trans_le b.1) (b.2.2.trans ·)
  exact (end_.2 i before).trans ((ProbeStage.Native.columns_frame tr (v.firstMem G s Z op base m) outside).trans
    (first.2.2 i (away.imp_right ((b.2.1.trans b.2.2).trans ·))))

private theorem data_cast_val {a b H L lanes : ℕ} (same : a = b)
    (f : Fin H → Fin L → Cell b) (p : Row H L lanes) :
    (data (fun h g => ((f h g).val : Cell a)) p).val = (data f p).val := by
  subst a
  have eqn : (fun h g => ((f h g).val : Cell b)) = f := by
    funext h g
    exact Fin.ext (Fin.val_cast_of_lt (f h g).isLt)
  rw [eqn]

set_option maxHeartbeats 1500000 in
theorem issued (m : Memory w) (safe : v.Fits base src w) (room : v.endAddress base<2^w)
    (bits : (c).bits=t) (cells : Fin (c).blocks→Fin (c).nodes→Fin (c).hosts→Fin (c).groups→PrintedInput t)
    (fitRaw : ∀x n h g,DescentResetPrimitivePage.localRole (cells x n h g)<2^r)
    (kept : ∀x n,Source (src.retained x n) (fun h g=>DescentResetPrimitivePage.oldWord (cells x n h g)) M m)
    (born : ∀x n,Source (src.fresh x n) (fun h g=>(DescentResetPrimitivePage.localRole (cells x n h g):Cell r)) M m)
    (self : ∀x n,Source (src.relay x n) (fun h g=>DescentResetPrimitivePage.relayFlag (cells x n h g)) M m) (x : Fin (c).blocks) :
    Reads (v.bank base x) (fun h g=>encode (c).bits (c).nodes (fun n=>((emit G s Z op (cells x n h g)).val:Cell (c).bits)))
      M (v.finalMem G s Z op base src m) :=by
  let tr:=List.ofFn act
  have len : tr.length=(c).blocks*(c).nodes:=List.length_ofFn
  have top:=((v.bounds base).2.1.trans (v.bounds base).2.2).trans_lt room
  apply DescentResetNodeBooks.posted_at u k (c).blocks (c).nodes (c).hosts (c).groups (c).bits M
    (v.secondMem G s Z op base src m) le_rfl room x
    (fun n h g => ((emit G s Z op (cells x n h g)).val : Cell (c).bits))
  intro n p
  let j : Fin ((c).blocks*(c).nodes):=finProdFinEquiv (x,n)
  have jFits : j.val<tr.length:=by rw [len];exact j.isLt
  have word:=ProbeStage.Native.columns_read tr (v.firstMem G s Z op base m) (le_refl k)
    (v.terms_fit G s Z op base src safe room) j.val jFits (row _ _ _ p)
  have term : tr[j.val]=DescentResetPrimitivePage.expr G s Z op base r M (src.retained x n) (src.fresh x n) (src.relay x n):=by
    simp only [tr, List.getElem_ofFn, Fin.eta, operation, j, Equiv.symm_apply_apply]
  have idx : j.val=x.val*(c).nodes+n.val:=by simp [j,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  rw [term,idx] at word
  apply word.trans
  have source:=DescentResetPrimitivePage.posted G s Z op base r M m _ _ _ (cells x n) (fitRaw x n)
    (safe x n) (kept x n) (born x n) (self x n) top p
  apply source.trans
  exact congrArg (fun y : ℕ => (y : Word w))
    (data_cast_val bits (fun h g => emit G s Z op (cells x n h g)) p).symm

theorem bank_fits (room : v.endAddress base<2^w) (x : Fin (c).blocks) :
    (v.bank base x).Fits w (v.endAddress base) ∧ (c).rows≤(v.bank base x).size:=
  DescentResetNodeBooks.placed u (c).blocks (c).nodes (c).hosts (c).groups (c).bits M x room

end
end Hierarchy.DescentResetPrimitiveCheckpoint.Shape

end OAI
