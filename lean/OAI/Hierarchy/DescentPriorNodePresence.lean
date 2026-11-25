import OAI.Hierarchy.DescentPriorNodePresenceShape
import OAI.Hierarchy.DescentOperandLaneRead

namespace OAI
/-! Deliver the true all-node occupancy and original arity on the reset's common page pitch. -/
namespace Hierarchy.DescentPriorNodePresence.Chart
open DescentSIMDLookup DescentPackedColony DescentSixParty.Chronology ProtocolRAM
open DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ} (C : Chart) (base : ℕ) (role arity : Fin C.blocks→Bank)
local notation "early" => ∀x,(role x).Fits w base ∧ (arity x).Fits w base
local notation "masker" => C.mask.phase C.presence base role (fun _=>true) w
local notation "tiler" => C.convert.phase (C.maskEnd base) (C.mask.bank base) w
local notation "last" => C.pages.phase C.expand (C.tileEnd base) (C.input base arity) C.test w

private theorem input_ready (old : early) (room : C.endAddress base<2^w) (j : Fin (2*C.blocks)) :
    (C.input base arity j).Fits w (C.tileEnd base):=by
  let p:Fin 2×Fin C.blocks:=finProdFinEquiv.symm j
  have step:=C.starts base
  have mid : C.tileEnd base<2^w:=(step.2.2.1.trans step.2.2.2).trans_lt room
  change (if p.1=0 then C.convert.bank (C.maskEnd base) p.2 else arity p.2).Fits w (C.tileEnd base)
  split
  · exact (C.convert.placed (C.maskEnd base) mid p.2).1
  · have f:=(old p.2).2
    exact ⟨f.1,f.2.1,f.2.2.trans (step.1.trans step.2.1)⟩

theorem any (m : Memory w) (old : early) (room : C.endAddress base<2^w):
    (C.phase base role arity w).Runs m ∧ ∀i,i<base ∨ C.endAddress base ≤ i →
    (C.phase base role arity w).image m i=m i:=by
  have step:=C.starts base
  have mid : C.tileEnd base<2^w:=(step.2.2.1.trans step.2.2.2).trans_lt room
  have small : C.maskEnd base<2^w:=step.2.1.trans_lt mid
  have a:=C.mask.any C.presence base role (fun _=>true) m (fun j=>(old j).1) small
  have b:=C.convert.any (C.maskEnd base) (C.mask.bank base) ((masker).image m)
    (fun j=>(C.mask.placed base small j).1) mid
  have c:=C.pages.any C.expand (C.tileEnd base) (C.input base arity) C.test ((tiler).image ((masker).image m))
    (C.input_ready base role arity old room) room
  refine ⟨NativePhase.seq_runs _ _ _ (NativePhase.seq_runs _ _ _ a.1 b.1) c.1,?_⟩
  intro i away
  rcases away with lo|hi
  · exact (c.2 i (.inl (lo.trans_le (step.1.trans step.2.1)))).trans
      ((b.2 i (.inl (lo.trans_le step.1))).trans (a.2 i (.inl lo)))
  · have top:=(step.2.2.1.trans step.2.2.2).trans hi
    exact (c.2 i (.inr hi)).trans ((b.2 i (.inr top)).trans (a.2 i (.inr (step.2.1.trans top))))

theorem placed (room : C.endAddress base<2^w) (f : Fin 2) (x : Fin C.blocks) :
    (C.bank base f x).Fits w (C.endAddress base) ∧ C.rows≤(C.bank base f x).size:=
  C.pages.placed (C.tileEnd base) room (finProdFinEquiv (f,x))

theorem issued (m : Memory w) (old : early) (room : C.endAddress base<2^w) (live : 0<C.roleLanes)
    (tokens : Fin C.blocks→Fin C.hosts→Fin C.groups→Cell (C.tokenBits*C.nodes))
    (arities : Fin C.blocks→Fin C.hosts→Fin C.groups→Cell (C.bits*C.nodes))
    (size : ∀x,C.mask.rows≤(role x).size ∧ C.rows≤(arity x).size)
    (input : ∀x,Reads (role x) (tokens x) C.roleLanes m ∧ Reads (arity x) (arities x) C.operandLanes m)
    (f : Fin 2) (x : Fin C.blocks) :
    Reads (C.bank base f x) (if f=0 then fun h g=>C.readings (tokens x h g) else arities x)
      C.operandLanes ((C.phase base role arity w).image m):=by
  have step:=C.starts base
  have mid : C.tileEnd base<2^w:=(step.2.2.1.trans step.2.2.2).trans_lt room
  have small : C.maskEnd base<2^w:=step.2.1.trans_lt mid
  let a:=(masker).image m
  let b:=(tiler).image a
  have first:=C.mask.issued C.presence base role (fun _=>true) m (fun j=>(old j).1) small
    C.presence_zero x (size x).1 (tokens x) (fun _ _=>0) (fun _=>(input x).1) (by simp)
  have boarded:=C.convert.reads (C.maskEnd base) (C.mask.bank base) a
    (fun j=>(C.mask.placed base small j).1) mid x (fun h g=>C.presence (tokens x h g) 0) live
    (C.mask.placed base small x).2 (by simpa [a,Chart.mask,Chart.convert] using first)
  have pa:=C.mask.any C.presence base role (fun _=>true) m (fun j=>(old j).1) small
  have pb:=C.convert.any (C.maskEnd base) (C.mask.bank base) a (fun j=>(C.mask.placed base small j).1) mid
  have arityRead : Reads (arity x) (arities x) C.operandLanes b:=by
    intro p
    have idx : (arity x).base+(row C.hosts C.groups C.operandLanes p).val<base:=
      (Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le (size x).2) _).trans_le (old x).2.2.2
    exact (pb.2 _ (.inl (idx.trans_le step.1))).trans ((pa.2 _ (.inl idx)).trans ((input x).2 p))
  let i:=finProdFinEquiv (f,x)
  have test_ : C.test i=decide (f=0):=by simp [test,i]
  have source_ : C.input base arity i=(if f=0 then C.convert.bank (C.maskEnd base) x else arity x):=by
    simp [Chart.input,i]
  have span : C.pages.rows≤(C.input base arity i).size:=by
    rw [source_];split
    · exact (C.convert.placed (C.maskEnd base) mid x).2
    · exact (size x).2
  have finished:=C.pages.issued C.expand (C.tileEnd base) (C.input base arity) C.test b
    (C.input_ready base role arity old room) room C.expand_zero i span
    (fun h g=>C.presence (tokens x h g) 0) (arities x)
    (by intro h;have hit : f=0:=of_decide_eq_true (test_.symm.trans h);simpa only [source_,ite_eq_left hit,b,Chart.pages,Chart.convert] using boarded)
    (by intro h;have miss : f≠0:=of_decide_eq_false (test_.symm.trans h);simpa only [source_,ite_eq_right miss,Chart.pages] using arityRead)
  simpa only [test_,decide_eq_true_eq,readings,Chart.phase,NativePhase.seq,Chart.bank,i,a,b,Chart.pages] using finished

/-- The numerical row lookup followed by the original node digit reads a genuine one or zero. -/
theorem presence_digit (src : Bank) (m : Memory w) (tokens : Fin C.hosts→Fin C.groups→Cell (C.tokenBits*C.nodes))
    (seen : Reads src (fun h g=>C.readings (tokens h g)) C.operandLanes m)
    (key : 0<C.bits) (bits : (C.bits*C.nodes)*C.operandLanes≤w) (lanes : 0<C.operandLanes)
    (h : Fin C.hosts) (g : Fin C.groups) (n : Fin C.nodes) :
    digit C.bits n.val (digit (C.bits*C.nodes) (lane g lanes).val
      (m (src.base+(row C.hosts C.groups C.operandLanes (position h g lanes)).val)).val)=
        if ((encode C.tokenBits C.nodes).symm (tokens h g) n).val=0 then 0 else 1:=by
  rw [DescentOperandStateBanks.Reset.lane_read src.base _ m seen bits lanes h g]
  have projected:=digit_encode ((encode C.bits C.nodes).symm (C.readings (tokens h g))) n
  rw [Equiv.apply_symm_apply,C.at_node] at projected
  rw [projected]
  split <;> simp_all [Nat.mod_eq_of_lt (Nat.one_lt_two_pow key.ne')]

end
end Hierarchy.DescentPriorNodePresence.Chart

end OAI
