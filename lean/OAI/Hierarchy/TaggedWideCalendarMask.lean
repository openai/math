import OAI.Hierarchy.TaggedWideStoredPadding
import OAI.Hierarchy.TaggedWideLeafBanks
import OAI.Hierarchy.TaggedWideLeafWorkspace
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # One zero-suffix circuit at each physical positive-stack input bit -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ThreeFlat Routing Diagonal TraceWords
open Computability.VPVNP.BurstRAM WidePadding ProtocolStackContraction TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type*} [Field F] {V T : Type} [Fintype V] [Fintype T]
    {groups ports lanes bits w m N : ℕ} {records : T→Fin N→ProtocolRAMEmit.Row}
    (cls : T→ℕ)
local notation "D" => ports*lanes
local notation "digit" => fun t:T=>⌈dyadic (cls t)*w⌉₊
local notation "Pins" t => Slot (Fin groups) D × Fin (digit t)
variable (word : T→Fin groups→Bool→Fin (ports*lanes)→Fin bits→V)
    (payload : (t : T)→(Slot (Fin groups) (ports*lanes) × Fin ⌈dyadic (cls t)*w⌉₊)→V)
local notation "rank" t => (Fintype.equivFin (Pins t)).symm

/-- Saturation at the largest local machine word preserves every comparison
against a stored native width, including an entirely inactive final lane. -/
def capColumn (n j : ℕ) : Word n :=
  ⟨min j (2^n-1),lt_of_le_of_lt (min_le_right ..) (by have:=Nat.two_pow_pos n;omega)⟩

theorem capColumn_lt (n j : ℕ) (a : Word n) : capColumn n j<a ↔ j<a.val := by
  change min j (2^n-1)<a.val ↔ j<a.val
  have small := a.isLt
  omega

def positivePorts (t : T) : Ports (V⊕Bool) (Fintype.card (Pins t)) bits where
  col i := let s:=(rank t) i; capColumn bits (s.1.2.2.val%lanes*digit t+s.2.val)
  live i := .inr ((rank t) i).1.1.isSome
  width i j := let s:=(rank t) i; match s.1.1 with
    | none => .inr false
    | some g => .inl (word t g s.1.2.1 s.1.2.2 j)
  payload i := .inl (payload t ((rank t) i))

/-- The menu and every payload pin are fixed before the report is read. -/
def positiveMask : BitNetwork F (Fintype.card V) :=
  WideHost.localFamily (A:=fun _ : T => V⊕Bool) (fun t=>(positivePorts (ports:=ports) (lanes:=lanes) (w:=w) cls word payload t).network (F:=F)) (fun _ i=>i)

theorem positiveMask_cost :
    let net:=positiveMask (F:=F) (ports:=ports) (lanes:=lanes) (w:=w) cls word payload
    net.cells+net.internal≤∑t : T,Fintype.card (Pins t)*(200*bits+65) := by
  dsimp only [positiveMask]
  rw [WideHost.localFamily_size]
  exact Finset.sum_le_sum (fun t _=>(positivePorts (ports:=ports) (lanes:=lanes) (w:=w) cls word payload t).cost)

variable (b : ∀t,Installed F groups ports lanes w m (cls t) (records t))
local notation "orig" t => fun e : TaggedShorterSlotWidth.Transport ((b t).bank.counts)=>
  (records t (((common (records t) w m (cls t) e.1.val (b t).unique).symm e.2).1.val)).width

/-- Original ordinal, lane and column are read directly at the two paid
width endpoints of the realized menu slot. A disabled dummy group is zero. -/
theorem positiveMask_value (v : V→Bool) (x : ∀t,(b t).bank.Slots)
    (words : ∀_t:T,TaggedShorterSlotWidth.Slot groups D→Word bits)
    (read : ∀t g s i j,v (word t g s i j)=TraceWords.bits (words t (g,s,i)) j)
    (stored : ∀t g s i,(words t (g,s,i)).val=
      TaggedShorterSlotWidth.value (b t).bank.place (orig t) (g,s,i))
    (portsLive : ∀t (p : Pins t),v (payload t p)=x t p.1 p.2) :
    TypedWiring.value (positiveMask (F:=F) (ports:=ports) (lanes:=lanes) (w:=w) cls word payload) v =
      if supported (banks b) (active b) x then 1 else 0 := by
  rw [positiveMask,WideHost.localFamily_eval]
  let seen (t : T) (p : Pins t) : Word bits :=
    match p.1.1 with | none=>0 | some g=>words t (g,p.1.2.1,p.1.2.2)
  have localEq (t : T) : TypedWiring.value ((positivePorts (ports:=ports) (lanes:=lanes) (w:=w) cls word payload t).network (F:=F))
      (Sum.elim v id) = if Supported (b t).bank.place (active b t) (x t) then 1 else 0 := by
    have digits (i : Fin (Fintype.card (Pins t))) (j : Fin bits) :
        Sum.elim v id ((positivePorts (ports:=ports) (lanes:=lanes) (w:=w) cls word payload t).width i j)=TraceWords.bits (seen t ((rank t) i)) j := by
      rcases h : ((rank t) i).1.1 with _|g
      · simp [positivePorts,h,seen,TraceWords.bits]
      · simpa [positivePorts,h,seen] using read t g ((rank t) i).1.2.1 ((rank t) i).1.2.2 j
    rw [Ports.eval _ _ (fun i=>seen t ((rank t) i)) digits]
    refine if_congr ?_ rfl rfl
    rw [←support_on_records b t (x t)]
    change (∀i,v (payload t ((rank t) i))=true→((rank t) i).1.1.isSome=true ∧
      capColumn bits (((rank t) i).1.2.2.val%lanes*digit t+((rank t) i).2.val)<seen t ((rank t) i)) ↔ _
    refine ((rank t).forall_congr_right (q:=fun p : Pins t =>
      v (payload t p)=true → p.1.1.isSome=true ∧
        capColumn bits (p.1.2.2.val%lanes*digit t+p.2.val)<seen t p)).trans ?_
    simp only [portsLive,capColumn_lt]
    constructor
    · intro yes
      refine ⟨fun s i j=>?_,fun g s i j on=>?_⟩
      · cases hx : x t (none,s,i) j with
        | false => rfl
        | true => exact Bool.noConfusion (yes ((none,s,i),j) hx).1
      · have hit := (yes ((some g,s,i),j) on).2
        change _ < (words t (g,s,i)).val at hit
        exact (stored_live (b t).bank.place (orig t) (g,s,i) _).mp
          (lt_of_lt_of_eq hit (stored t g s i))
    · rintro ⟨dummy,yes⟩ ⟨⟨g,s,i⟩,j⟩ on
      cases g with
      | none => exact Bool.noConfusion ((dummy s i j).symm.trans on)
      | some g =>
        refine ⟨rfl,?_⟩
        change _ < (words t (g,s,i)).val
        exact lt_of_lt_of_eq ((stored_live (b t).bank.place (orig t) (g,s,i) _).mpr
          (yes g s i j on)) (stored t g s i).symm
  change (∏t,TypedWiring.value ((positivePorts (ports:=ports) (lanes:=lanes) (w:=w) cls word payload t).network (F:=F)) (Sum.elim v id))=_
  simp_rw [localEq]
  by_cases ok : supported (banks b) (active b) x
  · simp [ok,show ∀t,Supported (b t).bank.place (active b t) (x t) from ok]
  · have miss : ¬∀t,Supported (b t).bank.place (active b t) (x t) := ok
    obtain ⟨t,bad⟩:=not_forall.mp miss
    rw [ite_eq_right ok,Finset.prod_eq_zero (Finset.mem_univ t) (ite_eq_right bad)]

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
