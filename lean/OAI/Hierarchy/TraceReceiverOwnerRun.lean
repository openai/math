import OAI.Hierarchy.TraceReceiverOwnerMount
import OAI.ThreeFlat.RAM.HistoryRootsCorrect
import OAI.ThreeFlat.RAM.HistorySelectedOwners

namespace OAI
/-! # The mounted selector scans the true parent and classifier rows -/
namespace Hierarchy.TraceReceiverOwnerMount
open ThreeFlat Diagonal RAM RAM.PhysicalProcedure RAM.HistoryNodeDirectory
open Diagonal.TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {W : ℕ}

structure Room (W age first roots owners target : ℕ) : Prop where
  fixed : 128 ≤ stride age
  nodes : 8*(first+roots) ≤ stride age
  high : base age 46 ≤ owners
  ownerEnd : owners+roots ≤ target
  word : target+1 < 2^W

private structure Bounds (W age first roots owners target : ℕ) : Prop where
  clock : base age 1+4 ≤ base age 6+1
  stats : base age 6+2 ≤ pairs age
  pair : pairs age+2*roots ≤ desc age
  desc : desc age+2 ≤ base age 44
  nodes : base age 44+8*(first+roots) ≤ base age 45
  rootRange : base age 45+(first+roots) ≤ owners
  owner : owners+roots ≤ target
  word : target+1 < 2^W

private theorem Room.bounds {u f n o t : ℕ} (room : Room W u f n o t) : Bounds W u f n o t := by
  obtain ⟨wide,total,high,own,last⟩:=room
  change 47*stride u ≤ o at high
  constructor
  · change 2*stride u+4 ≤ 7*stride u+1;omega
  · change 7*stride u+2 ≤ 12*stride u+1*(stride u/4);omega
  · change 12*stride u+1*(stride u/4)+2*n ≤ 12*stride u+3*(stride u/4);omega
  · change 12*stride u+3*(stride u/4)+2 ≤ 45*stride u;omega
  · change 45*stride u+8*(f+n) ≤ 46*stride u;omega
  · change 46*stride u+(f+n) ≤ o;omega
  · exact own
  · exact last

def headerImage (age first roots target : ℕ) (m : Memory W) :=
  let p:=writeMemory m (desc age) first
  let q:=writeMemory p ((desc age+1:ℕ):Word W) (base age 44)
  let r:=writeMemory q ((base age 6+1:ℕ):Word W) roots
  let s:=writeMemory r (base age 1) 0
  PhysicalInputCopy.copied target 1 (base age 1+3) s

def HeaderCell (u a : ℕ) := a=desc u ∨ a=desc u+1 ∨ a=base u 6+1 ∨ a=base u 1 ∨ a=base u 1+3

private structure HeaderState (u f n tgt : ℕ) (m out : Memory W) : Prop where
  first : out (desc u)=(f:Word W)
  pointer : out (desc u+1)=(base u 44:Word W)
  roots : out (base u 6+1)=(n:Word W)
  zero : out (base u 1)=0
  clock : out (base u 1+3)=m tgt
  frame : ∀ a,¬HeaderCell u a → out a=m a

private theorem header_run {u f n owners target : ℕ} (r : Bounds W u f n owners target) (m : Memory W) :
    (header W u f n target).Exec m (headerImage u f n target m) 23 ∧
    HeaderState u f n target m (headerImage u f n target m) := by
  obtain ⟨a,b,c,d,e,g,o,t⟩:=r
  let p:=writeMemory m (desc u:Word W) f
  let q:=writeMemory p ((desc u+1:ℕ):Word W) (base u 44)
  let v:=writeMemory q ((base u 6+1:ℕ):Word W) n
  let z:=writeMemory v (base u 1:Word W) 0
  have x0 : (NavigationPass.start (desc u) f).Exec m p 3 :=
    Procedure.Spec.exec (NavigationPass.start_spec (desc u:Word W) (f:Word W)) m trivial
  have x1 : (NavigationPass.start ((desc u+1:ℕ):Word W) (base u 44)).Exec p q 3 :=
    Procedure.Spec.exec (NavigationPass.start_spec ((desc u+1:ℕ):Word W) (base u 44:Word W)) p trivial
  have x2 : (NavigationPass.start ((base u 6+1:ℕ):Word W) n).Exec q v 3 :=
    Procedure.Spec.exec (NavigationPass.start_spec ((base u 6+1:ℕ):Word W) (n:Word W)) q trivial
  have x3 : (NavigationPass.start (base u 1:Word W) 0).Exec v z 3 :=
    Procedure.Spec.exec (NavigationPass.start_spec (base u 1:Word W) 0) v trivial
  have x4 : (PhysicalInputPhases.copying W target 1 (base u 1+3)).Exec z (headerImage u f n target m) 11 :=
    Procedure.Spec.exec (PhysicalInputPhases.copying_spec (w:=W) target 1 (base u 1+3) t (by omega)
    (.inl (by omega))) z trivial
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then x0 x1) x2) x3) x4,?_⟩
  have atZ (i : ℕ) : z i=if i=base u 1 then 0 else if i=base u 6+1 then (n:Word W)
      else if i=desc u+1 then (base u 44:Word W) else if i=desc u then (f:Word W) else m i := by
    simp only [z,v,q,p,writeMemory,Fin.val_cast_of_lt (by omega : desc u < 2^W),
      Fin.val_cast_of_lt (by omega : desc u+1 < 2^W),Fin.val_cast_of_lt (by omega : base u 1 < 2^W),
      Fin.val_cast_of_lt (by omega : base u 6+1 < 2^W)]
  have off (x : ℕ) (h : x≠base u 1+3) : headerImage u f n target m x=z x :=
    PhysicalInputCopy.copied_outside target 1 (base u 1+3) z x (by omega)
  have clock : headerImage u f n target m (base u 1+3)=z target := by
    change PhysicalInputCopy.copied target 1 (base u 1+3) z (base u 1+3) = z target
    simpa only [Nat.add_zero] using PhysicalInputCopy.copied_at target 1 (base u 1+3) z 0 (by decide)
  constructor
  · rw [off _ (by omega),atZ]; split_ifs <;> first | rfl | omega
  · rw [off _ (by omega),atZ]; split_ifs <;> first | rfl | omega
  · rw [off _ (by omega),atZ]; split_ifs <;> first | rfl | omega
  · rw [off _ (by omega),atZ,ite_eq_left rfl]
  · rw [clock,atZ]; split_ifs <;> first | rfl | omega
  · intro i hi
    unfold HeaderCell at hi
    rw [off _ (by tauto),atZ]
    split_ifs <;> tauto

def reverseBanks (W age first : ℕ) : Reverse.Banks W := ⟨first,base age 44,base age 45⟩

private theorem reverse_run {u f n owners tgt : ℕ} (r : Bounds W u f n owners tgt)
    (C : Chronology (f+n)) (first : C.firstFinal=f) (m : Memory W)
    (at0 : m (desc u)=(f:Word W)) (at1 : m (desc u+1)=(base u 44:Word W)) (num : m (base u 6+1)=(n:Word W))
    (parents : ∀ i : Fin (f+n),i.val < C.firstFinal → m (base u 44+8*i.val+1)=((C.parent i).val:Word W)) :
    let out:=Reverse.sweep (reverseBanks W u f) (f+n) m
    (reverse W u).Exec m out (12+11*(f+n)) ∧
    (∀ i : Fin (f+n),out (base u 45+i.val)=(C.root i:Word W)) ∧
    ∀ a,a < base u 45 ∨ base u 45+(f+n) ≤ a → out a=m a := by
  obtain ⟨a,b,c,e,h,g,o,t⟩:=r
  intro out
  have size : f+n < 2^W:=by omega
  have lo : base u 44 < 2^W:=by omega
  have dest : base u 45 < 2^W:=by omega
  have firstFit : f < 2^W:=by omega
  have one : ((desc u:Word W)+1).val=desc u+1:=by rw [←Nat.cast_add_one,Fin.val_cast_of_lt (by omega)]
  constructor
  · intro P R K M pc reg pub exit installed data cfg mem start eq
    subst mem
    change Fin 3 → Fin K at pub
    have d0 : M.publicData (pub 0)=(desc u:Word W):=data (0 : Fin 3)
    have d1 : M.publicData (pub 1)=((base u 6+1:ℕ):Word W):=data (1 : Fin 3)
    have d2 : M.publicData (pub 2)=(base u 45:Word W):=data (2 : Fin 3)
    have banks : Reverse.banks (M.publicData∘pub) m=reverseBanks W u f := by
      simp only [Reverse.banks,Function.comp_apply,d0,d2,Fin.val_cast_of_lt (by omega : desc u < 2^W),
        one,at0,at1,reverseBanks]
    have bound : (m (M.publicData (pub 1)).val).val+(m (M.publicData (pub 0)).val).val=f+n := by
      rw [d0,d1,Fin.val_cast_of_lt (by omega : desc u < 2^W),Fin.val_cast_of_lt (by omega : base u 6+1 < 2^W),
        at0,num,Fin.val_cast_of_lt firstFit,Fin.val_cast_of_lt (by omega : n < 2^W)]
      omega
    obtain ⟨steps,le,rs,run⟩:=Reverse.run M pc reg pub exit installed cfg m start (f+n) bound size
    rw [banks] at run
    exact ⟨steps,le,_,_,run,rfl,rfl⟩
  · constructor
    · intro i
      have ok:=Reverse.sweep_correct_of_inner C (reverseBanks W u f) m
        (by change (f:Word W).val=C.firstFinal;rw [first,Fin.val_cast_of_lt firstFit]) size
        (by simpa only [reverseBanks,Fin.val_cast_of_lt lo,Fin.val_cast_of_lt dest] using h)
        (by change (base u 45:Word W).val+(f+n) ≤ 2^W;rw [Fin.val_cast_of_lt dest];omega)
        (by simpa only [reverseBanks,Fin.val_cast_of_lt lo] using parents) i
      simpa only [out,reverseBanks,Fin.val_cast_of_lt dest] using ok
    · intro j off
      apply Reverse.sweep_frame
      · change (base u 45:Word W).val+(f+n) ≤ 2^W;rw [Fin.val_cast_of_lt dest];omega
      · simpa only [reverseBanks,Fin.val_cast_of_lt dest] using off

/-- These six public addresses are exactly the ports of the selected interpreter. -/
def data (W u : ℕ) : Selected.Data W := fun i=>
  (![base u 18,base u 45,pairs u,base u 1,desc u,base u 6+1] i:ℕ)

def directory {f n : ℕ} (C : Chronology (f+n)) (owner : Fin n → Word W) (slot : Word W) :
    Selected.Directory W (f+n) where
  root i:=(C.root i:Word W)
  owner w:=(0,if h:w.val < n then owner ⟨w.val,h⟩ else 0)
  group:=0
  slot:=slot

def Touched (u f n a : ℕ) :=
  HeaderCell u a ∨ (pairs u ≤ a ∧ a < pairs u+2*n) ∨ (base u 45 ≤ a ∧ a < base u 45+(f+n))

/-- These three intervals include low input words, both root-list/cursor banks,
the immutable registered stage and S44 node banks, and the high classifier archive. -/
theorem untouched_of_bands {u f n a : ℕ} (wide : 128 ≤ stride u) (nodes : 8*(f+n) ≤ stride u)
    (band : a < base u 1 ∨ (base u 12 ≤ a ∧ a < base u 45) ∨ base u 46 ≤ a) : ¬Touched u f n a := by
  change a < 2*stride u ∨ (13*stride u ≤ a ∧ a < 46*stride u) ∨ 47*stride u ≤ a at band
  change ¬((a=12*stride u+3*(stride u/4) ∨ a=12*stride u+3*(stride u/4)+1 ∨
    a=7*stride u+1 ∨ a=2*stride u ∨ a=2*stride u+3) ∨
    (12*stride u+1*(stride u/4) ≤ a ∧ a < 12*stride u+1*(stride u/4)+2*n) ∨
    (46*stride u ≤ a ∧ a < 46*stride u+(f+n)))
  omega

def output (u f n owners tick : ℕ) (m : Memory W) :=
  Reverse.sweep (reverseBanks W u f) (f+n)
    (TraceReceiverOwnerPairs.image owners (pairs u) n (headerImage u f n tick m))

/-- Framing the deterministic mount requires only the actual address layout.
Its input words, including all owner and parent values, may be arbitrary. -/
theorem output_frame {u f n owners target : ℕ} (room : Room W u f n owners target)
    (m : Memory W) (a : ℕ) (off : ¬Touched u f n a) :
    output u f n owners target m a=m a := by
  have bound:=room.bounds
  have high:=bound.rootRange;have own:=bound.owner;have word:=bound.word
  have fit : base u 45 < 2^W:=by omega
  change Reverse.sweep (reverseBanks W u f) (f+n) _ a=_
  rw [Reverse.sweep_frame (reverseBanks W u f) _ (f+n)
    (by change (base u 45:Word W).val+(f+n) ≤ 2^W;rw [Fin.val_cast_of_lt fit];omega) a
    (by change a<(base u 45:Word W).val ∨ (base u 45:Word W).val+(f+n) ≤ a
        rw [Fin.val_cast_of_lt fit];unfold Touched at off;omega)]
  rw [TraceReceiverOwnerPairs.outside _ _ _ _ a (by unfold Touched at off;omega)]
  exact (header_run bound m).2.frame a (fun h=>off (.inl h))

/-- The final S11 layer offset and S44 table pointer are still the words
written by the header instructions after the pair and reverse passes. -/
theorem output_descriptor {u f n owners target : ℕ} (room : Room W u f n owners target) (m : Memory W) :
    output u f n owners target m (desc u)=(f:Word W) ∧
      output u f n owners target m (desc u+1)=(base u 44:Word W) := by
  have bound:=room.bounds
  have pair:=bound.pair
  have past:=bound.desc
  have nodes:=bound.nodes
  have high:=bound.rootRange
  have owner:=bound.owner
  have word:=bound.word
  have dest : base u 45<2^W := by omega
  have fixed (j : Fin 2) : output u f n owners target m (desc u+j.val)=headerImage u f n target m (desc u+j.val) := by
    have col:=j.isLt
    change Reverse.sweep (reverseBanks W u f) (f+n) _ _=_
    rw [Reverse.sweep_frame (reverseBanks W u f) _ (f+n)
      (by change (base u 45:Word W).val+(f+n)≤2^W;rw [Fin.val_cast_of_lt dest];omega) _
      (Or.inl (by change desc u+j.val<(base u 45:Word W).val;rw [Fin.val_cast_of_lt dest];omega))]
    exact TraceReceiverOwnerPairs.outside _ _ _ _ _ (Or.inr (by omega))
  have loaded:=(header_run bound m).2
  exact ⟨(fixed 0).trans loaded.first,(fixed 1).trans loaded.pointer⟩

/-- The selected guard sees exactly the classifier-produced owner and the decoded target
on every chronological node. The other physical addresses retain their original words. -/
theorem run {u f n owners target : ℕ} (room : Room W u f n owners target)
    (C : Chronology (f+n)) (first : C.firstFinal=f) (owner : Fin n → Word W)
    (slot : Word W) (m : Memory W) (digits : ∀ i : Fin n,m (owners+i.val)=owner i) (tick : m target=slot)
    (parents : ∀ i : Fin (f+n),i.val < C.firstFinal → m (base u 44+8*i.val+1)=((C.parent i).val:Word W)) :
    let M:=output u f n owners target m
    (procedure W u f n owners target).Exec m M (ticks f n) ∧
    Selected.Recorded (data W u) (directory C owner slot) M ∧
    (M ((data W u) 4).val).val+(M ((data W u) 5).val).val=f+n ∧
    ∀ a,¬Touched u f n a → M a=m a := by
  intro M
  let h:=headerImage u f n target m
  let p:=TraceReceiverOwnerPairs.image owners (pairs u) n h
  have bounds:=room.bounds
  obtain ⟨ha,hb,hc,hd,he,hg,ho,ht⟩:=bounds
  have two : 2 < 2^W := by
    have sz:=room.fixed;have hi:=room.high
    change 47*stride u ≤ owners at hi
    omega
  have size : f+n < 2^W:=by omega
  obtain ⟨boot,head⟩:=header_run room.bounds m
  have pairRun : (TraceReceiverOwnerPairs.procedure W owners (pairs u) n).Exec h p (4+56*n) :=
    (TraceReceiverOwnerPairs.run owners (pairs u) n h (by omega) (by omega) (by omega) two)
  have stable (a : ℕ) (off : a < pairs u ∨ pairs u+2*n ≤ a) : p a=h a:=
    TraceReceiverOwnerPairs.outside owners (pairs u) n h a off
  have bank (a : ℕ) (off : ¬HeaderCell u a) : h a=m a:=head.frame a off
  have preserve (y : ℕ) (lo : base u 44 ≤ y) : p y=m y:=
    (stable y (.inr (by omega))).trans (bank y (by unfold HeaderCell;omega))
  have firstH : p (desc u)=(f:Word W):=(stable _ (.inr hc)).trans head.first
  have nodeH : p (desc u+1)=(base u 44:Word W):=(stable _ (.inr (by omega))).trans head.pointer
  have countH : p (base u 6+1)=(n:Word W):=(stable _ (.inl (by omega))).trans head.roots
  obtain ⟨back,roots,fr⟩:=reverse_run room.bounds C first p firstH nodeH countH
    (fun i hi=>(preserve _ (by omega)).trans (parents i hi))
  have after (a : ℕ) (off : a < base u 45 ∨ base u 45+(f+n) ≤ a) : M a=p a:=fr a off
  have rootWords (i : Fin (f+n)) : M (base u 45+i.val)=(C.root i:Word W):=roots i
  have pairWords (i : Fin n) : M (pairs u+2*i.val)=0 ∧ M (pairs u+2*i.val+1)=owner i := by
    have ci:=i.isLt
    have rows:=TraceReceiverOwnerPairs.columns owners (pairs u) n h i
    exact ⟨(after _ (.inl (by omega))).trans rows.1, (after _ (.inl (by omega))).trans
      (rows.2.trans ((bank _ (by unfold HeaderCell;omega)).trans (digits i)))⟩
  have group : M (base u 1)=0 := (after _ (.inl (by omega))).trans
    ((stable _ (.inl (by omega))).trans head.zero)
  have clock : M (base u 1+3)=slot := (after _ (.inl (by omega))).trans
    ((stable _ (.inl (by omega))).trans (head.clock.trans tick))
  refine ⟨?_,?_,?_,?_⟩
  · change (((header W u f n target).seq (TraceReceiverOwnerPairs.procedure W owners (pairs u) n)).seq
        (reverse W u)).Exec m (Reverse.sweep (reverseBanks W u f) (f+n) p) (ticks f n)
    have elapsed : ticks f n=23+(4+56*n)+(12+11*(f+n)) := by unfold ticks; omega
    rw [elapsed]
    intro P R K machine
    exact Procedure.Exec.then (Procedure.Exec.then boot pairRun) back machine
  · intro i j
    have ci:=i.isLt
    have bound:=C.root_lt i
    rw [first] at bound
    have fit : C.root i < n:=by omega
    let root : Fin n:=⟨C.root i,fit⟩
    have real : ((C.root i:ℕ):Word W).val=C.root i:=Fin.val_cast_of_lt (by omega)
    have off := pairWords root
    have aa : base u 45+i.val < 2^W:=by omega
    have bb : pairs u+2*C.root i+1 < 2^W:=by omega
    have baseRoom : base u 1+3 < 2^W:=by omega
    let ptr : Fin 5 → ℕ := ![base u 45+i.val,pairs u+2*C.root i,pairs u+2*C.root i+1,base u 1,base u 1+3]
    have atPtr (j : Fin 5) : Selected.addresses (data W u) (directory C owner slot) i j=(ptr j:Word W) := by
      fin_cases j <;> simp [Selected.addresses,data,directory,ptr,Nat.two_mul,Nat.cast_add]
    have within (j : Fin 5) : ptr j < 2^W:=by fin_cases j <;> dsimp [ptr] <;> omega
    rw [atPtr,Fin.val_cast_of_lt (within j)]
    fin_cases j
    · exact rootWords i
    · exact off.1
    · change M (pairs u+2*C.root i+1) =
          if h : ((C.root i : ℕ) : Word W).val < n then owner ⟨_,h⟩ else 0
      rw [dite_eq_left (by rw [real]; exact fit)]
      exact off.2.trans (congrArg owner (Fin.ext real.symm))
    · exact group
    · exact clock
  · change (M (desc u:Word W).val).val+(M ((base u 6+1:ℕ):Word W).val).val=f+n
    rw [Fin.val_cast_of_lt (by omega : desc u < 2^W),Fin.val_cast_of_lt (by omega : base u 6+1 < 2^W),
      after _ (.inl (by omega)),firstH,after _ (.inl (by omega)),countH,
      Fin.val_cast_of_lt (by omega : f < 2^W),Fin.val_cast_of_lt (by omega : n < 2^W)]
  · exact output_frame room m

end Hierarchy.TraceReceiverOwnerMount

end OAI
