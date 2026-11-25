import OAI.Hierarchy.DescentRegisteredOperandSource
import OAI.Hierarchy.DescentDatedOperandProgram

namespace OAI
/-! # Every fixed ordinary operand slot reads its genuine predecessor and preserves earlier returns -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {l : Layout} {w : ℕ}

namespace Banks
structure Registered (t : Banks l) (v : Fin l.jobs→Source l) (m : Memory w) : Prop where
  previous : ∀j p,Reads (t.book j p) ((v j).books p) l.lanes m
  header : ∀j f h g,let z:=l.index.symm j;
    (DescentOrdinaryAtomFieldRAM.ScalarOperand.take z.2.1 ((v j).books (DescentPriorOperandColumns.pageOf z.2.2 f) h g)).val=((v j).pointer h g).header f
  side : ∀j i,Reads (t.side j i) (fun h g=>sourceFields ((v j).fragment h g) (DescentPriorOperandColumns.sideIndex i)) l.lanes m
  route : ∀j i,Reads (t.route j i) ((v j).routed i) l.lanes m

variable {floor : ℕ} (t : Banks l) (v : Fin l.jobs→Source l)

def Returned (positive : 0<l.lanes) (floor : ℕ) (j : Fin l.jobs) (m : Memory w) :=
  ∀h g (f : Fin 5),digit (l.size+4) f.val (digit (outputWidth l.size) (lane g positive).val
    (m (l.output (l.slot floor j.val)+(row l.hosts l.groups l.lanes (position h g positive)).val)).val)=
      (resolve ((v j).compiled h g)).fields f

theorem registered_keep (early : t.Early floor w) {m o : Memory w} (prior : t.Registered v m)
    (keep : ∀j,j<floor → o j=m j) : t.Registered v o := by
  have transfer {b} (B : Bank) (fit : B.Fits w floor ∧ l.rows≤B.size) (x : Fin l.hosts→Fin l.groups→Cell b)
      (read : Reads B x l.lanes m) : Reads B x l.lanes o:=by
    intro q;exact (keep _ ((Nat.add_lt_add_left ((row _ _ _ q).isLt.trans_le fit.2) _).trans_le fit.1.2.2)).trans (read q)
  exact ⟨fun j p=>transfer _ (early.previous j p) _ (prior.previous j p),prior.header,
    fun j i=>transfer _ (early.side j i) _ (prior.side j i),fun j i=>transfer _ (early.route j i) _ (prior.route j i)⟩

theorem single (input : Memory w) (j : Fin l.jobs) (early : t.Early floor w) (prior : t.Registered v input)
    (room : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    let base:=l.slot floor j.val;let after_:=t.image base j input
    (t.one w base j).Exec input after_ (t.time base j) ∧ Returned v positive floor j after_ ∧
      (∀a,a<base ∨ l.slot floor (j.val+1)≤a→after_ a=input a) ∧ CheapCode (t.one w base j) := by
  intro base after_
  let ix:=l.index.symm j
  let R:=DescentPackedOperand.ROM.chart 0 l.size l.hosts l.groups l.lanes (fun _=>⟨0,0⟩)
  have slotFit:=l.within floor j
  have later (B : Bank) (fit : B.Fits w floor) : B.Fits w base:=⟨fit.1,fit.2.1,fit.2.2.trans slotFit.1⟩
  have end_ : l.output base+l.rowCap<2^w:=slotFit.2.trans_lt room
  have «prefix» : l.resolveBase base<2^w:=by
    have bound : l.resolveBase base≤l.output base+l.rowCap:=by unfold Layout.output;omega
    exact bound.trans_lt end_
  have run:=DescentPriorOperandColumns.execute_framed (t.book j) base (l.projected base) input (v j).books ix.2.2 ix.2.1
    (v j).pointer (v j).side (v j).size (t.side j) R (t.route j) (v j).routed
    (fun p=>later _ (early.previous j p).1) (fun p=>(early.previous j p).2) le_rfl (prior.previous j) (prior.header j)
    (fun i=>⟨later _ (early.side j i).1,(early.side j i).2⟩) (prior.side j)
    (fun i=>⟨later _ (early.route j i).1,(early.route j i).2⟩) (prior.route j) (v j).noCarry «prefix» word positive
    (by change l.resolveBase base+12*l.resolverPage+3*l.rowCap<2^w;unfold Layout.output at end_;omega)
  refine ⟨run.1,run.2.1,?_,run.2.2.2⟩
  intro a away;apply run.2.2.1 a
  rcases away with lo|hi
  · exact .inl lo
  · right;rw [←l.slot_end floor j.val] at hi
    change l.resolveBase base+12*l.resolverPage+3*l.rowCap≤a
    change l.resolveBase base+12*l.resolverPage+2*l.rowCap+l.rowCap≤a at hi
    omega

private theorem away (j i : Fin l.jobs) (different : j≠i) (q : Fin l.rows) :
    let loc:=l.output (l.slot floor j.val)+q.val
    loc<l.slot floor i.val ∨ l.slot floor (i.val+1)≤loc := by
  intro loc
  have cap : l.rows≤l.rowCap:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have bottom : l.slot floor j.val≤loc:=by
    dsimp only [loc,Layout.output,Layout.resolveBase,Layout.splice,Layout.projected];omega
  have top : loc<l.slot floor (j.val+1):=by rw [←l.slot_end];exact Nat.add_lt_add_left (q.isLt.trans_le cap) _
  have neq : j.val≠i.val:=fun h=>different (Fin.ext h)
  rcases lt_or_gt_of_ne neq with before|after
  · exact .inl (top.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_right _ before) _))
  · exact .inr ((Nat.add_le_add_left (Nat.mul_le_mul_right _ after) _).trans bottom)

theorem append_exec {w : ℕ} (A B : Procedure w) (a b c : Memory w) (u v : ℕ)
    (first : A.Exec a b u) (second : B.Exec b c v) (cheapA : CheapCode A) (cheapB : CheapCode B) :
    (A.seq B).Exec a c (u+v) ∧ CheapCode (A.seq B) :=
  ⟨@Procedure.Exec.then w A B a b c u v first second, @cheap_seq w A B cheapA cheapB⟩

set_option maxHeartbeats 600000 in
/-- Every occupied output survives the remaining visits. Later programs operate
on the actual preceding memory and read all old, route and side banks below the
same fixed floor, including when a visited slot is padding. -/
theorem run (m : Memory w) (early : t.Early floor w) (prior : t.Registered v m)
    (room : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    let done:=t.result floor m
    (t.program w floor).Exec m done (t.ticks floor) ∧ (∀j,Returned v positive floor j done) ∧
      (∀a,a<floor ∨ l.endAddress floor≤a→done a=m a) ∧ CheapCode (t.program w floor) :=by
  intro done
  have loop (jobs : List (Fin l.jobs)) (distinct : jobs.Nodup) (start : Memory w) (posted : t.Registered v start) :
      let last_:=t.state floor jobs start
      (t.code w floor jobs).Exec start last_ (t.cost floor jobs) ∧
        (∀j∈jobs,Returned v positive floor j last_) ∧
        (∀a,(∀j∈jobs,a<l.slot floor j.val ∨ l.slot floor (j.val+1)≤a)→last_ a=start a) ∧ CheapCode (t.code w floor jobs) :=by
    induction jobs generalizing start with
    | nil=>
      refine ⟨ProtocolRAM.program_exec [] start (by simp),by simp,fun _ _=>rfl,?_⟩
      exact program_cheap w []
    | cons j js tail=>
      let mid:=t.image (l.slot floor j.val) j start
      have one:=t.single v start j early posted room positive word
      have next:=t.registered_keep v early posted (o:=mid) (fun a h=>one.2.2.1 _ (.inl (h.trans_le (l.within floor j).1)))
      have rest:=tail distinct.of_cons mid next
      have both := append_exec (t.one w (l.slot floor j.val) j) (t.code w floor js)
        start mid (t.state floor js mid) (t.time (l.slot floor j.val) j) (t.cost floor js)
        one.1 rest.1 one.2.2.2 rest.2.2.2
      simp only [code,state,cost]
      refine ⟨both.1,?_,?_,?_⟩
      · intro ix mem
        rcases List.mem_cons.mp mem with hix|inside
        · subst ix
          intro h g f
          change digit (l.size+4) f.val (digit (outputWidth l.size) (lane g positive).val ((t.state floor js mid) _).val)=_
          have same:=rest.2.2.1 (l.output (l.slot floor j.val)+(row l.hosts l.groups l.lanes (position h g positive)).val)
            (fun i hi=>away j i (fun eqn=>(List.nodup_cons.mp distinct).1 (eqn.symm ▸ hi))
              (row l.hosts l.groups l.lanes (position h g positive)))
          rw [same];exact one.2.1 h g f
        · exact rest.2.1 ix inside
      · intro a held
        exact (rest.2.2.1 a (fun i hi=>held i (.tail _ hi))).trans (one.2.2.1 a (held j (.head _)))
      · intro P R K
        exact @both.2 P R K
  let jobs:=List.finRange l.jobs
  have ran:=loop jobs (List.nodup_finRange _) m prior
  refine ⟨ran.1,fun j=>ran.2.1 j (List.mem_finRange j),?_,ran.2.2.2⟩
  intro a outside
  apply ran.2.2.1
  intro j _
  rcases outside with lo|hi
  · exact .inl (lo.trans_le (l.within floor j).1)
  · exact .inr ((Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) floor).trans hi)

end Banks
end
end Hierarchy.DescentDatedPriorOperand

end OAI
