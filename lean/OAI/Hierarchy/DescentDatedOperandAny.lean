import OAI.Hierarchy.DescentDatedOperandRun

namespace OAI
/-! # Total physical ordinary operand time on all old words, including malformed and vacant rows -/
namespace Hierarchy.DescentDatedPriorOperand.Banks
open DescentSIMDLookup DescentOperandStateBanks DescentPackedOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {l : DescentDatedPriorOperand.Layout} {w floor : ℕ} (t : DescentDatedPriorOperand.Banks l)

theorem any_one (j : Fin l.jobs) (m : Memory w) (early : t.Early floor w)
    (room : l.endAddress floor<2^w) (word : l.lanes*unit l.size≤w/2) :
    let base:=l.slot floor j.val;let next_:=t.image base j m
    (t.one w base j).Exec m next_ (t.time base j) ∧
    (∀a,a<base ∨ l.slot floor (j.val+1)≤a→next_ a=m a) ∧ CheapCode (t.one w base j) :=by
  intro base next_
  let out:=l.projected base;let start:=l.splice base
  let mid:=DescentPriorOperandColumns.image (t.book j) (l.size+2) l.nodes l.lanes l.rows base out m
  have limits:=l.within floor j
  have high : l.output base+l.rowCap<2^w:=limits.2.trans_lt room
  have ends : start≤l.output base+l.rowCap:=by dsimp [Layout.output,Layout.resolveBase,start];omega
  have sr : start<2^w:=ends.trans_lt high
  have bound : out+l.columns*l.rows<2^w:=(Nat.le_add_right ..).trans_lt sr
  have mo : floor ≤ start:=by
    apply limits.1.trans;change base≤base+l.dictionary+l.columns*l.rows+l.rowCap;omega
  have widen (B : Bank) {y : ℕ} (fit : B.Fits w floor) (h : floor≤y):B.Fits w y:=⟨fit.1,fit.2.1,fit.2.2.trans h⟩
  have geom : ∀i,(t.fields base j i).Fits w start ∧ l.rows≤(t.fields base j i).size:=by
    let ix:=l.index.symm j
    have heads (f : Fin 4):=DescentPriorOperandColumns.returned_bank out l.rows (DescentPriorOperandColumns.pageOf ix.2.2 f) ix.2.1 sr
    have tails (i : Fin 6):=And.intro (widen _ (early.side j i).1 mo) (early.side j i).2
    exact DescentPriorOperandColumns.fields_forall (fun b : Bank => b.Fits w start ∧ l.rows ≤ b.size)
      (fun f => DescentPriorOperandColumns.fieldBank out l.rows
        (DescentPriorOperandColumns.pageOf ix.2.2 f) ix.2.1) (t.side j) heads tails
  have fits (i : Fin 3) : (t.args j i).Fits w start:=⟨widen _ (early.route j i).1 mo,trivial⟩
  have last:=DescentOrdinaryLocalFragment.any start l.size l.hosts l.groups l.lanes w (t.fields base j) (t.args j 0) (t.args j 1) (t.args j 2) mid
    (fun i=>(geom i).1) (fun i=>(geom i).2) (fits 0) (fits 1) (fits 2) word
    (by change l.resolveBase base+12*l.resolverPage+3*l.rowCap<2^w;unfold Layout.output at high;omega)
  have fst : (DescentPriorOperandColumns.program (t.book j) (l.size+2) l.nodes l.lanes l.rows w base out).Exec m mid
      (DescentPriorOperandColumns.ticks (t.book j) (l.size+2) l.nodes l.lanes l.rows base out):=
    DescentPriorOperandColumns.exec (t.book j) (l.size+2) l.nodes l.lanes l.rows base out m
      (fun p=>widen _ (early.previous j p).1 limits.1) le_rfl bound
  refine ⟨(by intro P R K machine;exact Procedure.Exec.then fst last.1 machine),?_,
    cheap_seq (DescentPriorOperandColumns.cheap (t.book j) (l.size+2) l.nodes l.lanes l.rows w base out) last.2.2⟩
  intro a away
  rcases away with lower|upper
  · have b : base≤out:=Nat.le_add_right ..
    have z : base ≤ start:=by change base≤base+_+_+_;omega
    exact (last.2.1 _ (.inl (lower.trans_le z))).trans (DescentPriorOperandColumns.frame _ _ _ _ _ _ _ m _ (.inl lower) (.inl (lower.trans_le b)))
  · rw [←l.slot_end floor j.val] at upper
    have all_ : DescentOrdinaryLocalFragment.endAddress start l.size l.hosts l.groups l.lanes≤a:=by
      change l.resolveBase base+12*l.resolverPage+3*l.rowCap≤a
      change l.resolveBase base+12*l.resolverPage+2*l.rowCap+l.rowCap≤a at upper;omega
    have outEnd : out+l.columns*l.rows≤a:= (Nat.le_add_right ..).trans (ends.trans upper)
    exact (last.2.1 _ (.inr all_)).trans (DescentPriorOperandColumns.frame _ _ _ _ _ _ _ m _ (.inr ((Nat.le_add_right ..).trans outEnd)) (.inr outEnd))

set_option maxHeartbeats 600000 in
theorem any (m : Memory w) (early : t.Early floor w) (room : l.endAddress floor<2^w) (word : l.lanes*unit l.size≤w/2) :
    let done:=t.result floor m
    (t.program w floor).Exec m done (t.ticks floor) ∧ (∀a,a<floor ∨ l.endAddress floor≤a→done a=m a) ∧ CheapCode (t.program w floor) :=by
  intro done
  have loop (jobs : List (Fin l.jobs)) (start : Memory w) :
      (t.code w floor jobs).Exec start (t.state floor jobs start) (t.cost floor jobs) ∧
      (∀a,a<floor ∨ l.endAddress floor≤a→t.state floor jobs start a=start a) ∧ CheapCode (t.code w floor jobs) :=by
    induction jobs generalizing start with
    | nil=>exact ⟨ProtocolRAM.program_exec [] start (by simp),fun _ _=>rfl,program_cheap w []⟩
    | cons j js ih=>
      have head:=t.any_one j start early room word
      have tail:=ih (t.image (l.slot floor j.val) j start)
      let base := l.slot floor j.val
      let mid := t.image base j start
      have both := append_exec (t.one w base j) (t.code w floor js) start mid
        (t.state floor js mid) (t.time base j) (t.cost floor js) head.1 tail.1 head.2.2 tail.2.2
      simp only [code,state,cost]
      refine ⟨both.1,?_,?_⟩
      · intro a away;apply (tail.2.1 a away).trans;apply head.2.1
        rcases away with left|right
        · exact .inl (left.trans_le (l.within floor j).1)
        · exact .inr ((Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) floor).trans right)
      · intro P R K
        exact @both.2 P R K
  exact loop _ m
end
end Hierarchy.DescentDatedPriorOperand.Banks

end OAI
