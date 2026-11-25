import OAI.Hierarchy.DescentDatedTaggedOperandBanks
import OAI.Hierarchy.DescentDatedOperandTagRead
import OAI.Hierarchy.DescentPriorOperandRawFields
import OAI.Hierarchy.DescentDatedOperandAny
import OAI.Hierarchy.DescentDatedOperandWordBank
import OAI.Hierarchy.DescentOperandLaneRead

namespace OAI
/-! # Running the original dated operand resolver on noncanonical unused reset fields -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {l : Layout} {floor w : ℕ} (t : Banks l) (b : Books l)
    (s : Fin l.jobs→Fin l.hosts→Fin l.groups→DescentPriorOperandColumns.Side l.size)
    (r : Fin l.jobs→Fin 3→Fin l.hosts→Fin l.groups→Cell (l.size+2))
    (room : ∀(j:Fin l.jobs) (h:Fin l.hosts) (g:Fin l.groups),11*(r j 1 h g).val+(r j 2 h g).val<2^(l.size+2))

namespace Banks

theorem single_tagged_words (m : Memory w) (j : Fin l.jobs) (early : t.Early floor w) (prior : t.Tagged b s r room m)
    (space : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    let base:=l.slot floor j.val
    let done:=t.image base j m
    (t.one w base j).Exec m done (t.time base j) ∧ Returned (decodedBooks b s r room) positive floor j done ∧
      Reads (wordBank l floor j) (fun h g=>DescentPackedOperand.word ((decodedBooks b s r room j).compiled h g)) l.lanes done ∧
      (∀a,a<base ∨ l.slot floor (j.val+1)≤a→done a=m a) ∧ CheapCode (t.one w base j) :=by
  intro base done
  have total:=t.any_one j m early space word
  let ix:=l.index.symm j
  let R:=DescentPackedOperand.ROM.chart 0 l.size l.hosts l.groups l.lanes (fun _=>⟨0,0⟩)
  let x:=fun h g=>readFragment (booksHeader b j h g) (s j h g)
  have sides (i : Fin 6) : Reads (t.side j i) (fun h g=>sourceFields (x h g)
      (DescentPriorOperandColumns.sideIndex i)) l.lanes m :=by
    simpa only [x, readFragment_side, Source.fragment, decodedBooks] using prior.side j i
  have limits:=l.within floor j
  have later (B : Bank) (fit : B.Fits w floor) : B.Fits w base:=⟨fit.1,fit.2.1,fit.2.2.trans limits.1⟩
  have end_ : l.output base+l.rowCap<2^w:=limits.2.trans_lt space
  have «prefix» : l.resolveBase base<2^w:=by
    have bound : l.resolveBase base≤l.output base+l.rowCap:=by unfold Layout.output;omega
    exact bound.trans_lt end_
  have returned:=DescentPriorOperandColumns.raw_resolved_fields (t.book j) base (l.projected base) m
    ((decodedBooks b s r room j).books) ix.2.2 ix.2.1 x (t.side j) R (t.route j) (r j)
    (fun p=>later _ (early.previous j p).1) (fun p=>(early.previous j p).2) le_rfl (prior.previous j)
    (fun f h g=>(readFragment_header (booksHeader b j h g) (s j h g) (prior.tags j h g) f).symm)
    (fun i=>⟨later _ (early.side j i).1,(early.side j i).2⟩) sides
    (fun i=>⟨later _ (early.route j i).1,(early.route j i).2⟩) (prior.route j) (room j) «prefix» word positive
    (by change l.resolveBase base+12*l.resolverPage+3*l.rowCap<2^w;unfold Layout.output at end_;omega)
  refine ⟨total.1,?_,?_,total.2⟩
  · intro h g f
    exact (returned.1 h g f).trans (congrArg (fun p : Key=>p.fields f) (decodedBooks_key b prior.tags s r room j h g))
  · let routed:=fun h g=>DescentOrdinaryLocalFragment.route (x h g) (r j 0 h g)
        (DescentPackedRawTicket.payload (r j 1) (r j 2) (room j) h g)
    have same : (fun h g=>DescentPackedOperand.word (routed h g))=
        (fun h g=>DescentPackedOperand.word ((decodedBooks b s r room j).compiled h g)) :=by
      funext h g
      unfold DescentPackedOperand.word
      congr 1
      funext f
      apply Fin.ext
      exact congrArg (fun key : Key=>key.fields f) (decodedBooks_key b prior.tags s r room j h g)
    rw [← same]
    intro p
    exact returned.2 p

theorem single_tagged (m : Memory w) (j : Fin l.jobs) (early : t.Early floor w) (prior : t.Tagged b s r room m)
    (space : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    let base:=l.slot floor j.val
    let done:=t.image base j m
    (t.one w base j).Exec m done (t.time base j) ∧ Returned (decodedBooks b s r room) positive floor j done ∧
      (∀a,a<base ∨ l.slot floor (j.val+1)≤a→done a=m a) ∧ CheapCode (t.one w base j) :=by
  have res:=t.single_tagged_words b s r room m j early prior space positive word
  exact ⟨res.1,res.2.1,res.2.2.2⟩

open private away from OAI.Hierarchy.DescentDatedOperandRun

theorem run_words_tagged (m : Memory w) (early : t.Early floor w) (prior : t.Tagged b s r room m)
    (space : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    ∀j,Reads (wordBank l floor j) (fun h g=>DescentPackedOperand.word ((decodedBooks b s r room j).compiled h g))
      l.lanes (t.result floor m) := by
  have loop (jobs : List (Fin l.jobs)) (distinct : jobs.Nodup) (start : Memory w) (posted : t.Tagged b s r room start) :
      (∀j∈jobs,Reads (wordBank l floor j) (fun h g=>DescentPackedOperand.word ((decodedBooks b s r room j).compiled h g))
        l.lanes (t.state floor jobs start)) ∧
      (∀a,(∀j∈jobs,a<l.slot floor j.val ∨ l.slot floor (j.val+1)≤ a)→t.state floor jobs start a=start a) := by
    induction jobs generalizing start with
    | nil=>exact ⟨by simp,fun _ _=>rfl⟩
    | cons j js ih=>
      let mid:=t.image (l.slot floor j.val) j start
      have one:=t.single_tagged_words b s r room start j early posted space positive word
      have next:=tagged_keep t b s r room early posted (o:=mid) (fun a h=>one.2.2.2.1 _ (.inl (h.trans_le (l.within floor j).1)))
      have tail:=ih distinct.of_cons mid next
      constructor
      · intro ix mem
        rcases List.mem_cons.mp mem with eqn|inside
        · subst ix
          intro p
          have keep:=tail.2 ((wordBank l floor j).base+(row l.hosts l.groups l.lanes p).val)
            (fun i hi=>away j i (fun eqn=>(List.nodup_cons.mp distinct).1 (eqn.symm ▸ hi))
              (row l.hosts l.groups l.lanes p))
          exact keep.trans (one.2.2.1 p)
        · exact tail.1 ix inside
      · intro a held
        exact (tail.2 a (fun i hi=>held i (.tail _ hi))).trans (one.2.2.2.1 a (held j (.head _)))
  intro j
  exact (loop (List.finRange l.jobs) (List.nodup_finRange _) m prior).1 j (List.mem_finRange j)

/-- Retrieve the five scalar fields at each live lane from its completed packed physical row. -/
theorem run_tagged (m : Memory w) (early : t.Early floor w) (prior : t.Tagged b s r room m)
    (space : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    let done:=t.result floor m
    (t.program w floor).Exec m done (t.ticks floor) ∧ (∀j,Returned (decodedBooks b s r room) positive floor j done) ∧
      (∀a,a<floor ∨ l.endAddress floor≤a→done a=m a) ∧ CheapCode (t.program w floor) :=by
  have run:=t.any m early space word
  have words:=t.run_words_tagged b s r room m early prior space positive word
  have fit : outputWidth l.size*l.lanes≤w:=by
    have fieldSize : outputWidth l.size≤unit l.size:=by unfold outputWidth unit;omega
    calc
      outputWidth l.size*l.lanes ≤ unit l.size*l.lanes := Nat.mul_le_mul_right _ fieldSize
      _ = l.lanes*unit l.size := Nat.mul_comm ..
      _ ≤ w := word.trans (Nat.div_le_self w 2)
  refine ⟨run.1,?_,run.2⟩
  intro j h g f
  have read:=DescentOperandStateBanks.Reset.lane_read (wordBank l floor j).base
    (fun v i=>DescentPackedOperand.word ((decodedBooks b s r room j).compiled v i)) (t.result floor m)
    (words j) fit positive h g
  exact (congrArg (digit (l.size+4) f.val) read).trans (word_read _ f)

end Banks
end
end Hierarchy.DescentDatedPriorOperand

end OAI
