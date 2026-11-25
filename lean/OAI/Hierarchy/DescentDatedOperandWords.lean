import OAI.Hierarchy.DescentDatedOperandWordBank
import OAI.Hierarchy.DescentDatedOperandRun
import OAI.Hierarchy.DescentOperandResolverWords

namespace OAI
/-! Whole packed rows retained by the actual dated ordinary operand pass. -/
namespace Hierarchy.DescentPriorOperandColumns
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand (take)
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w k H G M K slots : ℕ}

variable (old : Pages slots→Bank) (base out : ℕ) (m : Memory w) (books : Pages slots→Fin H→Fin G→Cell ((k+2)*K))
local notation "nr" => H*chunks G M
local notation "co" => (7*slots)*K
local notation "next_" => endAddress out co nr

theorem output_words (arg : Fin slots) (node : Fin K) (ptr : Fin H→Fin G→Pointer)
    (route : Fin H→Fin G→Side k) (sizes : ∀h g f,(ptr h g).header f<2^(k+2))
    (side : Fin 6→Bank) (rest : Layout) (extra : Fin 3→Bank) (vals : Fin 3→Fin H→Fin G→Cell (k+2))
    (low : ∀p,(old p).Fits w base) (capacity : ∀p,nr≤(old p).size) (spaced : base+K*2^(((k+2)*K)*M)≤out)
    (prior : ∀p,Reads (old p) (books p) M m)
    (header : ∀f h g,(take node (books (pageOf arg f) h g)).val=(ptr h g).header f)
    (sideFits : ∀i,(side i).Fits w base ∧ nr≤(side i).size)
    (sideReads : ∀i,Reads (side i) (fun h g=>sourceFields ((route h g).withHeader (ptr h g) (sizes h g)) (sideIndex i)) M m)
    (extraFits : ∀i,(extra i).Fits w base ∧ nr≤(extra i).size) (extraReads : ∀i,Reads (extra i) (vals i) M m)
    (within : ∀h g,11*(vals 1 h g).val+(vals 2 h g).val<2^(k+2))
    (room : DescentOrdinaryLocalFragment.finish next_ k M nr<2^w) (word : M*unit k≤w/2) (_lanes : 0<M)
    (space : ROM.maskBase (DescentOrdinaryLocalFragment.finish next_ k M nr) k M+3*ROM.rows H G M<2^w) :
    let e:=fun i : Fin 3=>Expr.lookup (extra i) .row
    let L:=(selectedLayout H G M out arg node side rest).field
    let cl:=fun h g=>DescentOrdinaryLocalFragment.route ((route h g).withHeader (ptr h g) (sizes h g)) (vals 0 h g) (DescentPackedRawTicket.payload (vals 1) (vals 2) within h g)
    let finished:=DescentOrdinaryLocalFragment.outputMemory next_ k H G M L (e 0) (e 1) (e 2) (image old (k+2) K M nr base out m)
    ∀p : Row H G M,finished (ROM.output (DescentOrdinaryLocalFragment.finish next_ k M nr) k H G M+
      (row H G M p).val)=((data (fun h g=>DescentPackedOperand.word (cl h g)) p).val:ℕ) := by
  intro e L cl finished
  let mid:=image old (k+2) K M nr base out m
  let x:=fun h g=>(route h g).withHeader (ptr h g) (sizes h g)
  have nextRoom : next_<2^w:=by
    apply lt_of_le_of_lt _ room
    simp only [DescentOrdinaryLocalFragment.finish,DescentOrdinaryLocalFragment.specEnd];omega
  have outputRoom : out+co*nr<2^w:=(Nat.le_add_right ..).trans_lt nextRoom
  have base_le_out : base ≤ out := (Nat.le_add_right ..).trans spaced
  have monotone : base ≤ next_ :=
    ((base_le_out.trans (Nat.le_add_right out (co * nr))).trans (Nat.le_add_right ..))
  have onward (B : Bank) (h : B.Fits w base) : B.Fits w next_:=⟨h.1,h.2.1,h.2.2.trans monotone⟩
  have saved (B : Bank) (fit : B.Fits w base) (count : nr≤B.size) (y : Fin H→Fin G→Cell (k+2)) (held : Reads B y M m) : Reads B y M mid := by
    intro q
    have small : B.base+(row H G M q).val<base:=(Nat.add_lt_add_left ((row H G M q).isLt.trans_le count) _).trans_le fit.2.2
    exact (frame old (k+2) K M nr base out m _ (.inl small) (.inl (small.trans_le ((Nat.le_add_right ..).trans spaced)))).trans (held q)
  have read:=measured_fields old base out m books arg node ptr route sizes side rest low capacity spaced outputRoom
    prior header (fun i=>(Nat.add_le_add_left (sideFits i).2 _).trans (sideFits i).1.2.2) sideReads
  have geometry : ∀i,(L i).Fits w next_ ∧ nr≤(L i).size:=by
    have heads (f : Fin 4):=returned_bank out nr (pageOf arg f) node nextRoom
    have tails (f : Fin 6):=(And.intro (onward (side f) (sideFits f).1) (sideFits f).2)
    intro i
    fin_cases i
    · exact heads 0
    · exact tails 0
    · exact heads 1
    · exact heads 2
    · exact heads 3
    · exact tails 1
    · exact tails 2
    · exact tails 3
    · exact tails 4
    · exact tails 5
  have extRead (i : Fin 3) : Source (e i) (vals i) M mid :=
    source_column _ next_ (onward _ (extraFits i).1) mid _ (extraFits i).2 (saved _ (extraFits i).1 (extraFits i).2 _ (extraReads i))
  have extFits (i : Fin 3) : (e i).Fits w next_:=⟨onward _ (extraFits i).1,trivial⟩
  exact DescentOrdinaryLocalFragment.output_words next_ L (e 0) (e 1) (e 2) x (vals 0) (vals 1) (vals 2) mid within
    (fun i=>(geometry i).1) (fun i=>(geometry i).2) read (extFits 0) (extFits 1) (extFits 2) (extRead 0) (extRead 1) (extRead 2) room word space

end
end Hierarchy.DescentPriorOperandColumns
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {l : Layout} {w : ℕ}

namespace Banks
variable {floor : ℕ} (t : Banks l) (v : Fin l.jobs→Source l)

theorem single_words (input : Memory w) (j : Fin l.jobs) (early : t.Early floor w) (prior : t.Registered v input)
    (room : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    Reads (wordBank l floor j) (fun h g=>DescentPackedOperand.word ((v j).compiled h g)) l.lanes
      (t.image (l.slot floor j.val) j input) := by
  let base:=l.slot floor j.val
  let ix:=l.index.symm j
  let R:=DescentPackedOperand.ROM.chart 0 l.size l.hosts l.groups l.lanes (fun _=>⟨0,0⟩)
  have slotFit:=l.within floor j
  have later (B : Bank) (fit : B.Fits w floor) : B.Fits w base:=⟨fit.1,fit.2.1,fit.2.2.trans slotFit.1⟩
  have end_ : l.output base+l.rowCap<2^w:=slotFit.2.trans_lt room
  have «prefix» : l.resolveBase base<2^w:=by
    have bound : l.resolveBase base≤l.output base+l.rowCap:=by unfold Layout.output;omega
    exact bound.trans_lt end_
  exact DescentPriorOperandColumns.output_words (t.book j) base (l.projected base) input (v j).books ix.2.2 ix.2.1
    (v j).pointer (v j).side (v j).size (t.side j) R (t.route j) (v j).routed
    (fun p=>later _ (early.previous j p).1) (fun p=>(early.previous j p).2) le_rfl (prior.previous j) (prior.header j)
    (fun i=>⟨later _ (early.side j i).1,(early.side j i).2⟩) (prior.side j)
    (fun i=>⟨later _ (early.route j i).1,(early.route j i).2⟩) (prior.route j) (v j).noCarry «prefix» word positive
    (by change l.resolveBase base+12*l.resolverPage+3*l.rowCap<2^w;unfold Layout.output at end_;omega)


open private away from OAI.Hierarchy.DescentDatedOperandRun

theorem run_words (m : Memory w) (early : t.Early floor w) (prior : t.Registered v m)
    (room : l.endAddress floor<2^w) (positive : 0<l.lanes) (word : l.lanes*unit l.size≤w/2) :
    ∀j,Reads (wordBank l floor j) (fun h g=>DescentPackedOperand.word ((v j).compiled h g))
      l.lanes (t.result floor m) := by
  have loop (jobs : List (Fin l.jobs)) (distinct : jobs.Nodup) (start : Memory w) (posted : t.Registered v start) :
      (∀j∈jobs,Reads (wordBank l floor j) (fun h g=>DescentPackedOperand.word ((v j).compiled h g))
        l.lanes (t.state floor jobs start)) ∧
      (∀a,(∀j∈jobs,a<l.slot floor j.val ∨ l.slot floor (j.val+1)≤ a)→t.state floor jobs start a=start a) := by
    induction jobs generalizing start with
    | nil=>exact ⟨by simp,fun _ _=>rfl⟩
    | cons j js ih=>
      let mid:=t.image (l.slot floor j.val) j start
      have one:=t.single v start j early posted room positive word
      have next:=t.registered_keep v early posted (o:=mid) (fun a h=>one.2.2.1 _ (.inl (h.trans_le (l.within floor j).1)))
      have tail:=ih distinct.of_cons mid next
      constructor
      · intro ix mem
        rcases List.mem_cons.mp mem with eqn|inside
        · subst ix
          intro p
          have keep:=tail.2 ((wordBank l floor j).base+(row l.hosts l.groups l.lanes p).val)
            (fun i hi=>away j i (fun eqn=>(List.nodup_cons.mp distinct).1 (eqn.symm ▸ hi)) _)
          exact keep.trans (t.single_words v start j early posted room positive word p)
        · exact tail.1 ix inside
      · intro a held
        exact (tail.2 a (fun i hi=>held i (.tail _ hi))).trans (one.2.2.1 a (held j (.head _)))
  intro j
  exact (loop (List.finRange l.jobs) (List.nodup_finRange _) m prior).1 j (List.mem_finRange j)

end Banks
end
end Hierarchy.DescentDatedPriorOperand

end OAI
