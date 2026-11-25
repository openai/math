import OAI.Hierarchy.DescentPriorOperandResolve
import OAI.Hierarchy.DescentOperandResolverWords

namespace OAI
/-! # Scalar observation of the unchanged native projection, ticket and resolution phases -/
namespace Hierarchy.DescentPriorOperandColumns
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand
open DescentOrdinaryAtomFieldRAM
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

local notation "after_" => image old (k+2) K M nr base out m

theorem measured_raw_fields (arg : Fin slots) (node : Fin K) (x : Fin H→Fin G→Fragment k)
    (side : Fin 6→Bank) (rest : Layout) (low : ∀p,(old p).Fits w base)
    (capacity : ∀p,nr≤(old p).size) (apart : base+K*2^(((k+2)*K)*M)≤out)
    (room : out+((7*slots)*K)*nr<2^w) (prior : ∀p,Reads (old p) (books p) M m)
    (header : ∀f h g,ScalarOperand.take node (books (pageOf arg f) h g)=sourceFields (x h g) (headerIndex f))
    (sideLow : ∀i,(side i).base+nr≤base)
    (sides : ∀i,Reads (side i) (fun h g=>sourceFields (x h g) (sideIndex i)) M m) :
    let L:=selectedLayout H G M out arg node side rest
    ∀i,Reads (L.field i) (fun h g=>sourceFields (x h g) i) M after_ := by
  intro L
  obtain ⟨_,emitted,frame,_⟩:=run old base out m books low capacity apart room prior
  have head (f : Fin 4) : Reads (fieldBank out nr (pageOf arg f) node) (fun h g=>sourceFields (x h g) (headerIndex f)) M after_ := by
    have eqn : (fun h g=>ScalarOperand.take node (books (pageOf arg f) h g)) = (fun h g=>sourceFields (x h g) (headerIndex f)) := by
      funext h g;exact header f h g
    simpa only [eqn] using emitted (pageOf arg f) node
  have tail (i : Fin 6) : Reads (side i) (fun h g=>sourceFields (x h g) (sideIndex i)) M after_ := by
    intro p
    have h : (side i).base+(row H G M p).val<base:=(Nat.add_lt_add_left (row H G M p).isLt _).trans_le (sideLow i)
    exact (frame _ (.inl h) (.inl (h.trans_le ((Nat.le_add_right ..).trans apart)))).trans (sides i p)
  intro i
  fin_cases i
  · exact head 0
  · exact tail 0
  · exact head 1
  · exact head 2
  · exact head 3
  · exact tail 1
  · exact tail 2
  · exact tail 3
  · exact tail 4
  · exact tail 5

theorem raw_resolved_fields (arg : Fin slots) (node : Fin K) (x : Fin H→Fin G→Fragment k)
    (side : Fin 6→Bank) (rest : Layout) (extra : Fin 3→Bank) (vals : Fin 3→Fin H→Fin G→Cell (k+2))
    (low : ∀p,(old p).Fits w base) (capacity : ∀p,nr≤(old p).size) (spaced : base+K*2^(((k+2)*K)*M)≤out)
    (prior : ∀p,Reads (old p) (books p) M m)
    (header : ∀f h g,take node (books (pageOf arg f) h g)=sourceFields (x h g) (headerIndex f))
    (sideFits : ∀i,(side i).Fits w base ∧ nr≤(side i).size)
    (sideReads : ∀i,Reads (side i) (fun h g=>sourceFields (x h g) (sideIndex i)) M m)
    (extraFits : ∀i,(extra i).Fits w base ∧ nr≤(extra i).size) (extraReads : ∀i,Reads (extra i) (vals i) M m)
    (within : ∀h g,11*(vals 1 h g).val+(vals 2 h g).val<2^(k+2))
    (room : DescentOrdinaryLocalFragment.finish next_ k M nr<2^w) (word : M*unit k≤w/2) (lanes : 0<M)
    (space : ROM.maskBase (DescentOrdinaryLocalFragment.finish next_ k M nr) k M+3*ROM.rows H G M<2^w) :
    let e:=fun i : Fin 3=>Expr.lookup (extra i) .row
    let L:=(selectedLayout H G M out arg node side rest).field
    let last_:=DescentOrdinaryLocalFragment.finish next_ k M nr
    let cl:=fun h g=>DescentOrdinaryLocalFragment.route (x h g) (vals 0 h g) (DescentPackedRawTicket.payload (vals 1) (vals 2) within h g)
    let finished:=DescentOrdinaryLocalFragment.outputMemory next_ k H G M L (e 0) (e 1) (e 2) (image old (k+2) K M nr base out m)
    (∀h g (f : Fin 5),digit (k+4) f.val (digit (outputWidth k) (lane g lanes).val
      (finished (ROM.output last_ k H G M+(row H G M (position h g lanes)).val)).val)=(resolve (cl h g)).fields f) ∧
      ∀p : Row H G M,finished (ROM.output last_ k H G M+(row H G M p).val)=
        ((data (fun h g=>DescentPackedOperand.word (cl h g)) p).val:ℕ) :=by
  intro e L last_ cl finished
  let mid:=image old (k+2) K M nr base out m
  have nextRoom : next_<2^w:=by
    apply lt_of_le_of_lt _ room
    simp only [DescentOrdinaryLocalFragment.finish,DescentOrdinaryLocalFragment.specEnd];omega
  have outputRoom : out+co*nr<2^w:=(Nat.le_add_right ..).trans_lt nextRoom
  have monotone : base ≤ next_ :=
    calc
      base ≤ out := (Nat.le_add_right ..).trans spaced
      _ ≤ out+co*nr := Nat.le_add_right ..
      _ ≤ next_ := Nat.le_add_right ..
  have onward (B : Bank) (h : B.Fits w base) : B.Fits w next_:=⟨h.1,h.2.1,h.2.2.trans monotone⟩
  have saved (B : Bank) (fit : B.Fits w base) (count : nr≤B.size) (y : Fin H→Fin G→Cell (k+2)) (held : Reads B y M m) : Reads B y M mid := by
    intro q
    have small : B.base+(row H G M q).val<base:=(Nat.add_lt_add_left ((row H G M q).isLt.trans_le count) _).trans_le fit.2.2
    exact (frame old (k+2) K M nr base out m _ (.inl small) (.inl (small.trans_le ((Nat.le_add_right ..).trans spaced)))).trans (held q)
  have read:=measured_raw_fields old base out m books arg node x side rest low capacity spaced outputRoom
    prior header (fun i=>(Nat.add_le_add_left (sideFits i).2 _).trans (sideFits i).1.2.2) sideReads
  have geometry : ∀i,(L i).Fits w next_ ∧ nr≤(L i).size:=by
    have heads (f : Fin 4):=returned_bank out nr (pageOf arg f) node nextRoom
    have tails (f : Fin 6):=(And.intro (onward (side f) (sideFits f).1) (sideFits f).2)
    exact fields_forall (fun b : Bank => b.Fits w next_ ∧ nr ≤ b.size)
      (fun f => fieldBank out nr (pageOf arg f) node) side heads tails
  have extRead (i : Fin 3) : Source (e i) (vals i) M mid :=
    source_column _ next_ (onward _ (extraFits i).1) mid _ (extraFits i).2 (saved _ (extraFits i).1 (extraFits i).2 _ (extraReads i))
  have extFits (i : Fin 3) : (e i).Fits w next_:=⟨onward _ (extraFits i).1,trivial⟩
  have compiled:=DescentOrdinaryLocalFragment.execute_framed next_ L (e 0) (e 1) (e 2) x (vals 0) (vals 1) (vals 2) mid within
    (fun i=>(geometry i).1) (fun i=>(geometry i).2) read (extFits 0) (extFits 1) (extFits 2) (extRead 0) (extRead 1) (extRead 2) room word lanes space
  exact ⟨compiled.2.1,DescentOrdinaryLocalFragment.output_words next_ L (e 0) (e 1) (e 2)
    x (vals 0) (vals 1) (vals 2) mid within (fun i=>(geometry i).1) (fun i=>(geometry i).2)
    read (extFits 0) (extFits 1) (extFits 2) (extRead 0) (extRead 1) (extRead 2) room word space⟩

end
end Hierarchy.DescentPriorOperandColumns

end OAI
