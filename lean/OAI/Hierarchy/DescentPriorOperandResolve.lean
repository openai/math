import OAI.Hierarchy.DescentPriorOperandFragment
import OAI.Hierarchy.DescentOrdinaryFragmentImage

namespace OAI
/-! # Execution of the measured previous operand and its genuine local cable motion -/
namespace Hierarchy.DescentPriorOperandColumns
open DescentSIMDLookup DescentPackedColony DescentOperandStateBanks DescentPackedOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand (take)
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w k H G M K slots : ℕ}

/-- Later short-header lookups may read anywhere in the rounded bank, even
though only its `rows` genuine values are written. -/
def endAddress (out count rows : ℕ) := out+count*rows+2^Nat.clog 2 (rows+1)

theorem fields_forall (P : Bank → Prop) (header : Fin 4 → Bank) (side : Fin 6 → Bank)
    (heads : ∀ f, P (header f)) (tails : ∀ f, P (side f)) (i : Fin 10) :
    P (fields header side i) := by
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

theorem returned_bank {P K w : ℕ} (out rows : ℕ) (p : Fin P) (j : Fin K)
    (room : endAddress out (P*K) rows<2^w) :
    (fieldBank out rows p j).Fits w (endAddress out (P*K) rows) ∧ rows≤(fieldBank out rows p j).size := by
  let idx:Fin (P*K):=finProdFinEquiv (p,j)
  have before:=Nat.mul_le_mul_right rows idx.isLt.le
  have size : rows≤2^Nat.clog 2 (rows+1):=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have end_ : (fieldBank out rows p j).base+(fieldBank out rows p j).size≤endAddress out (P*K) rows:=by
    change out+idx.val*rows+2^Nat.clog 2 (rows+1)≤out+(P*K)*rows+2^Nat.clog 2 (rows+1);omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt room),end_⟩,size⟩

variable (old : Pages slots→Bank) (base out : ℕ) (m : Memory w) (books : Pages slots→Fin H→Fin G→Cell ((k+2)*K))
local notation "nr" => H*chunks G M
local notation "co" => (7*slots)*K
local notation "next_" => endAddress out co nr

/-- The three numerical route columns are read on the original state, after
the issuing roster program. They are retained through old-book projection. -/
theorem execute_framed (arg : Fin slots) (node : Fin K) (ptr : Fin H→Fin G→Pointer)
    (route : Fin H→Fin G→Side k) (sizes : ∀h g f,(ptr h g).header f<2^(k+2))
    (side : Fin 6→Bank) (rest : Layout) (extra : Fin 3→Bank) (vals : Fin 3→Fin H→Fin G→Cell (k+2))
    (low : ∀p,(old p).Fits w base) (capacity : ∀p,nr≤(old p).size) (spaced : base+K*2^(((k+2)*K)*M)≤out)
    (prior : ∀p,Reads (old p) (books p) M m)
    (header : ∀f h g,(take node (books (pageOf arg f) h g)).val=(ptr h g).header f)
    (sideFits : ∀i,(side i).Fits w base ∧ nr≤(side i).size)
    (sideReads : ∀i,Reads (side i) (fun h g=>sourceFields ((route h g).withHeader (ptr h g) (sizes h g)) (sideIndex i)) M m)
    (extraFits : ∀i,(extra i).Fits w base ∧ nr≤(extra i).size) (extraReads : ∀i,Reads (extra i) (vals i) M m)
    (within : ∀h g,11*(vals 1 h g).val+(vals 2 h g).val<2^(k+2))
    (room : DescentOrdinaryLocalFragment.finish next_ k M nr<2^w) (word : M*unit k≤w/2) (lanes : 0<M)
    (space : ROM.maskBase (DescentOrdinaryLocalFragment.finish next_ k M nr) k M+3*ROM.rows H G M<2^w) :
    let e:=fun i : Fin 3=>Expr.lookup (extra i) .row
    let L:=(selectedLayout H G M out arg node side rest).field
    let stage:=DescentOrdinaryLocalFragment.program next_ k M nr w L (e 0) (e 1) (e 2)
    let last_:=DescentOrdinaryLocalFragment.finish next_ k M nr
    let resolveStage:=ROM.run last_ k H G M w (DescentOrdinaryLocalFragment.fields next_ k M nr L)
    let program_ := (program old (k+2) K M nr w base out).seq (stage.seq resolveStage)
    let cl:=fun h g=>DescentOrdinaryLocalFragment.route ((route h g).withHeader (ptr h g) (sizes h g)) (vals 0 h g) (DescentPackedRawTicket.payload (vals 1) (vals 2) within h g)
    let finished:=DescentOrdinaryLocalFragment.outputMemory next_ k H G M L (e 0) (e 1) (e 2) (image old (k+2) K M nr base out m)
    let cost:=ticks old (k+2) K M nr base out+DescentOrdinaryLocalFragment.time next_ k H G M L (e 0) (e 1) (e 2)
    program_.Exec m finished cost ∧ (∀h g (f : Fin 5),digit (k+4) f.val (digit (outputWidth k) (lane g lanes).val
      (finished (ROM.output last_ k H G M+(row H G M (position h g lanes)).val)).val)=(resolve (cl h g)).fields f) ∧
    (∀a,a<base ∨ DescentOrdinaryLocalFragment.endAddress next_ k H G M≤a→finished a=m a) ∧ CheapCode program_ := by
  intro e L stage last_ resolveStage program_ cl finished cost
  let mid:=image old (k+2) K M nr base out m
  let x:=fun h g=>(route h g).withHeader (ptr h g) (sizes h g)
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
  have read:=measured_fields old base out m books arg node ptr route sizes side rest low capacity spaced outputRoom
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
  have first_:=run old base out m books low capacity spaced outputRoom prior
  refine ⟨(by intro P₀ R K₀ machine;exact Procedure.Exec.then first_.1 compiled.1 machine),compiled.2.1,?_,cheap_seq first_.2.2.2 compiled.2.2.2⟩
  intro a away
  have high : next_≤DescentOrdinaryLocalFragment.endAddress next_ k H G M:=by
    simp only [DescentOrdinaryLocalFragment.endAddress,ROM.endAddress,ROM.maskBase,DescentOrdinaryLocalFragment.finish,DescentOrdinaryLocalFragment.specEnd];omega
  have priorEnd : out+co*nr≤next_:=Nat.le_add_right ..
  rcases away with lo|hi
  · exact (compiled.2.2.1 _ (.inl (lo.trans_le monotone))).trans (first_.2.2.1 _ (.inl lo) (.inl (lo.trans_le ((Nat.le_add_right ..).trans spaced))))
  · have tail:=priorEnd.trans (high.trans hi)
    exact (compiled.2.2.1 _ (.inr hi)).trans (first_.2.2.1 _ (.inr (spaced.trans ((Nat.le_add_right ..).trans tail))) (.inr tail))

/-- The three numerical route columns are read on the original state, after
the issuing roster program. They are retained through old-book projection. -/
theorem execute (arg : Fin slots) (node : Fin K) (ptr : Fin H→Fin G→Pointer)
    (route : Fin H→Fin G→Side k) (sizes : ∀h g f,(ptr h g).header f<2^(k+2))
    (side : Fin 6→Bank) (rest : Layout) (extra : Fin 3→Bank) (vals : Fin 3→Fin H→Fin G→Cell (k+2))
    (low : ∀p,(old p).Fits w base) (capacity : ∀p,nr≤(old p).size) (spaced : base+K*2^(((k+2)*K)*M)≤out)
    (prior : ∀p,Reads (old p) (books p) M m)
    (header : ∀f h g,(take node (books (pageOf arg f) h g)).val=(ptr h g).header f)
    (sideFits : ∀i,(side i).Fits w base ∧ nr≤(side i).size)
    (sideReads : ∀i,Reads (side i) (fun h g=>sourceFields ((route h g).withHeader (ptr h g) (sizes h g)) (sideIndex i)) M m)
    (extraFits : ∀i,(extra i).Fits w base ∧ nr≤(extra i).size) (extraReads : ∀i,Reads (extra i) (vals i) M m)
    (within : ∀h g,11*(vals 1 h g).val+(vals 2 h g).val<2^(k+2))
    (room : DescentOrdinaryLocalFragment.finish next_ k M nr<2^w) (word : M*unit k≤w/2) (lanes : 0<M)
    (space : ROM.maskBase (DescentOrdinaryLocalFragment.finish next_ k M nr) k M+3*ROM.rows H G M<2^w) :
    let e:=fun i : Fin 3=>Expr.lookup (extra i) .row
    let L:=(selectedLayout H G M out arg node side rest).field
    let stage:=DescentOrdinaryLocalFragment.program next_ k M nr w L (e 0) (e 1) (e 2)
    let last_:=DescentOrdinaryLocalFragment.finish next_ k M nr
    let resolveStage:=ROM.run last_ k H G M w (DescentOrdinaryLocalFragment.fields next_ k M nr L)
    let program_ := (program old (k+2) K M nr w base out).seq (stage.seq resolveStage)
    let cl:=fun h g=>DescentOrdinaryLocalFragment.route ((route h g).withHeader (ptr h g) (sizes h g)) (vals 0 h g) (DescentPackedRawTicket.payload (vals 1) (vals 2) within h g)
    program_.Spec (·=m) (fun _ done=>∀h g (f : Fin 5),digit (k+4) f.val (digit (outputWidth k) (lane g lanes).val
      (done (ROM.output last_ k H G M+(row H G M (position h g lanes)).val)).val)=(resolve (cl h g)).fields f)
      (ticks old (k+2) K M nr base out+(DescentOrdinaryLocalFragment.cost next_ k M nr L (e 0) (e 1) (e 2)+
        (12+120*ROM.page k M+420*nr))) ∧ CheapCode program_ := by
  intro e L stage last_ resolveStage program_ cl
  have all_:=execute_framed old base out m books arg node ptr route sizes side rest extra vals low capacity spaced prior header sideFits sideReads extraFits extraReads within room word lanes space
  refine ⟨?_,all_.2.2.2⟩
  apply Procedure.spec_of_exec (f:=fun _=>DescentOrdinaryLocalFragment.outputMemory next_ k H G M L (e 0) (e 1) (e 2) (image old (k+2) K M nr base out m))
  · intro before same;subst before;exact all_.1
  · intro _ _;exact all_.2.1

end
end Hierarchy.DescentPriorOperandColumns

end OAI
