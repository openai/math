import OAI.Hierarchy.DescentResetSignedScan
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Shared tables for all reset incidence, parallel, and source-position queries -/
namespace Hierarchy.DescentResetSignedScan.Ranks
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM DescentDyadicSpan
open DescentColonies.SplitRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentPackedSumWords
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {H G M w b paid K X : ℕ}

def width (b M : ℕ) := (b*5+b*5)*M
def headWords (b M : ℕ) :=4*2^(width b M)
def start (base b M : ℕ) :=base+headWords b M
def count (X K : ℕ) := (X*3)*K
def endAddress (base X K b M H G : ℕ) :=start base b M+count X K*span (H*chunks G M)
def order (X K : ℕ) : (Fin X×Fin 3)×Fin K ≃ Fin (count X K) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def parallelQuery (axis : Fin 3) : Bool :=decide (axis.val=1)
def atTable (peer : Bool) (half : Fin 2) : Fin 4 :=
  finProdFinEquiv (m:=2) (n:=2) ((if peer then (1 : Fin 2) else 0), half)
def pages (b paid M : ℕ) (a : Fin 4) : Page :=
  let part : Fin 2×Fin 2 := finProdFinEquiv.symm a
  binary (kernel b paid (decide (part.1.val=1))) M part.2

theorem page_at (peer : Bool) (half : Fin 2) : pages b paid M (atTable peer half)=binary (kernel b paid peer) M half := by
  cases peer <;> simp [atTable,pages]

theorem room (a : Fin 4) : (pages b paid M a).bits ≤ width b M := by
  obtain ⟨⟨peer,half⟩,rfl⟩ := (finProdFinEquiv (m:=2) (n:=2)).surjective a
  simp only [pages, Equiv.symm_apply_apply]
  fin_cases half
  · exact Nat.mul_le_mul_right M (Nat.le_add_right (b*5) (b*5))
  · exact le_rfl

def tables (b paid M base : ℕ) (peer : Bool) :=joined (pages b paid M) (width b M) base (atTable peer)

abbrev Request (X K : ℕ) :=Fin X→Fin 3→Fin K→Expr
abbrev Inputs (X K : ℕ) :=Fin X→Fin 3→Fin K→Fin K→Expr
def body (b paid M base : ℕ) (peer : Bool) (q : Expr) (a : Fin K→Expr) :=total
  (fun i=>(tables b paid M base peer).read q (a i)) (List.finRange K)

def expression (b paid M base : ℕ) (q : Request X K) (a : Inputs X K) (t : ℕ) : Expr :=
  if ok : t<count X K then
    let p:=(order X K).symm ⟨t,ok⟩
    body b paid M base (parallelQuery p.1.2) (q p.1.1 p.1.2 p.2) (a p.1.1 p.1.2 p.2)
  else .lit 0

theorem at_query (q : Request X K) (a : Inputs X K) (base : ℕ) (x : Fin X) (p : Fin 3) (j : Fin K) :
    expression b paid M base q a ((order X K) ((x,p),j)).val=
      body b paid M base (parallelQuery p) (q x p j) (a x p j) := by
  simp [expression,((order X K) ((x,p),j)).isLt]

def output (base X K b M H G : ℕ) (x : Fin X) (p : Fin 3) (j : Fin K) : Bank :=
  ⟨start base b M+((order X K) ((x,p),j)).val*span (H*chunks G M),Nat.clog 2 (H*chunks G M)⟩

def passes (base b paid M H G : ℕ) (q : Request X K) (a : Inputs X K) :=
  DescentPackedFlowBatch.passes (start base b M) (H*chunks G M) (span (H*chunks G M))
    (expression b paid M base q a) 0 (count X K)

def program (base b paid M H G w : ℕ) (q : Request X K) (a : Inputs X K) :=
  (mount (pages b paid M) (width b M) w base).seq (ProtocolRAM.program w (passes base b paid M H G q a))

def memory (base b paid M H G : ℕ) (q : Request X K) (a : Inputs X K) (m : Memory w) :=
  ProtocolRAM.result (passes base b paid M H G q a) (after (pages b paid M) (width b M) base m)

def time (base b paid M H G : ℕ) (q : Request X K) (a : Inputs X K) :=
  (4+10*headWords b M)+ProtocolRAM.clock (passes base b paid M H G q a)

variable (base : ℕ)
local notation "P" => pages b paid M
local notation "head" => start base b M
local notation "N" => H*chunks G M

theorem one (peer : Bool) (q : Expr) (a : Fin K→Expr) (mem : Memory w)
    (query : Fin H→Fin G→Option Parent) (items : Fin K→Fin H→Fin G→Option Parent)
    (qFit : q.Fits w base) (aFit : ∀i,(a i).Fits w base)
    (qRoom : ∀h g,DescentResetSignedScan.Fits b (query h g)) (aRoom : ∀i h g,DescentResetSignedScan.Fits b (items i h g))
    (qSource : Source q (fun h g=>encode b 5 (literal b (query h g))) M mem)
    (aSource : ∀i,Source (a i) (fun h g=>encode b 5 (literal b (items i h g))) M mem)
    (bounded : ∀h g,(∑i,contribution peer (query h g) (items i h g))<2^paid)
    (space : head<2^w) :
    (body b paid M base peer q a).Fits w head ∧ Source (body b paid M base peer q a) (sumWord peer query items bounded) M
      (after P (width b M) base mem) := by
  let tab:=tables b paid M base peer
  let mounted:=after P (width b M) base mem
  have separated : base≤head:=Nat.le_add_right ..
  have held:=binary_mounted (kernel b paid peer) M P (width b M) base mem room (atTable peer) (page_at peer)
  have keep {d : ℕ} (e : Expr) (fit : e.Fits w base) (v : Fin H→Fin G→Cell d) (read : Source e v M mem) :
      Source e v M mounted := fun j=>(ProtocolRAM.eval_below e _ mem mounted fit
        (fun z hz=>frame P _ base mem z (.inl hz))).trans (read j)
  have fit (i : Fin K) : DescentPackedZip.Fits tab q (a i) (b*5) (b*5) M head w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ separated qFit,ProtocolRAMGeneratedWrite.fits_mono _ separated (aFit i),
      bank_room P _ base _ _ (room _) le_rfl space,bank_room P _ base _ _ (room _) le_rfl space,
      congrArg Page.bits (page_at (b:=b) (paid:=paid) (M:=M) peer 0),
      congrArg Page.bits (page_at (b:=b) (paid:=paid) (M:=M) peer 1)⟩
  have each (i : Fin K) : (tab.read q (a i)).Fits w head := by
    have law:=fit i
    simp [Tables.read,Expr.Fits,law.left,law.right,law.shift,law.apply]
  refine ⟨fits_total _ each _,?_⟩
  intro r
  have value (i : Fin K):=read_data tab q (a i) head (fit i) (kernel b paid peer) (blank ..) mounted held _ _
    (keep _ qFit _ qSource) (keep _ (aFit i) _ (aSource i)) r
  simp only [kernel,unpack_literal _ _ (qRoom _ _),unpack_literal _ _ (aRoom _ _ _)] at value
  have sum:=eval_sum _ _ mounted _ value (List.finRange K)
  rw [←List.ofFn_eq_map,List.sum_ofFn,packed_sum peer query items bounded] at sum
  exact sum

abbrev QueryRows (X K H G : ℕ) :=Fin X→Fin 3→Fin K→Fin H→Fin G→Option Parent
abbrev ItemRows (X K H G : ℕ) :=Fin X→Fin 3→Fin K→Fin K→Fin H→Fin G→Option Parent

theorem run (q : Request X K) (a : Inputs X K) (mem : Memory w)
    (query : QueryRows X K H G) (items : ItemRows X K H G)
    (qFit : ∀x p j,(q x p j).Fits w base) (aFit : ∀x p j i,(a x p j i).Fits w base)
    (qRoom : ∀x p j h g,DescentResetSignedScan.Fits b (query x p j h g))
    (aRoom : ∀x p j i h g,DescentResetSignedScan.Fits b (items x p j i h g))
    (qSource : ∀x p j,Source (q x p j) (fun h g=>encode b 5 (literal b (query x p j h g))) M mem)
    (aSource : ∀x p j i,Source (a x p j i) (fun h g=>encode b 5 (literal b (items x p j i h g))) M mem)
    (bounded : ∀x p j h g,(∑i,contribution (parallelQuery p) (query x p j h g) (items x p j i h g))<2^paid)
    (space : endAddress base X K b M H G<2^w) :
    let done:=memory base b paid M H G q a mem
    (program base b paid M H G w q a).Exec mem done (time base b paid M H G q a) ∧
    (∀x p j,Reads (output base X K b M H G x p j) (sumWord (parallelQuery p) (query x p j) (items x p j) (bounded x p j)) M done) ∧
    (∀u,u<base ∨ endAddress base X K b M H G≤u→done u=mem u) ∧ CheapCode (program base b paid M H G w q a) := by
  intro done
  let exp_:=expression b paid M base q a
  let mounted:=after P (width b M) base mem
  have upper : head≤endAddress base X K b M H G:=Nat.le_add_right ..
  have before:=DescentOrdinaryAtomFieldRAM.ROM.run P (width b M) base mem (upper.trans_lt space)
  have held (x p j):=(one base (parallelQuery p) (q x p j) (a x p j) mem (query x p j) (items x p j)
    (qFit x p j) (aFit x p j) (qRoom x p j) (aRoom x p j) (qSource x p j) (aSource x p j) (bounded x p j) (upper.trans_lt space))
  have valid (t : ℕ) (lt : t<count X K) : (exp_ t).Fits w head := by
    obtain ⟨⟨⟨x,p⟩,j⟩,eqn⟩ := (order X K).surjective ⟨t,lt⟩
    have num : ((order X K) ((x,p),j)).val=t:=congrArg Fin.val eqn
    rw [←num]
    change (expression b paid M base q a ((order X K) ((x,p),j)).val).Fits w head
    rw [at_query]
    exact (held x p j).1
  have whole:=DescentPackedFlowBatch.execute head N (span N) (count X K) exp_ mounted valid space (span_ge N)
  refine ⟨Procedure.Exec.then before.1 whole.1,?_,?_,?_⟩
  · intro x p j r
    change done (head+((order X K) ((x,p),j)).val*span N+(row H G M r).val)=_
    have atRow := congrArg (fun e : Expr => e.eval mounted ((row H G M r).val : Word w))
      (at_query (b:=b) (paid:=paid) (M:=M) q a base x p j)
    exact (whole.2.1 ((order X K) ((x,p),j)) (row H G M r)).trans
      (atRow.trans ((held x p j).2 r))
  · intro u side
    rcases side with low|high
    · exact (whole.2.2 u (low.trans_le (Nat.le_add_right ..))).trans (frame P _ base mem u (.inl low))
    · have after_:=DescentPackedFlowBatch.above head N (span N) exp_ mounted 0 (count X K) u (span_ge N)
        (by simpa only [endAddress, Nat.zero_add] using high)
      exact after_.trans (frame P _ base mem u (.inr (upper.trans high)))
  · apply ProtocolRAM.cheap_seq
    · apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply ProtocolRAM.program_cheap

theorem output_fits (x : Fin X) (p : Fin 3) (j : Fin K) (space : endAddress base X K b M H G<2^w) :
    (output base X K b M H G x p j).Fits w (endAddress base X K b M H G) := by
  let addr:=(order X K) ((x,p),j)
  have step:=Nat.mul_le_mul_right (span N) addr.isLt
  have pos:=span_pos N
  have extent:=Nat.mul_le_mul_right (span N) (show 1≤count X K from Nat.zero_lt_of_lt addr.isLt)
  rw [Nat.one_mul] at extent
  change 0<span N ∧ span N<2^w ∧ head+addr.val*span N+span N≤head+count X K*span N
  rw [Nat.succ_mul] at step
  exact ⟨pos,(extent.trans (Nat.le_add_left ..)).trans_lt space,by omega⟩

theorem any (q : Request X K) (a : Inputs X K) (mem : Memory w)
    (qFit : ∀x p j,(q x p j).Fits w base) (aFit : ∀x p j i,(a x p j i).Fits w base)
    (space : endAddress base X K b M H G<2^w) :
    let done:=memory base b paid M H G q a mem
    (program base b paid M H G w q a).Exec mem done (time base b paid M H G q a) ∧
    (∀u,u<base ∨ endAddress base X K b M H G≤u→done u=mem u) ∧ CheapCode (program base b paid M H G w q a) := by
  intro done
  let mounted:=after P (width b M) base mem
  let e:=expression b paid M base q a
  have top : head≤endAddress base X K b M H G:=Nat.le_add_right ..
  have lo : base≤head:=Nat.le_add_right ..
  have started:=DescentOrdinaryAtomFieldRAM.ROM.run P (width b M) base mem (top.trans_lt space)
  have valid (i : ℕ) (hi : i<count X K) : (e i).Fits w head := by
    obtain ⟨⟨⟨x,p⟩,j⟩,at_⟩:=(order X K).surjective ⟨i,hi⟩
    have eqn : ((order X K) ((x,p),j)).val = i := congrArg Fin.val at_
    rw [←eqn]
    change (expression b paid M base q a ((order X K) ((x,p),j)).val).Fits w head
    rw [at_query]
    apply fits_total
    intro l
    have left:=bank_room P _ base head (atTable (parallelQuery p) 0) (room _) le_rfl (top.trans_lt space)
    have right:=bank_room P _ base head (atTable (parallelQuery p) 1) (room _) le_rfl (top.trans_lt space)
    exact ⟨right,ProtocolRAMGeneratedWrite.fits_mono _ lo (aFit x p j l),
      left,ProtocolRAMGeneratedWrite.fits_mono _ lo (qFit x p j)⟩
  have all:=DescentPackedFlowBatch.execute head N (span N) (count X K) e mounted valid space (span_ge N)
  refine ⟨Procedure.Exec.then started.1 all.1,?_,?_⟩
  · intro u away
    rcases away with low|high
    · exact (all.2.2 u (low.trans_le lo)).trans (frame P _ base mem u (.inl low))
    · have back:=DescentPackedFlowBatch.above head N (span N) e mounted 0 (count X K) u (span_ge N)
        (by simpa only [endAddress, Nat.zero_add] using high)
      exact back.trans (frame P _ base mem u (.inr (top.trans high)))
  · apply ProtocolRAM.cheap_seq
    · apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply ProtocolRAM.program_cheap

theorem clock_bound (q : Request X K) (a : Inputs X K) (lim : ℕ)
    (qLim : ∀x p j,(q x p j).work ≤ lim) (aLim : ∀x p j i,(a x p j i).work ≤ lim) :
    time base b paid M H G q a≤(4+10*headWords b M)+(4+count X K*(4+N*(2*(1+K*(2*lim+12))+4))) := by
  apply Nat.add_le_add_left
  apply DescentPackedFlowBatch.tariff
  intro t ht
  obtain ⟨⟨⟨x,p⟩,j⟩,eqn⟩:=(order X K).surjective ⟨t,ht⟩
  rw [←show ((order X K) ((x,p),j)).val=t from congrArg Fin.val eqn,at_query]
  let tab:=tables b paid M base (parallelQuery p)
  have each (l:Fin K) : (tab.read (q x p j) (a x p j l)).work≤2*lim+11 :=by
    rw [DescentPackedZip.work];have hq:=qLim x p j;have ha:=aLim x p j l;omega
  simpa [body, tab, List.length_finRange, Nat.add_assoc] using
    work_total _ (2*lim+11) each (List.finRange K)

end
end Hierarchy.DescentResetSignedScan.Ranks

end OAI
