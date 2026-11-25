import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedSumWords

namespace OAI
/-! # Looking up the reached candidate selected by each packed rotor or retained operand -/
namespace Hierarchy.DescentOperandCandidateLookup
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentPackedSumWords
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {n a b H G M w base out : ℕ}

def code (room : n<2^a) : Option (Fin n) → Cell a
  | none=>0
  | some j=>⟨j.val+1,by have inside:=j.isLt;omega⟩

def test (j : Fin n) (q : Cell a) (v : Cell b) : Cell b :=
  if q.val=j.val+1 then v else 0

theorem test_zero (j : Fin n) : test (a:=a) (b:=b) j 0 0=0 := by simp [test]

theorem test_code (room : n<2^a) (query : Option (Fin n)) (j : Fin n) (value : Cell b) :
    test j (code room query) value=(if query=some j then value else 0) := by
  cases query with
  | none => simp [test,code]
  | some i =>
    by_cases hit : i=j
    · subst j;simp [test,code]
    · have dif : i.val≠j.val:=fun e=>hit (Fin.ext e)
      simp [test,code,hit,dif]

def selected (q : Fin H→Fin G→Option (Fin n)) (items : Fin n→Fin H→Fin G→Cell b)
    (h : Fin H) (g : Fin G) : Cell b := (q h g).elim 0 (fun i=>items i h g)

theorem packed_select (q : Fin H→Fin G→Option (Fin n)) (items : Fin n→Fin H→Fin G→Cell b)
    (p : Row H G M) :
    (∑i,(data (fun h g=>if q h g=some i then items i h g else 0) p).val) =
      (data (selected q items) p).val := by
  simp_rw [lanes_val]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases live : p.2.val*M+j.val<G
  · simp only [dite_eq_left live]
    cases found:q p.1 ⟨p.2.val*M+j.val,live⟩ with
    | none => simp [selected,found]
    | some u =>
      simp [selected,found,apply_ite,ite_mul]
  · simp [live]

/-- The first page of each pair shifts one packed query and the second
selects the reached field if its one-based candidate number matches. -/
def pages (n a b M : ℕ) (j : Fin (n*2)) : Page :=
  let t:=finProdFinEquiv.symm j
  binary (test (a:=a) (b:=b) t.1) M t.2

def index (i : Fin n) (s : Fin 2) : Fin (n*2) :=finProdFinEquiv (i,s)
def bits (a b M : ℕ) := (a+b)*M

theorem layout (i : Fin n) (s : Fin 2) :
    pages n a b M (index i s)=binary (test (a:=a) (b:=b) i) M s := by simp [pages,index]

theorem page_room (j : Fin (n*2)) : (pages n a b M j).bits≤bits a b M := by
  obtain ⟨⟨i,s⟩,rfl⟩:=finProdFinEquiv.surjective j
  rw [show pages n a b M (finProdFinEquiv (i,s))=binary (test (a:=a) (b:=b) i) M s from layout i s]
  fin_cases s
  · exact Nat.mul_le_mul_right M (Nat.le_add_right ..)
  · exact le_rfl

def table (base a b M : ℕ) (i : Fin n) := joined (pages n a b M) (bits a b M) base (index i)

def expr (q : Expr) (old : Fin n→Expr) (base a b M : ℕ) :=
  total (fun i=>(table base a b M i).read q (old i)) (List.finRange n)

def dictionaryEnd (n a b M base : ℕ) := base+(n*2)*2^(bits a b M)

def program (q : Expr) (old : Fin n→Expr) (base out a b H G M w : ℕ) :=
  (mount (pages n a b M) (bits a b M) w base).seq (scan w out (H*chunks G M) (expr q old base a b M))

def imageAt (q : Expr) (old : Fin n→Expr) (base out a b H G M : ℕ) (mem : Memory w) :=
  image out (H*chunks G M) (expr q old base a b M) (after (pages n a b M) (bits a b M) base mem)

def ticks (q : Expr) (old : Fin n→Expr) (base a b H G M : ℕ) :=
  4+10*((n*2)*2^(bits a b M))+(4+H*chunks G M*(2*(expr q old base a b M).work+4))

theorem prepared (query : Expr) (prior : Fin n→Expr) (source : Memory w)
    (tickets : Fin H→Fin G→Option (Fin n)) (items : Fin n→Fin H→Fin G→Cell b)
    (early : query.Fits w base) (held : ∀i,(prior i).Fits w base) (small : n<2^a)
    (requested : Source query (fun h g=>code small (tickets h g)) M source)
    (columns : ∀i,Source (prior i) (items i) M source)
    (apart : dictionaryEnd n a b M base ≤ out) (upper : out<2^w) :
    let op:=expr query prior base a b M
    let mem:=after (pages n a b M) (bits a b M) base source
    op.Fits w out ∧ ∀r : Row H G M,op.eval mem ((row H G M r).val:Word w)=((data (selected tickets items) r).val:Word w) := by
  intro op mem
  let book:=pages n a b M
  let span:=bits a b M
  let dict:=after book span base source
  have sep : base+(n*2)*2^span≤out:=apart
  have low : base≤out:=(Nat.le_add_right ..).trans sep
  have stable:=DescentOrdinaryAtomFieldRAM.ROM.frame book span base source
  have get {c : ℕ} (e : Expr) (bound : e.Fits w base) (v : Fin H→Fin G→Cell c) (valid : Source e v M source) :
      Source e v M dict:=fun r=>(eval_below e _ source dict bound (fun z pre=>stable z (.inl pre))).trans (valid r)
  have fits (i : Fin n) : DescentPackedZip.Fits (table base a b M i) query (prior i) a b M out w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ low early,ProtocolRAMGeneratedWrite.fits_mono _ low (held i),
      bank_room book span base out _ (page_room (index i 0)) sep upper,
      bank_room book span base out _ (page_room (index i 1)) sep upper,
      congrArg Page.bits (layout (a:=a) (b:=b) (M:=M) i 0),
      congrArg Page.bits (layout (a:=a) (b:=b) (M:=M) i 1)⟩
  have safe (i : Fin n) : ((table base a b M i).read query (prior i)).Fits w out := by
    have fit:=fits i
    simp [DescentPackedZip.Tables.read,Expr.Fits,fit.left,fit.right,fit.apply,fit.shift]
  refine ⟨fits_total _ safe _,?_⟩
  intro r
  have each (i : Fin n) := DescentPackedZip.read_data (table base a b M i) query (prior i) out (fits i) (test i)
    (test_zero i) dict (binary_mounted (test i) M book span base source page_room (index i) (layout i))
    _ _ (get _ early _ requested) (get _ (held i) _ (columns i)) r
  simp only [test_code] at each
  have sum:=eval_sum _ _ dict _ each (List.finRange n)
  rw [←List.ofFn_eq_map,List.sum_ofFn,packed_select tickets items r] at sum
  exact sum

/-- All candidates may carry different words in every active group. This
native query uses the reached values as input and prints its finite comparator
once for the full rectangle. The code and its price are independent of those
values and of which actuator accepts a candidate. -/
theorem run (query : Expr) (prior : Fin n→Expr) (source : Memory w)
    (tickets : Fin H→Fin G→Option (Fin n)) (items : Fin n→Fin H→Fin G→Cell b)
    (early : query.Fits w base) (held : ∀i,(prior i).Fits w base) (small : n<2^a)
    (requested : Source query (fun h g=>code small (tickets h g)) M source)
    (columns : ∀i,Source (prior i) (items i) M source)
    (apart : dictionaryEnd n a b M base ≤ out) (room : out+H*chunks G M<2^w) :
    let done:=imageAt query prior base out a b H G M source
    (program query prior base out a b H G M w).Exec source done (ticks query prior base a b H G M) ∧
      (∀r : Row H G M,done (out+(row H G M r).val)=((data (selected tickets items) r).val:Word w)) ∧
      (∀z,z<base ∨ out+H*chunks G M≤z → done z=source z) ∧
      CheapCode (program query prior base out a b H G M w) := by
  intro done
  let book:=pages n a b M
  let span:=bits a b M
  let dict:=after book span base source
  have upper : out<2^w:=(Nat.le_add_right ..).trans_lt room
  have sep : base+(n*2)*2^span≤out:=apart
  have started:=DescentOrdinaryAtomFieldRAM.ROM.run book span base source (sep.trans_lt upper)
  have hold:=DescentOrdinaryAtomFieldRAM.ROM.frame book span base source
  have ready:=prepared query prior source tickets items early held small requested columns apart upper
  let op:=expr query prior base a b M
  have scan_ : (scan w out (H*chunks G M) op).Exec dict (ProtocolRAM.image out (H*chunks G M) op dict)
      (4+(H*chunks G M)*(2*op.work+4)) := scan_exec out (H*chunks G M) op dict ready.1 room
  refine ⟨Procedure.Exec.then started.1 scan_,?_,?_,cheap_seq (cheap book span w base) (scan_cheap w _ _ _)⟩
  · intro r
    exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M r)).trans (ready.2 r)
  · intro z outside
    exact (ProtocolRAMGeneratedWrite.frame_image out _ _ dict z (by rcases outside with h|h <;> omega)).trans
      (hold z (by rcases outside with h|h <;> omega))

end
end Hierarchy.DescentOperandCandidateLookup

end OAI
