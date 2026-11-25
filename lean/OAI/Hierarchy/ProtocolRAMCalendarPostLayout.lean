import OAI.Hierarchy.ProtocolRAMPurchaseStage

namespace OAI
/-! # Physical word and column addresses after a frozen calendar purchase -/

namespace Hierarchy.ProtocolRAM.Calendar.PostLayout

open PurchaseStage
open scoped Classical

variable {q d : ℕ}

def startColumns (first bits n : ℕ) := first+2^bits+n+2

def column (first bits n i : ℕ) := startColumns first bits n+i*n

def columnsCount (B : Repair q d) := 17+3*d+B.batch.quotes.length

/-- A score check writes its running sums followed by its Boolean result. -/
def placeTests (tests : AttemptGate.TestBoard) (first : ℕ) : AttemptGate.TestBoard :=
  let excess := first+1
  let payload := excess+tests.excess.rows+1
  let discrepancy := payload+tests.payload.rows+1
  {tests with
    stop := ⟨first,0⟩
    excess := {tests.excess with out:=excess}
    payload := {tests.payload with out:=payload}
    discrepancy := {tests.discrepancy with out:=discrepancy}}

def afterTests (tests : AttemptGate.TestBoard) (first : ℕ) :=
  first+1+(tests.excess.rows+1)+(tests.payload.rows+1)+(tests.discrepancy.rows+1)

theorem tests_separate (tests : AttemptGate.TestBoard) (first : ℕ) :
    let t := placeTests tests first
    t.stop.base < t.excess.out ∧ t.excess.out+t.excess.rows < t.payload.out ∧
      t.payload.out+t.payload.rows < t.discrepancy.out ∧
      t.discrepancy.out+t.discrepancy.rows+1 = afterTests tests first := by
  dsimp [placeTests,afterTests]
  omega

/-- The test board and the expressions are supplied by the current event.
The repair mask and the inspection and output columns occupy a fresh shelf. -/
def place (L : Dispatch) (B : Repair q d) (first bits : ℕ) : Repair q d :=
  let n := L.candidates
  let out := column first bits n
  {B with
    repairBits := ⟨first,bits⟩
    keys := first+2^bits
    tally := first+2^bits+n
    quoteOut := out 0
    purchaseOut := out 1
    modeOut := out 2
    reportOut := fun j => out (3+j.val)
    boughtFields := fun j => out (10+j.val)
    stockOut := fun i => out (17+3*i.val)
    reserveOut := fun i => out (17+3*i.val+2)
    priceOut := fun i => out (17+3*d+i.val)
    verdict := out (columnsCount B)}

theorem beforeColumns (L : Dispatch) (B : Repair q d) (first bits : ℕ)
    (room : L.candidates ≤ 2^bits) :
    let P := place L B first bits
    P.repairBits.base+L.candidates ≤ P.keys ∧
      P.keys+L.candidates=P.tally ∧ P.tally+2=startColumns first bits L.candidates := by
  dsimp [place,startColumns]
  omega

/-- The actual output address and the number of rows written by a pass. -/
def span (p : Pass) := (p.out,p.rows)

private def band {α : Type*} (f : ℕ → α) (start len : ℕ) := (List.range' start len).map f

private theorem band_append {α : Type*} (f : ℕ → α) (start a b : ℕ) :
    band f start a ++ band f (start+a) b = band f start (a+b) := by
  simp only [band,←List.map_append,List.range'_append_1]

private theorem ofFn_band {α : Type*} (f : ℕ → α) (start n : ℕ) :
    List.ofFn (fun i : Fin n => f (start+i.val))=band f start n := by
  apply List.ext_getElem
  · simp [band]
  · intro i _ _
    simp [band,List.getElem_range']

private theorem flat_bands {α : Type*} (f : ℕ → α) (start n width : ℕ) :
    (List.ofFn (fun i : Fin n => band f (start+width*i.val) width)).flatten =
      band f start (width*n) := by
  induction n with
  | zero => simp [band]
  | succ n ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
    change (List.ofFn (fun i : Fin n => band f (start+width*i.val) width)).flatten ++
      band f (start+width*n) width = _
    rw [ih,band_append,Nat.mul_succ]

/-- Reading the addresses from the unmodified executable pass list yields the
complete increasing enumeration of output columns. -/
theorem writes_layout (L : Dispatch) (B : Repair q d) (first bits : ℕ) :
    (writes L (place L B first bits)).map span =
      (List.range (columnsCount B)).map (fun i => (column first bits L.candidates i,L.candidates)) := by
  let fn := fun i => (column first bits L.candidates i,L.candidates)
  let P := place L B first bits
  have stock (i : Fin d) : (stockWrites L P i).map span=band fn (17+3*i.val) 3 := by
    simp [P,stockWrites,place,span,fn,band,List.range'_succ,column,Nat.add_mul]
   ; ring_nf
    all_goals exact ⟨True.intro,True.intro⟩
  have stocks : ((List.ofFn (stockWrites L P)).flatten.map span)=band fn 17 (3*d) := by
    rw [List.map_flatten,List.map_ofFn]
    change (List.ofFn (fun i : Fin d => (stockWrites L P i).map span)).flatten=_
    simp_rw [stock]
    exact flat_bands fn 17 d 3
  have prices : (priceColumns L P).map span=band fn (17+3*d) B.batch.quotes.length := by
    unfold priceColumns
    rw [List.map_ofFn]
    exact ofFn_band fn (17+3*d) _
  have firstThree : [fn 0,fn 1,fn 2]=band fn 0 3 := by rfl
  change (writes L P).map span=_
  rw [writes]
  simp only [List.map_cons,List.map_append,List.map_ofFn,stocks,prices]
  change fn 0 :: fn 1 :: fn 2 :: ((List.ofFn (fun i : Fin 7 => fn (3+i.val)) ++
    List.ofFn (fun i : Fin 7 => fn (10+i.val))) ++
      (band fn 17 (3*d) ++ band fn (17+3*d) B.batch.quotes.length)) = _
  rw [ofFn_band fn 3 7,ofFn_band fn 10 7,band_append fn 3 7 7,band_append fn 17 (3*d) B.batch.quotes.length]
  change [fn 0,fn 1,fn 2] ++ (band fn 3 14 ++ band fn 17 (3*d+B.batch.quotes.length)) = _
  rw [firstThree,band_append,band_append]
  simp only [band,List.range_eq_range',columnsCount,Nat.add_assoc]
  exact congrArg (fun len => (List.range' 0 len).map fn) (by omega)

theorem listed (L : Dispatch) (B : Repair q d) (first bits : ℕ) (p : Pass)
    (hp : p∈writes L (place L B first bits)) :
    ∃ i < columnsCount B, p.out=column first bits L.candidates i ∧ p.rows=L.candidates := by
  have h := List.mem_map_of_mem (f:=span) hp
  rw [writes_layout] at h
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
  exact ⟨i,List.mem_range.mp hi,(congrArg Prod.fst eq).symm,(congrArg Prod.snd eq).symm⟩

theorem board (L : Dispatch) (B : Repair q d) (first bits w : ℕ)
    (inputs : ∀p∈writes L (place L B first bits),p.term.inputEnd ≤ (place L B first bits).keys)
    (keysFit : (place L B first bits).keys < 2^w) :
    Board L (place L B first bits) w := by
  let P := place L B first bits
  refine ⟨⟨P.keys,le_rfl,?_⟩,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,addr,_⟩ := listed L B first bits p hp
    refine ⟨p.term.fits_of_inputEnd (inputs p hp) keysFit,?_⟩
    rw [addr]
    dsimp [P,place,column,startColumns]
    omega
  · let relation := fun (a b : ℕ×ℕ) => a.1+a.2 ≤ b.1
    change (writes L P).Pairwise (fun p r => relation (span p) (span r))
    apply (List.pairwise_map (f:=span) (R:=relation)).mp
    rw [writes_layout,List.pairwise_map]
    refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro i j h
    have le := Nat.mul_le_mul_right L.candidates (Nat.succ_le_of_lt h)
    simp only [Nat.succ_mul] at le
    change startColumns first bits L.candidates+i*L.candidates+L.candidates ≤
      startColumns first bits L.candidates+j*L.candidates
    omega
  · intro p hp
    obtain ⟨i,hi,addr,rows⟩ := listed L B first bits p hp
    rw [addr,rows]
    have le := Nat.mul_le_mul_right L.candidates (Nat.succ_le_of_lt hi)
    simp only [Nat.succ_mul] at le
    change startColumns first bits L.candidates+i*L.candidates+L.candidates ≤
      startColumns first bits L.candidates+columnsCount B*L.candidates
    omega

end Hierarchy.ProtocolRAM.Calendar.PostLayout

end OAI
