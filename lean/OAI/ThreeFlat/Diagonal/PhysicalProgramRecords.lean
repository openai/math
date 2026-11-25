import OAI.ThreeFlat.Diagonal.FixedTileCapacity
import OAI.ThreeFlat.Diagonal.PhysicalBlockRecordBounds
import OAI.ThreeFlat.Diagonal.PhysicalProgramLength
import OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.PhysicalRefreshFamily
import OAI.ThreeFlat.Diagonal.PhysicalRepeatWidth
import OAI.ThreeFlat.Diagonal.ProgramDirectory

namespace OAI
/-! # Actual native row and symbol ordering in the complete shared history register -/

namespace ThreeFlat.Diagonal.PhysicalStage.Program
open CompressorPacking HistoryContraction
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

def recordBounds : {s : ℕ} → Program F s → List (ℕ×ℕ)
  | _, .done _ => []
  | _, .shrink s _ T _ tail => (shrinkSymbolBound T,shrinkCopyFactor (2*2^s+1) (2^s)) :: tail.recordBounds
  | _, .refresh s _ _ _ _ _ _ T _ _ _ _ _ _ _ tail =>
    (refreshSymbolBound T,1+2*(2^s)*(2^s)) :: tail.recordBounds

structure RecordTable {d l : ℕ} {A : State d l} (r : Run F A) (K W : ℕ) (sizes : List ℕ) where
  families : r.Families
  fit : r.FamiliesFit K W families
  shape : ∀ h,r.rowCounts families h=sizes

def RecordTable.codes {d l K W : ℕ} {A : State d l} {r : Run F A} {sizes : List ℕ}
    (Q : RecordTable r K W sizes) := r.codes (r.familyRecords K W Q.families Q.fit)

theorem RecordTable.write_size {d l K W : ℕ} {A : State d l} {r : Run F A} {sizes : List ℕ}
    (Q : RecordTable r K W sizes) (h : r.plan.History) :
    (r.plan.write Q.codes h).length=sizes.sum*K*W := by
  rw [RecordTable.codes,r.write_length,Q.shape h]

/-- Reindex only the published vector of row counts. This keeps the executable moved
family and its term ordering definitionally available when reading the next native word. -/
def RecordTable.changeSizes {d l K W : ℕ} {A : State d l} {r : Run F A}
    {x y : List ℕ} (q : RecordTable r K W x) (e : x=y) : RecordTable r K W y :=
  ⟨q.families,q.fit,fun h=>(q.shape h).trans e⟩

def RecordTable.records {d l K W : ℕ} {A : State d l} {r : Run F A}
    {sizes : List ℕ} (q : RecordTable r K W sizes) : r.Records := r.familyRecords K W q.families q.fit

def changeTable {d l l' K W : ℕ} (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l'))
    {sizes : List ℕ} (t : RecordTable r K W sizes) : RecordTable (recast e A r) K W sizes := by
  cases e; exact t

theorem beforeRecast {d l l' : ℕ} (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l'))
    {Z : ℕ} (bound : (recast e A r).WidthCeiling Z) : r.WidthCeiling Z := by cases e; exact bound

def degreeFamily {d l D D' L K W : ℕ} {A : State d l} (e : D=D') (R : Move F A D L)
    (count futureBase : ℕ)
    (f : RecordFamily R.rules.count) (fit : f.Fits K W) (size : f.motifs=count)
    (nextBase : ∀ t,Fintype.card (R.next t).Base=futureBase) :
    (Q : RecordFamily (recastMove e R).rules.count) ×'
      (Q.Fits K W ∧ Q.motifs=count ∧ ∀ t,Fintype.card ((recastMove e R).next t).Base=futureBase) := by
  cases e
  exact ⟨f,fit,size,nextBase⟩

def degreeTerm {d l D D' L : ℕ} {A : State d l} (e : D=D') (R : Move F A D L) :
    Fin R.rules.count ≃ Fin (recastMove e R).rules.count := by cases e;exact Equiv.refl _

theorem degree_next {d l D D' L : ℕ} {A : State d l} (e : D=D') (R : Move F A D L)
    (j : Fin R.rules.count) : (e ▸ R.next j : State D' L)=(recastMove e R).next (degreeTerm e R j) := by
  cases e;rfl

theorem degree_read {d l D D' L K W : ℕ} {A : State d l} (e : D=D') (R : Move F A D L)
    (count futureBase : ℕ) (f : RecordFamily R.rules.count) (fit : f.Fits K W) (size : f.motifs=count)
    (nextBase : ∀ t,Fintype.card (R.next t).Base=futureBase) (raw : List Bool) :
    let q:=degreeFamily e R count futureBase f fit size nextBase
    (q.1.record q.2.1).read (raw.take (q.1.record q.2.1).width)=
      ((f.record fit).read (raw.take (f.record fit).width)).map (degreeTerm e R) := by
  cases e
  let value := (f.record fit).read (raw.take (f.record fit).width)
  change value = Option.map id value
  cases value <;> rfl

def consTable {d l D L K W : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ i,Run F (R.next i)) (q : RecordFamily R.rules.count) (fit : q.Fits K W)
    {count : ℕ} {sizes : List ℕ} (head : q.motifs=count) (tail : ∀ i,RecordTable (next i) K W sizes) :
    RecordTable (.step R next) K W (count::sizes) :=
  ⟨(q,fun i=>(tail i).families),⟨fit,fun i=>(tail i).fit⟩,fun h=>by
    change q.motifs :: (next h.1).rowCounts (tail h.1).families (Run.tailHistory R next h) = _
    rw [head,(tail h.1).shape]⟩

theorem prefix_changeTable {d l l' K W n : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) {sizes : List ℕ} (q : RecordTable r K W sizes) (raw : List Bool) :
    Run.PrefixOK n (recast e A r) (changeTable e A r q).records raw ↔
      Run.PrefixOK n r q.records raw := by cases e;rfl

theorem endsAt_changeTable {d l l' K W : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) {sizes : List ℕ} (q : RecordTable r K W sizes)
    (raw : List Bool) (v : Run.WireLayer) (tail : List Bool) :
    (recast e A r).EndsAt (changeTable e A r q).records raw v tail ↔ r.EndsAt q.records raw v tail := by
  cases e;rfl

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8192 in
/-- Each stage recomputes its genuine motif family from the old graph and its selected
history. Only the number of rows in each record is fixed by the public stage directory. -/
def table {s : ℕ} (P : Program F s) (K W Z : ℕ)
    (bounds : ∀ a∈P.recordBounds,a.1≤K ∧ a.2*Z<2^W)
    (rem : ℕ) (A : State (2^s) (P.charge+rem)) (hZ : (P.run rem A).WidthCeiling Z) :
    RecordTable (P.run rem A) K W ((P.directory rem (Fintype.card A.Base)).map NavigationDirectory.Stage.motifs) := by
  induction P with
  | done => exact ⟨PUnit.unit,trivial,fun _=>rfl⟩
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    let next := fun i=>tail.run rem (R.next i)
    have budget : (Run.step R next).WidthCeiling Z := beforeRecast e A _ hZ
    have hs := bounds _ List.mem_cons_self
    have baseEq : Fintype.card B.Base = Fintype.card A.Base := baseCast e A
    let Q := shrinkBinaryFamily T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    have fit : Q.Fits K W := shrinkBinaryFamily_fits T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B hs.1
      ((Nat.mul_le_mul_left _ (by simpa [Nat.add_comm] using budget.1)).trans_lt hs.2)
    apply changeTable e A
    apply consTable R next Q fit
    · dsimp only [Q]
      rw [shrinkBinaryFamily_motifs,baseEq]
      rfl
    · intro i
      have q := ih (fun a ha=>bounds a (List.mem_cons_of_mem _ ha)) (R.next i) (budget.2 i)
      exact q.changeSizes (by dsimp only [R]; rw [shrinkBinary_next_base,baseEq])
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    let next := fun i=>tail.run rem ((recastMove degree R).next i)
    have budget : (Run.step (recastMove degree R) next).WidthCeiling Z := beforeRecast e A _ hZ
    have hs := bounds _ List.mem_cons_self
    have baseEq : Fintype.card B.Base = Fintype.card A.Base := baseCast e A
    let Q := refreshBinaryFamily T B hm hh sym rows zero conn
    have fit : Q.Fits K W := refreshBinaryFamily_fits T B hm hh sym rows zero conn hs.1
      ((Nat.mul_le_mul_left _ (by simpa [Nat.add_comm] using budget.1)).trans_lt hs.2)
    let f := degreeFamily degree R ((Fintype.card B.Base)*2^(tail.charge+rem)) (Fintype.card B.Base*2^s)
      Q fit rfl (refreshBinary_next_base T B hm hh sym rows zero conn)
    apply changeTable e A
    apply consTable (recastMove degree R) next f.1 f.2.1
    · rw [f.2.2.1,baseEq]; rfl
    · intro i
      have q := ih (fun a ha=>bounds a (List.mem_cons_of_mem _ ha)) _ (budget.2 i)
      exact q.changeSizes (by rw [f.2.2.2 i,baseEq])

theorem recordBounds_cast {s t : ℕ} (e : s=t) (P : Program F s) :
    (e ▸ P : Program F t).recordBounds=P.recordBounds := by cases e; rfl

end
end ThreeFlat.Diagonal.PhysicalStage.Program

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F)

theorem bounds_shrinkPrefix (n i : ℕ) (P : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i P).recordBounds=B.shrinkRecordBounds n i++P.recordBounds := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [shrinkPrefix,shrinkRecordBounds,Program.recordBounds,ih,
      Program.recordBounds_cast,List.cons_append]

theorem bounds_prefix (P : Program F (B.exponent 0)) :
    (B.prefix P).recordBounds=B.fixedRecordBounds++P.recordBounds := by
  simp only [Block.prefix,bounds_shrinkPrefix,Program.recordBounds_cast,Program.recordBounds,
    fixedRecordBounds,List.cons_append,List.nil_append,List.append_assoc]

theorem bounds_repeat (n : ℕ) {p : ℕ×ℕ} (hp : p∈(B.repeat n).recordBounds) : p∈B.fixedRecordBounds := by
  induction n with
  | zero => exact (List.not_mem_nil hp).elim
  | succ n ih =>
    rw [Block.repeat,B.bounds_prefix,List.mem_append] at hp
    exact hp.elim id ih

theorem component_le (f : ℕ×ℕ→ℕ) {p : ℕ×ℕ} {l : List (ℕ×ℕ)} (hp : p∈l) :
    f p≤(l.map f).sum := by
  induction l with
  | nil => exact (List.not_mem_nil hp).elim
  | cons b l ih =>
    simp only [List.map_cons,List.sum_cons]
    cases List.mem_cons.mp hp with
    | inl h => rw [h]; omega
    | inr h => have := ih h; omega


/-- The fixed grid contains refresh row zero and its alphabet has a letter. -/
theorem alphabetCap_pos : 0<B.alphabetCap := by
  classical
  let j : Fin (B.refresh.last+1):=⟨0,Nat.zero_lt_succ _⟩
  let := (B.refresh.block j).hasLetter
  have member : (refreshSymbolBound B.refresh,1+2*(2^(B.exponent B.levels))*(2^(B.exponent B.levels)))∈
      B.fixedRecordBounds:=List.mem_append_right _ (List.mem_singleton_self _)
  have letter : 0<Fintype.card (B.refresh.block j).Alphabet:=Fintype.card_pos
  have digit : Fintype.card (B.refresh.block j).Alphabet≤refreshSymbolBound B.refresh:=
    Finset.le_sup (f:=fun i=>Fintype.card (B.refresh.block i).Alphabet) (Finset.mem_univ j)
  exact letter.trans_le (digit.trans (component_le Prod.fst member))


/-- All histograms of every real branch use a single word count per symbol, with a
fixed padded alphabet. Neither the instruction set nor the alphabet grows with n. -/
def recordTable (K W n rem : ℕ) (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (cap : B.alphabetCap≤K)
    (word : B.repeatFactor*((A.maxWidth+1)*B.widthBase^n)<2^W) :
    Program.RecordTable ((B.repeat n).run rem A) K W
      (((B.repeat n).directory rem (Fintype.card A.Base)).map NavigationDirectory.Stage.motifs) :=
  (B.repeat n).table K W ((A.maxWidth+1)*B.widthBase^n)
    (fun _ h=>⟨(component_le Prod.fst (B.bounds_repeat n h)).trans cap,
      (Nat.mul_le_mul_right _ (component_le Prod.snd (B.bounds_repeat n h))).trans_lt word⟩)
    rem A (B.repeat_widthCeiling n rem A)

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
