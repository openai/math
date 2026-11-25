import OAI.Hierarchy.ProbeStageRecordSpace
import OAI.Hierarchy.ProbeMaskedRoute
import OAI.Hierarchy.ProbeStagePackedMasks

namespace OAI
/-! # Fixed record-advice arrays and initial masks -/

namespace Hierarchy.ProbeStage.Native

open scoped Fin.CommRing

def rowCode {B : ℕ} (r : MaskIndex B) := (finProdFinEquiv r).val

def readRow {B : ℕ} (f : MaskIndex B → ℕ) (i : ℕ) : ℕ :=
  if fit : i<B^2*B^2 then f (finProdFinEquiv.symm ⟨i,fit⟩) else 0

theorem readRow_at {B : ℕ} (f : MaskIndex B → ℕ) (r : MaskIndex B) : readRow f (rowCode r)=f r := by
  unfold readRow rowCode
  rw [dite_eq_left (finProdFinEquiv r).isLt]
  exact congrArg f (finProdFinEquiv.symm_apply_apply r)

def readFin {k : ℕ} (f : Fin k → ℕ) (i : ℕ) := if h : i<k then f ⟨i,h⟩ else 0

theorem readFin_at {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : readFin f i.val=f i := by simp [readFin,i.isLt]

def stringAt {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (i : ℕ) :=
  readRow (fun r => readFin (fun j => (strings r j).val) (i%ℓ)) (i/ℓ)

theorem stringAt_index {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (r : MaskIndex B) (p : Fin ℓ) :
    stringAt strings (rowCode r*ℓ+p.val)=(strings r p).val := by
  have lp : 0<ℓ := Nat.zero_lt_of_lt p.isLt
  have q : (rowCode r*ℓ+p.val)/ℓ=rowCode r := by rw [Nat.mul_comm (rowCode r) ℓ,Nat.mul_add_div lp,Nat.div_eq_of_lt p.isLt,Nat.add_zero]
  have s : (rowCode r*ℓ+p.val)%ℓ=p.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt p.isLt]
  rw [stringAt,q,s,readRow_at,readFin_at]

def directoryCapacity (B ℓ : ℕ) := B^4*ℓ

noncomputable def occurrenceAt {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (i : ℕ) :
    Option (PackedMask.Pos B ℓ) :=
  let c := i/directoryCapacity B ℓ
  if fit : c<B then (PackedMask.occurrences strings ⟨c,fit⟩)[i%directoryCapacity B ℓ]? else none

theorem occurrence_length {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B) :
    (PackedMask.occurrences strings c).length≤directoryCapacity B ℓ := by
  have card := Finset.card_le_univ (Finset.univ.filter fun p : PackedMask.Pos B ℓ => strings p.1 p.2=c)
  simpa [PackedMask.occurrences,PackedMask.Pos,MaskIndex,directoryCapacity,pow_succ,Nat.mul_assoc]
    using card

theorem occurrenceAt_index {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B) (i : ℕ)
    (hi : i<(PackedMask.occurrences strings c).length) :
    occurrenceAt strings (c.val*directoryCapacity B ℓ+i) = some ((PackedMask.occurrences strings c)[i]) := by
  let cap := directoryCapacity B ℓ
  have bound : i<cap := hi.trans_le (occurrence_length strings c)
  have pos := Nat.zero_lt_of_lt bound
  have q : (c.val*cap+i)/cap=c.val := by rw [Nat.mul_comm c.val cap,Nat.mul_add_div pos,Nat.div_eq_of_lt bound,Nat.add_zero]
  have s : (c.val*cap+i)%cap=i := by simp [Nat.add_mod,Nat.mod_eq_of_lt bound]
  simp only [occurrenceAt,← show cap=directoryCapacity B ℓ from rfl,q,s,dite_eq_left c.isLt,List.getElem?_eq_getElem hi]

def clearOffset {B ℓ : ℕ} (width chunks : ℕ) (p : PackedMask.Pos B ℓ) :=
  rowCode p.1*chunks+p.2.val/width

def clearWord {B ℓ : ℕ} (width : ℕ) (p : PackedMask.Pos B ℓ) := PackedMask.keep width (p.2.val%width)

/-- The initial mask words for both endpoints contain every color-position
in range. Each block has the same initialization. -/
def initialPacked {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (width chunks i : ℕ) :=
  readRow (fun r => PackedMask.word (strings r) ∅ width (i%chunks))
    ((i/chunks)%(B^2*B^2))

/-- All private counters start at zero. The directory tables, colors,
first-bit ROM, and clear descriptors are fixed entirely by the format. -/
noncomputable def arrayValue (h d j : ℕ) (k : Fin 16) (i : ℕ) : ℕ :=
  let B := radix h d
  let ℓ := stringLength h
  let width := fieldWidth h
  let chunks := fieldChunks h
  let strings := (formatAdvice h d).row
  ![region h d j 12+i*B,region h d j 13+i*B,
    region h d j 14+i*(B^4*chunks),region h d j 15+i*(B^4*chunks),
    i*chunks,i*ℓ,stringAt strings i,i.bitIndices.headD 0,
    i*directoryCapacity B ℓ,readFin (fun c => (PackedMask.occurrences strings c).length) i,
    ((occurrenceAt strings i).map (clearOffset width chunks)).getD 0,
    ((occurrenceAt strings i).map (clearWord width)).getD 0,
    0,0,initialPacked strings width chunks i,initialPacked strings width chunks i] k

end Hierarchy.ProbeStage.Native

end OAI
