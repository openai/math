import OAI.Computability.BorderVNP.PackedGridVerifierFactors

/-! # Staging the use reports of weighted unary sources

An original cell stores its factors once for a whole bottom bundle. Weighted
sources get consecutive private lanes at the end of each copy. A two-input
truth table compares each such lane to the selected wire. A compact list of
strided equalities connects precisely these lanes to the externally guessed
use bits in source-major, copy-minor order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse

/-- Number of entries with a weighted unary source. -/
def count : List Factor → ℕ
  | [] => 0
  | .unary _ _ :: fs => count fs + 1
  | _ :: fs => count fs

/-- The private equality table checking a selected wire against its staged use. -/
def compareUse (wire staged : ℕ) : Factor := .truth [wire, staged] [true,false,false,true]

/-- The little-endian two-wire row passes exactly when the two bits agree. -/
theorem compareUse_observe (wire staged off copy : ℕ) (bank : ℕ → Bool) :
    (compareUse wire staged).observe bank off copy =
      if bank (off+wire) = bank (off+staged) then some (false,none) else none := by
  cases hw : bank (off+wire) <;> cases hs : bank (off+staged) <;>
    simp [compareUse,Factor.observe,word,hw,hs]

/-- Stored factors with all weighted checks made relative to the current box copy. -/
def stage : ℕ → List Factor → List Factor
  | _, [] => []
  | next, .unary wire _ :: fs => compareUse wire next :: stage (next+1) fs
  | next, f :: fs => f :: stage next fs

/-- The sparse sidecar records the source label and its relative staging address.
The label is the original unary tag and is never used as a bank address here. -/
def sidecar : ℕ → List Factor → List (Port × ℕ)
  | _, [] => []
  | next, .unary _ tag :: fs => (tag,next) :: sidecar (next+1) fs
  | next, _ :: fs => sidecar next fs

/-- The bottom metadata has the same number of factors after staging. -/
@[simp] theorem stage_length (next : ℕ) (fs : List Factor) :
    (stage next fs).length = fs.length := by
  induction fs generalizing next with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [stage,ih]

/-- Only the designated weighted entries appear on the sidecar. -/
@[simp] theorem sidecar_length (next : ℕ) (fs : List Factor) :
    (sidecar next fs).length = count fs := by
  induction fs generalizing next with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [sidecar,count,ih]

/-- The staged relative lanes occupy exactly one consecutive prefix of the padding. -/
theorem sidecar_ranks (next : ℕ) (fs : List Factor) :
    (sidecar next fs).map Prod.snd = List.range' next (count fs) := by
  induction fs generalizing next with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [sidecar,count,ih,List.range'_succ]

/-- The physical stride includes the reserved report region in every copy. -/
def bottomStride (originalStride publicCap : ℕ) := originalStride + publicCap

/-- Relative staged bit of the original box, translated to this cell's local bank. -/
def stagedPort (base stride rel : ℕ) : Port := ⟨base+rel,stride,1⟩

/-- Consecutive compact report bits for the copies of one listed original source. -/
def usePort (cursor : ℕ) : Port := ⟨cursor,1,1⟩

/-- Bind one actual sparse equality record per listed position; advance by copies. -/
def links (base stride copies : ℕ) : ℕ → List (Port × ℕ) → List Record
  | _, [] => []
  | cursor, (_,rel) :: ps =>
      .equal copies 1 (stagedPort base stride rel) (usePort cursor) ::
        links base stride copies (cursor+copies) ps

/-- Pin the entire unused suffix to zero, including in cells with no sources. -/
def padding (base originalStride publicCap copies used : ℕ) : Record :=
  .zero copies (publicCap-used)
    (stagedPort base (bottomStride originalStride publicCap) (originalStride+used))

/-- Binding and zero records for one bottom bundle. -/
def reportRows (base originalStride publicCap copies cursor : ℕ) (fs : List Factor) : List Record :=
  links base (bottomStride originalStride publicCap) copies cursor (sidecar originalStride fs) ++
    [padding base originalStride publicCap copies (count fs)]

/-- Reading a compact use port advances one bit per copy. -/
@[simp] theorem usePort_atBit (cursor copy : ℕ) : (usePort cursor).atBit copy 0 = cursor+copy := by
  simp [usePort,Port.atBit]

/-- The staged port reads the relative lane in the physical copy of its box. -/
@[simp] theorem stagedPort_atBit (base stride rel copy lane : ℕ) :
    (stagedPort base stride rel).atBit copy lane = base+copy*stride+rel+lane := by
  simp [stagedPort,Port.atBit,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

/-- The original private factors with use guesses supplied in compact rank order. -/
def compactReads (bank : ℕ → Bool) (offset copy copies : ℕ) :
    ℕ → List Factor → List (Option (Bool × Option ℕ))
  | _, [] => []
  | cursor, .unary wire _ :: fs =>
      (if bank (offset+wire) = bank (cursor+copy) then some (false,none) else none) ::
        compactReads bank offset copy copies (cursor+copies) fs
  | cursor, f :: fs => f.observe bank offset copy :: compactReads bank offset copy copies cursor fs

/-- After the actual compact equality rows pass, every staged private read is the
original read with the guessed use bit of precisely that source and copy. -/
theorem stage_observe (bank : ℕ → Bool) (boxes : List (List Factor)) (base stride copies copy : ℕ)
    (hi : copy < copies) (next cursor : ℕ) (fs : List Factor)
    (h : ∀ r ∈ links base stride copies cursor (sidecar next fs), r.Valid boxes bank) :
    (stage next fs).map (fun f => f.observe bank (base+copy*stride) copy) =
      compactReads bank (base+copy*stride) copy copies cursor fs := by
  induction fs generalizing next cursor with
  | nil => rfl
  | cons f fs ih =>
    cases f with
    | truth | sign | gadget => simp [stage,compactReads,ih next cursor (by simpa [sidecar] using h)]
    | unary wire tag =>
      simp only [sidecar,links,List.mem_cons,forall_eq_or_imp] at h
      have hb := h.1 copy hi 0 (by decide)
      simp only [stagedPort_atBit,usePort_atBit,Nat.add_zero] at hb
      simp [stage,compactReads,compareUse_observe,hb,ih _ _ h.2]

/-- Zero padding and equality links force the assignment of every added bit. -/
def stageValue (use : ℕ → ℕ → Bool) (used copy rank : ℕ) : Bool :=
  if rank < used then use rank copy else false

private theorem links_valid (bank : ℕ → Bool) (boxes : List (List Factor)) (base stride copies : ℕ)
    (next cursor : ℕ) (fs : List Factor) :
    (∀ r ∈ links base stride copies cursor (sidecar next fs), r.Valid boxes bank) ↔
      ∀ t < count fs, ∀ i < copies, bank (base+i*stride+next+t) = bank (cursor+t*copies+i) := by
  induction fs generalizing next cursor with
  | nil => simp [sidecar,links,count]
  | cons f fs ih =>
    cases f with
    | truth | sign | gadget => simpa only [sidecar,count] using ih next cursor
    | unary wire tag =>
      simp only [sidecar,links,List.mem_cons,forall_eq_or_imp,count]
      rw [ih]
      simp only [Record.Valid,equalValid]
      constructor
      · rintro ⟨hhead,htail⟩ t ht i hi
        cases t with
        | zero => simpa using hhead i hi 0 (by decide)
        | succ t =>
          have hh := htail t (by omega) i hi
          simpa only [Nat.succ_mul,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
      · intro h
        constructor
        · intro i hi k hk
          have : k = 0 := by omega
          subst k
          simpa using h 0 (by omega) i hi
        · intro t ht i hi
          simpa only [Nat.succ_mul,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
            using h (t+1) (by omega) i hi

/-- All the staged lanes of every copy have their unique required values exactly
when the emitted sparse records pass, for arbitrary surrounding bank data. -/
theorem reportRows_valid (bank : ℕ → Bool) (boxes : List (List Factor)) (base orig cap copies cursor : ℕ)
    (fs : List Factor) (hcap : count fs ≤ cap) :
    (∀ r ∈ reportRows base orig cap copies cursor fs, r.Valid boxes bank) ↔
      ∀ i < copies, ∀ t < cap, bank (base+i*bottomStride orig cap+orig+t) =
        stageValue (fun u j => bank (cursor+u*copies+j)) (count fs) i t := by
  have splitRows : (∀ r ∈ reportRows base orig cap copies cursor fs, r.Valid boxes bank) ↔
      (∀ r ∈ links base (bottomStride orig cap) copies cursor (sidecar orig fs), r.Valid boxes bank) ∧
      (padding base orig cap copies (count fs)).Valid boxes bank := by
    constructor
    · intro h
      exact ⟨fun r hr => h r (List.mem_append_left _ hr), h _ (List.mem_append_right _ (by simp))⟩
    · intro h r hr
      rcases List.mem_append.mp hr with hl | hr
      · exact h.1 r hl
      · simpa only [List.mem_singleton.mp hr] using h.2
  rw [splitRows,links_valid]
  simp only [padding,Record.Valid,zeroValid,stagedPort_atBit]
  constructor
  · rintro ⟨hused,hzero⟩ i hi t ht
    by_cases h : t < count fs
    · simpa [stageValue,h] using hused t h i hi
    · have hz := hzero i hi (t-count fs) (by omega)
      rw [stageValue,ite_eq_right h]
      convert hz using 2
      omega
  · intro h
    constructor
    · intro t ht i hi
      simpa [stageValue,ht] using h i hi t (lt_of_lt_of_le ht hcap)
    · intro i hi k hk
      have hn : ¬ count fs+k < count fs := by omega
      simpa [stageValue,hn,Nat.add_assoc] using h i hi (count fs+k) (by omega)

/-- Given the compact use bits, the private padding has exactly one possible
extension; false reports and all unused lanes are included in this statement. -/
theorem unique_staged (copies cap used : ℕ) (use : ℕ → ℕ → Bool) :
    ∃! b : Fin copies → Fin cap → Bool,
      (∀ i (t : Fin cap), t.val < used → b i t = use t.val i.val) ∧
      (∀ i (t : Fin cap), used ≤ t.val → b i t = false) := by
  refine ⟨fun i t => stageValue use used i t, ⟨?_,?_⟩,?_⟩
  · intro i t ht
    simp [stageValue,ht]
  · intro i t ht
    simp [stageValue,Nat.not_lt.mpr ht]
  · intro b h
    funext i t
    by_cases ht : t.val < used
    · simpa [stageValue,ht] using h.1 i t ht
    · simpa [stageValue,ht] using h.2 i t (Nat.le_of_not_lt ht)

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
