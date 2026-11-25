import OAI.Computability.BorderVNP.CrossingCellWord
import OAI.Computability.BorderVNP.CrossingProfileScan

/-!
# Reading a profile selector in a private cell

The sparse address map reads consecutive copies and lanes at their declared
strides. Its little-endian label and prefix count agree with the physical
selector decoder and occurrence ordinal for every bank assignment, including
an empty selector when the alphabet has one term.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile.Cell

open CellSparse
variable {A j b : ℕ}

private theorem lanes_eq_ofFn (s : Port) (i width : ℕ) :
    s.lanes i width = List.ofFn (fun l : Fin width => s.atBit i l.val) := by
  apply List.ext_getElem
  · simp [Port.lanes]
  · intro n hn hm
    simp [Port.lanes]

/-- The physical selector obtained by reading each advertised cell-bank port. -/
def selector (bank : ℕ → Bool) (s : Port) :
    Fin j → Fin (Nat.clog 2 A) → Fin 2 :=
  fun i l => finTwoEquiv.symm (bank (s.atBit i l))

/-- The sparse label is the unsigned index of the same physical selector code. -/
theorem label_selector (bank : ℕ → Bool) (s : Port) (i : Fin j) :
    label bank s (Nat.clog 2 A) i =
      (finFunctionFinEquiv (selector (A := A) (j := j) bank s i)).val := by
  rw [label, lanes_eq_ofFn, word_ofFn]
  rfl

/-- Decoding a physical word is equivalent to equality of all its sparse numeric labels. -/
theorem decode_selector_iff (bank : ℕ → Bool) (s : Port) (w : Fin j → Fin A) :
    decode (selector bank s) = some w ↔
      ∀ i : Fin j, label bank s (Nat.clog 2 A) i = (w i).val := by
  rw [decode_eq_some_iff]
  constructor
  · intro h i
    rw [label_selector, congrFun h i]
    simp [encode]
  · intro h
    funext i
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    simpa only [encode, Equiv.apply_symm_apply, Fin.val_castLE, label_selector] using h i

/-- The ordinal computed by scanning the record equals the physical prefix
histogram on every prefix of a decoded word. -/
theorem earlier_eq_prefixCount (bank : ℕ → Bool) (s : Port) {w : Fin j → Fin A}
    (hw : decode (selector bank s) = some w) (a : Fin A) {n : ℕ} (hn : n ≤ j) :
    earlier bank s (Nat.clog 2 A) a.val n = prefixCount w n a := by
  induction n with
  | zero => simp [earlier, prefixCount_zero]
  | succ n ih =>
    let i : Fin j := ⟨n, hn⟩
    have he := (decode_selector_iff bank s w).mp hw i
    have hr := prefixCount_step w i a
    change prefixCount w (n + 1) a = _ at hr
    rw [hr, ← ih (by omega)]
    simp only [earlier, List.range_succ, List.map_append, List.map_singleton, List.count_append]
    rw [show label bank s (Nat.clog 2 A) n = (w i).val from he]
    simp [List.count_cons, Fin.ext_iff]

/-- The sparse header accepts exactly the physical words with the advertised histogram. -/
theorem header_iff (bank : ℕ → Bool) (s : Port) (p : Fin A → ℕ) :
    ((∀ i < j, label bank s (Nat.clog 2 A) i < A) ∧
      ∀ a : Fin A, earlier bank s (Nat.clog 2 A) a.val j = p a) ↔
    ∃ w : Fin j → Fin A, decode (selector bank s) = some w ∧ histogram w = p := by
  constructor
  · rintro ⟨hlabel, hhist⟩
    let w (i : Fin j) : Fin A := ⟨label bank s (Nat.clog 2 A) i, hlabel i i.isLt⟩
    have hw := (decode_selector_iff bank s w).mpr (fun _ => rfl)
    refine ⟨w, hw, funext fun a => ?_⟩
    rw [← prefixCount_end w a, ← earlier_eq_prefixCount bank s hw a le_rfl]
    exact hhist a
  · rintro ⟨w, hw, hp⟩
    refine ⟨fun i hi => ?_, fun a => ?_⟩
    · rw [show label bank s (Nat.clog 2 A) i = (w ⟨i, hi⟩).val from
        (decode_selector_iff bank s w).mp hw ⟨i, hi⟩]
      exact (w ⟨i, hi⟩).isLt
    · rw [earlier_eq_prefixCount bank s hw a le_rfl, prefixCount_end, hp]

/-- Feeders in the cell's assignment bank, ordered by each term's occurrences. -/
def feeders (p : Fin A → ℕ) (bank : ℕ → Bool) (ports : Fin A → Port) :
    ∀ a, Fin (p a) → Fin b → Bool := fun a i l => bank ((ports a).atBit i l)

/-- The bundle of original external copy slots read from the cell bank. -/
def external (bank : ℕ → Bool) (original : Port) : Fin (j * b) → Bool :=
  blocks.symm fun i l => bank (original.atBit i l)

/-- One sparse ordinal-routing rule per term, using the same source bundle. -/
def routes (A b : ℕ) (original : Port) (compact : Fin A → Port) : List Route :=
  List.ofFn fun a => ⟨a.val, b, original, compact a⟩

/-- After decoding the header, all sparse lane comparisons are exactly the
physical terminal's one-copy block comparisons. -/
private theorem routes_iff (bank : ℕ → Bool) (s original : Port) (compact : Fin A → Port)
    {w : Fin j → Fin A} {p : Fin A → ℕ} (hd : decode (selector bank s) = some w)
    (hp : histogram w = p) :
    (∀ r ∈ routes A b original compact, r.term < A ∧
      ∀ i < j, label bank s (Nat.clog 2 A) i = r.term →
        ∀ l < r.lanes, bank (r.original.atBit i l) =
          bank (r.compact.atBit (earlier bank s (Nat.clog 2 A) r.term i) l)) ↔
    ∀ a i, feeders (b := b) p bank compact a i =
      blocks (external (j := j) bank original) (slots w a hp i) := by
  simp only [routes, List.forall_mem_ofFn_iff, Fin.isLt, true_and, external, Equiv.apply_symm_apply]
  constructor
  · intro h a i
    let k := (slots w a hp i).val
    have hsel : w k = a := (Finset.mem_filter.mp (slots w a hp i).property).2
    have hlabel : label bank s (Nat.clog 2 A) k = a.val :=
      ((decode_selector_iff bank s w).mp hd k).trans (congrArg Fin.val hsel)
    have hord : earlier bank s (Nat.clog 2 A) a.val k = i.val := by
      rw [earlier_eq_prefixCount bank s hd a k.isLt.le]
      exact prefixCount_slot w hp a i
    funext l
    simpa only [hord, feeders] using (h a k k.isLt hlabel l l.isLt).symm
  · intro h a n hn hl l hlt
    let k : Fin j := ⟨n, hn⟩
    have hsel : w k = a := Fin.ext (((decode_selector_iff bank s w).mp hd k).symm.trans hl)
    let v : positions w a := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hsel⟩⟩
    let i := (slots w a hp).symm v
    have hk : (slots w a hp i).val = k := congrArg Subtype.val ((slots w a hp).apply_symm_apply v)
    have hord : earlier bank s (Nat.clog 2 A) a.val n = i.val := by
      rw [earlier_eq_prefixCount bank s hd a hn.le]
      change prefixCount w k.val a = i.val
      rw [← hk]
      exact prefixCount_slot w hp a i
    rw [hord]
    simpa only [feeders, hk] using (congrFun (h a i) (⟨l, hlt⟩ : Fin b)).symm

/-- Reading a row of the explicit public histogram gives its actual multiplicity. -/
theorem histRow_iff (f : ℕ → ℕ) (p : Fin A → ℕ) :
    (∀ a : Fin (List.ofFn p).length, f a.val = (List.ofFn p)[a.val]) ↔
      ∀ a : Fin A, f a.val = p a := by
  constructor
  · intro h a
    let a' : Fin (List.ofFn p).length := ⟨a.val, by simp⟩
    simpa [a'] using h a'
  · intro h a
    let a' : Fin A := ⟨a.val, by simpa using a.isLt⟩
    simpa [a'] using h a'

/-- The sparse terminal record has precisely the acceptance predicate of
the physical terminal table for the explicit selector, feeder and input ports. -/
theorem terminal_record_iff (bank : ℕ → Bool) (s original : Port) (compact : Fin A → Port)
    (j b : ℕ) (p : Fin A → ℕ) :
    profileValid bank j s (Nat.clog 2 A) (List.ofFn p) (routes A b original compact) ↔
      terminalTest p (selector bank s) (feeders p bank compact) (external (j := j) (b := b) bank original) := by
  simp only [profileValid, List.length_ofFn]
  have hhrow := histRow_iff (fun a => earlier bank s (Nat.clog 2 A) a j) p
  constructor
  · rintro ⟨hl, hh, hr⟩
    obtain ⟨w, hd, hp⟩ := (header_iff bank s p).mp ⟨hl, hhrow.mp hh⟩
    exact ⟨w, hp, hd, (routes_iff bank s original compact hd hp).mp hr⟩
  · rintro ⟨w, hp, hd, hr⟩
    have h := (header_iff bank s p).mpr ⟨w, hd, hp⟩
    exact ⟨h.1, hhrow.mpr h.2, (routes_iff bank s original compact hd hp).mpr hr⟩

end Crossing.Profile.Cell

end BorderVNP
end Computability
end OAI
