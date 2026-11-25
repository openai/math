import OAI.Computability.MultitapeWeakETH.EntryProgram
import OAI.Computability.MultitapeWeakETH.DispatchProgram
import OAI.Computability.NearSquareRoot.InterchangeROMAffineMask

/-! # Latest-write lookup over the initialized descriptor memory -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM
open NearSquareRoot.InterchangeAffineMask
open private eq_poly from OAI.Computability.NearSquareRoot.InterchangeROMAffineMask
noncomputable section

abbrev CellBytes := Bits.Word × Bits.Word
abbrev WriteBytes := List CellBytes

theorem value_native {w : ℕ} (a : Word w) : Bits.value (wordBits a) = a.val := by
  have e (bs : Bits.Word) : Bits.value bs = TapeWord.value bs := by
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [Bits.value,TapeWord.value,ih]
  exact (e _).trans (TapeWord.value_wordBits a)

def writes {w : ℕ} (xs : List (Word w × Word w)) : WriteBytes :=
  xs.map fun p => (wordBits p.1,wordBits p.2)

/-- Newest-first external stores override the initial word queried on a miss. -/
def memory {w : ℕ} (base : Memory w) : List (Word w × Word w) → Memory w
  | [] => base
  | (a,v)::xs => writeMemory (memory base xs) a v

private def hits (q : Bits.Word × WriteBytes) : List Bits.Word :=
  (q.2.map fun p => bif eqWord (q.1,p.1) then [p.2] else []).flatten

private theorem hits_poly : Poly hits := by
  have flag : Poly (fun p : Bits.Word × CellBytes => eqWord (p.1,p.2.1)) := (Easy.fst.pair (Easy.snd.compose Easy.fst)).poly.compose eq_poly
  have row : Poly (fun p : Bits.Word × CellBytes => bif eqWord (p.1,p.2.1) then [p.2.2] else []) :=
    Poly.choose flag (by fun_prop) (Code.Poly.const [])
  exact (Poly.push [] ([],[]) row).compose Easy.flatten.poly

private def firstOr (q : List Bits.Word × Bits.Word) : Bits.Word := (q.1 ++ [q.2]).headD []

private theorem firstOr_poly : Poly firstOr :=
  (Easy.fst.poly.app (by fun_prop)).compose (Iter.leader []).poly

/-- Return one native word from its address, the external log and the
already computed initial word. All input and output fields are binary. -/
def lookup (q : (Bits.Word × WriteBytes) × Bits.Word) : Bits.Word := firstOr (hits q.1,q.2)

theorem lookup_poly : Poly lookup := ((Easy.fst.poly.compose hits_poly).pair Easy.snd.poly).compose firstOr_poly

theorem lookup_spec {w : ℕ} (base : Memory w) (log : List (Word w × Word w)) (a : Word w) :
    lookup ((wordBits a,writes log),wordBits (base a.val)) = wordBits (memory base log a.val) := by
  induction log with
  | nil => rfl
  | cons p log ih =>
    obtain ⟨k,v⟩ := p
    by_cases same : a=k
    · subst k
      simp [lookup,hits,firstOr,writes,memory,writeMemory]
    · simpa [lookup,hits,firstOr,writes,memory,writeMemory,value_native,Fin.val_ne_of_ne same] using ih

private theorem resize_native {w : ℕ} (bs : Bits.Word) (a : Word w) (v : Bits.value bs = a.val) :
    Bits.resize (tally w,bs) = wordBits a := by
  change Bits.sized w bs = _
  apply Bits.word_inject
  · simp
  · rw [Bits.sized_low,v,Nat.mod_eq_of_lt a.isLt,value_native]

attribute [local irreducible] entryMemory scale

set_option maxHeartbeats 1200000 in
/-- The descriptor's actual external memory is available by a polynomial
tape callback after any sequence of writes. The width is read from the
address and the grid index selects the initial contents. -/
theorem descriptor_memory_program {k : Type} [Field k] {S : VPVNP.Compression.BlockSchedule k} (B : S.Templates) :
    ∃ read : (Tally × Bits.Word) × WriteBytes → Bits.Word, Poly read ∧ ∀ (s : ℕ),
      let u := DyadicBudget.stepSize B*s
      let n := scale B s
      let w := VPVNP.CursorBounds.wordBits 1 n
      let base := entryMemory B (3*u) u n s w
      ∀ (log : List (Word w × Word w)) (a : Word w),
        read ((tally s,wordBits a),writes log) = wordBits (memory base log a.val) := by
  obtain ⟨base,program,spec⟩ := entry_program B
  let fallback (q : Tally × Bits.Word) := Bits.resize (ruler q.2,base q)
  have cost : Poly fallback :=
    (((Easy.ruler Easy.snd).poly.pair program).compose (Bits.easy_resize Easy.identity).poly)
  refine ⟨fun q => lookup ((q.1.2,q.2),fallback q.1),
    ((((Easy.fst.compose Easy.snd).pair Easy.snd).poly.pair (Easy.fst.poly.compose cost)).compose lookup_poly),?_⟩
  intro s u n w m log a
  have val := spec (tally s,wordBits a)
  dsimp only at val
  rw [tally_length,value_native] at val
  have width : ruler (wordBits a) = tally w := by rw [← recover_tally (ruler _),ruler_length,length_wordBits]
  have initial : fallback (tally s,wordBits a) = wordBits (m a.val) := by
    change Bits.resize (ruler (wordBits a),base (tally s,wordBits a)) = _
    rw [width]
    exact resize_native (base (tally s,wordBits a)) (m a.val) val
  change lookup ((wordBits a,writes log),fallback (tally s,wordBits a)) = _
  rw [initial,lookup_spec]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
