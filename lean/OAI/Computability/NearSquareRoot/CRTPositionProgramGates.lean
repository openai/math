import OAI.Computability.NearSquareRoot.CRTPositionTableAction

/-! # A round of 36 directed XOR gates

Each gate carries the source chunk, the destination chunk and a table giving
the selected source index for every bit of the destination. The same compiler
handles arbitrary tables, including those with disabled ports.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication.Code PositionPreparation

set_option synthInstance.maxSize 5000

abbrev Gate := Fin 3 × Fin 3 × ReadTable

/-- Apply a single directed XOR gate to a full position word. -/
def directed {k : ℕ} (a : Gate) (w : Fin k → Bool) (x : Fin k) : Bool :=
  match threeChunksWithTail k x with
  | .inl (c,i) => if c = a.2.1 then
      xorFrom (decodePort a.2.2) (chunkWord w a.1) (chunkWord w a.2.1) i else w x
  | .inr _ => w x

def run {k : ℕ} (program : List Gate) (w : Fin k → Bool) : Fin k → Bool :=
  program.foldl (fun word a => directed a word) w

theorem run_append {k : ℕ} (a b : List Gate) (w : Fin k → Bool) :
    run (a++b) w = run b (run a w) := List.foldl_append

private def triple (s d : Fin 3) (t : Both) : List Gate :=
  [(s,d,t.1),(d,s,t.2),(s,d,t.1)]

private def borrow (c d : Fin 3) (rows : Borrow) : List Gate :=
  let idRead := rows.map Prod.fst
  let upRead := rows.map (Prod.fst ∘ Prod.snd)
  let downRead := rows.map (Prod.snd ∘ Prod.snd)
  let aux := triple c d (idRead,idRead)
  aux ++ triple c d (upRead,downRead) ++ aux

/-- Flatten the ordered six matching stages to their directed XORs. -/
def gates (t : RoundTables) : List Gate :=
  borrow 0 (NativeRound.auxiliary 0) t.2.1 ++ triple 0 1 t.1.1 ++
  triple 0 2 t.1.2.1 ++ borrow 1 (NativeRound.auxiliary 1) t.2.2.1 ++
  triple 1 2 t.1.2.2 ++ borrow 2 (NativeRound.auxiliary 2) t.2.2.2

@[fun_prop] private theorem triple_poly (s d : Fin 3) : Poly (triple s d) := by
  unfold triple
  fun_prop

@[fun_prop] private theorem borrow_poly (s d : Fin 3) : Poly (borrow s d) := by
  unfold borrow
  fun_prop

@[fun_prop] theorem gates_poly : Poly gates := by
  unfold gates
  fun_prop

@[simp] theorem gates_length (t : RoundTables) : (gates t).length = 36 := rfl

theorem gates_distinct (t : RoundTables) : ∀ a ∈ gates t, a.1 ≠ a.2.1 := by
  simp [gates,borrow,triple,NativeRound.auxiliary]

private theorem put_initial {k : ℕ} (s d : Fin 3) (w : Fin k → Bool) :
    writeRows s d (chunkWord w s,chunkWord w d) w = w := by
  funext x
  obtain ⟨u,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases u with
  | inr _ => simp [writeRows]
  | inl z =>
    rcases z with ⟨c,i⟩
    by_cases cs : c=s
    · subst c
      simp [writeRows,chunkWord]
    · by_cases cd : c=d
      · subst d
        simp [writeRows,chunkWord,cs]
      · simp [writeRows,cs,cd]

private theorem read_first {k : ℕ} (s d : Fin 3) (rows) (w : Fin k → Bool) :
    chunkWord (writeRows s d rows w) s = rows.1 := by
  funext i
  simp [chunkWord,writeRows]

private theorem read_second {k : ℕ} (s d : Fin 3) (h : s ≠ d) (rows) (w : Fin k → Bool) :
    chunkWord (writeRows s d rows w) d = rows.2 := by
  funext i
  simp [chunkWord,writeRows,h.symm]

private theorem target_second {k : ℕ} (s d : Fin 3) (sd : s ≠ d) (codes : ReadTable) (rows)
    (w : Fin k → Bool) :
    directed (s,d,codes) (writeRows s d rows w) =
      writeRows s d (rows.1,xorFrom (decodePort codes) rows.1 rows.2) w := by
  funext x
  obtain ⟨u,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases u with
  | inr _ => simp [directed,writeRows]
  | inl z =>
    rcases z with ⟨c,i⟩
    by_cases cd : c=d
    · subst c
      simp [directed,read_first,read_second s d sd,writeRows,sd.symm]
    · simp [directed,writeRows,cd]

private theorem target_first {k : ℕ} (s d : Fin 3) (sd : s ≠ d) (codes : ReadTable) (rows)
    (w : Fin k → Bool) :
    directed (d,s,codes) (writeRows s d rows w) =
      writeRows s d (xorFrom (decodePort codes) rows.2 rows.1,rows.2) w := by
  funext x
  obtain ⟨u,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases u with
  | inr _ => simp [directed,writeRows]
  | inl z =>
    rcases z with ⟨c,i⟩
    by_cases cs : c=s
    · subst c
      simp [directed,read_first,read_second s d sd,writeRows]
    · simp [directed,writeRows,cs]

private theorem run_triple_put {k : ℕ} (s d : Fin 3) (sd : s ≠ d) (t : Both)
    (rows) (w : Fin k → Bool) :
    run (triple s d t) (writeRows s d rows w) =
      writeRows s d (exchangeRows (decodePort t.2) (decodePort t.1) rows) w := by
  simp only [run,triple,List.foldl_cons,List.foldl_nil,target_second s d sd,target_first s d sd,exchangeRows]

private theorem run_triple {k : ℕ} (s d : Fin 3) (sd : s ≠ d) (t : Both)
    (w : Fin k → Bool) : run (triple s d t) w = crossFromRows t s d w := by
  unfold crossFromRows
  simpa only [put_initial] using run_triple_put s d sd t (chunkWord w s,chunkWord w d) w

private theorem run_borrow {k : ℕ} (c d : Fin 3) (cd : c ≠ d) (t : Borrow) (w : Fin k → Bool) :
    run (borrow c d t) w = borrowFromRows t c d w := by
  conv_lhs => rw [← put_initial c d w]
  simp only [borrow,run_append,run_triple_put c d cd]
  rfl

/-- Executing the 36 serialized gates equals execution of the complete round,
including on words with residual positions after the three chunks. -/
theorem run_gates {k : ℕ} (t : RoundTables) (w : Fin k → Bool) :
    run (gates t) w = runTables t w := by
  simp only [gates,run_append,run_borrow _ _ (NativeRound.auxiliary_ne _).symm,
    run_triple (0 : Fin 3) 1 (by decide),run_triple (0 : Fin 3) 2 (by decide),
    run_triple (1 : Fin 3) 2 (by decide),runTables]

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
