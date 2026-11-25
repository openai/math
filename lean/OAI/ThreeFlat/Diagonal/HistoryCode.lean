import OAI.ThreeFlat.Diagonal.HistoryContraction

namespace OAI
/-! # Canonical encodings of adaptive compression histories

Term records may describe a full vector of motif histograms, so the record
length can exceed one RAM word. Each visited step reads its own advertised
number of bits before deciding the topology of the next stage.
-/

namespace ThreeFlat.Diagonal.HistoryContraction

/-- Each admitted fixed-length record encodes a unique term. -/
structure Record (n : ℕ) where
  width : ℕ
  write : Fin n → List Bool
  read : List Bool → Option (Fin n)
  write_length : ∀ i, (write i).length = width
  read_write : ∀ i, read (write i) = some i
  write_read : ∀ s i, read s = some i → write i = s

namespace Plan

variable {F : Type*} [CommSemiring F] {S : Shape}

def Codes : {S : Shape} → Plan F S → Type
  | _, .done _ => Unit
  | _, .step R next => Record R.count × (∀ t, (next t).Codes)

def write : {S : Shape} → (P : Plan F S) → P.Codes → P.History → List Bool
  | _, .done _, _, _ => []
  | _, .step _ next, E, h => E.1.write h.1 ++ (next h.1).write (E.2 h.1) h.2

/-- Parsing returns the exact unconsumed suffix, which may hold final wires. -/
def read : {S : Shape} → (P : Plan F S) → P.Codes → List Bool → Option (P.History × List Bool)
  | _, .done _, _, s => some ((),s)
  | _, .step _ next, E, s => do
    let t ← E.1.read (s.take E.1.width)
    let (h, rest) ← (next t).read (E.2 t) (s.drop E.1.width)
    return (⟨t,h⟩,rest)

theorem read_write (P : Plan F S) (E : P.Codes) (h : P.History) (tail : List Bool) :
    P.read E (P.write E h ++ tail) = some (h,tail) := by
  induction P with
  | done S => cases h; rfl
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    simp only [write, read, List.append_assoc]
    rw [← E.1.write_length t]
    simp [E.1.read_write, ih]

/-- Every accepted parse consumes exactly the written representation. -/
theorem write_read (P : Plan F S) (E : P.Codes) (s : List Bool) (h : P.History) (rest : List Bool)
    (parse : P.read E s = some (h,rest)) : s = P.write E h ++ rest := by
  induction P generalizing s rest with
  | done S =>
    cases h
    exact congrArg Prod.snd (Option.some.inj parse)
  | step R next ih =>
    unfold read at parse
    cases e : E.1.read (s.take E.1.width) with
    | none => simp [e] at parse
    | some t =>
      cases f : (next t).read (E.2 t) (s.drop E.1.width) with
      | none => simp [e,f] at parse
      | some v =>
        obtain ⟨h',rest'⟩ := v
        simp [e,f] at parse
        obtain ⟨rfl,rfl⟩ := parse
        change s = (E.1.write t ++ (next t).write (E.2 t) h') ++ rest
        rw [E.1.write_read _ t e, List.append_assoc, ← ih t _ _ _ _ f]
        exact (List.take_append_drop _ s).symm

/-- Padding a history to a fixed-size shared register is injective whenever
its actual encoding fits. The padding may be any deterministic suffix. -/
theorem write_suffix_injective (P : Plan F S) (E : P.Codes) (tail : P.History → List Bool) :
    Function.Injective (fun h => P.write E h ++ tail h) := by
  intro h h' eq
  have same := congrArg (P.read E) eq
  rw [P.read_write, P.read_write] at same
  exact congrArg Prod.fst (Option.some.inj same)

end Plan
end ThreeFlat.Diagonal.HistoryContraction

end OAI
