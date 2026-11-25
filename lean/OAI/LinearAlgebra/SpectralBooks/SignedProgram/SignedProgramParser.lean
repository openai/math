import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramParserCircuit

/-! # Parsimonious Boolean decoder for the signed universal witness

The public input is the entire machine input, including its program prefix.
On success exactly one private bit string passes the decoder. This string
recovers the returned program through the table accessor used by execution.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram.Hot

open SignedMachine ExactQuantumFactoring BooleanNetwork
variable {n : ℕ}

private theorem check_and_frame {x : Basis n} {g : Basis (decodeGuessWidth n)}
    (hcode : WellCoded g) (hframe : FrameValid g) :
    ((Unary.check (wires n)).eval (Fin.append x g) 0 = true ∧
     (Unary.frameTest (frameWire n) (cursorWire n (Fin.last (slotsCount n)))).eval (Fin.append x g) 0 = true) ↔
    Unary.LocalCheck x ((tableOfBits g).slot (frameOfBits g)) (fun i j ↦ marksOfBits g i j = true) ∧
      ∀ j, marksOfBits g (Fin.last _) j = true → j.val = 2*(frameOfBits g).val+1 := by
  have hfr (v : Fin (n+1)) : (frameWire n v).eval (Fin.append x g) 0 = true ↔ v = frameOfBits g := by
    simpa only [frameWire,guessBit_eval] using frameOfBits_spec hframe v
  have hs := Unary.check_correct (wires n) (Fin.append x g) ((tableOfBits g).slot (frameOfBits g))
    (slotNet_correct (fieldBit_agrees x g hcode) (frameWire n) (frameOfBits g) hfr)
  simp only [wires, eval_bit, Fin.append_left, cursorWire, guessBit_eval] at hs
  change (Unary.check (wires n)).eval (Fin.append x g) 0 = true ↔ Unary.LocalCheck x _ (fun i j ↦ marksOfBits g i j = true) at hs
  rw [hs]
  apply and_congr_right
  intro hlocal
  obtain ⟨e,_,hmarks⟩ := (Unary.localCheck_iff _ _ _).mp hlocal
  have hend (v : Fin (n+1)) :
      (cursorWire n (Fin.last (slotsCount n)) v).eval (Fin.append x g) 0 = true ↔ v = e (Fin.last _) := by
    simpa [cursorWire,marksOfBits] using hmarks (Fin.last _) v
  rw [Unary.frameTest_correct _ _ _ _ _ hfr hend]
  constructor
  · intro h j hj
    exact (congrArg Fin.val ((hmarks _ _).mp hj)).trans h
  · intro h
    exact h _ ((hmarks _ _).mpr rfl)

/-- The Boolean network accepts exactly the normalized typed certificates, with
every private bit checked. -/
theorem parseNet_correct (x : Basis n) (g : Basis (decodeGuessWidth n)) :
    (parseNet n).eval (Fin.append x g) 0 = true ↔
      WellCoded g ∧ FrameValid g ∧ Accepts x (unpack g) := by
  simp only [parseNet,eval_band,Bool.and_eq_true,codeNet_correct,frameCodeNet_correct]
  apply and_congr_right
  intro hcode
  apply and_congr_right
  intro hf
  have hread := fieldBit_agrees x g hcode
  rw [paddingNet_correct hread,distinctRows_correct hread, distinct_iff,
    fitsNet_correct hread (frameOfBits g), check_and_frame hcode hf]
  rfl

/-- Invalid prefixes have no accepting assignment. -/
theorem parseNet_decode {x : Basis n} {g : Basis (decodeGuessWidth n)}
    (hg : (parseNet n).eval (Fin.append x g) 0 = true) :
    ProgramCode.decode (List.ofFn x) = some (tableOfBits g).program :=
  ((parseNet_correct _ _).mp hg).2.2.decode

theorem parseNet_wellCoded {x : Basis n} {g : Basis (decodeGuessWidth n)}
    (hg : (parseNet n).eval (Fin.append x g) 0 = true) : WellCoded g :=
  ((parseNet_correct _ _).mp hg).1

theorem parse_guesses_equal {x : Basis n} {g h : Basis (decodeGuessWidth n)}
    (hg : (parseNet n).eval (Fin.append x g) 0 = true)
    (hh : (parseNet n).eval (Fin.append x h) 0 = true) : g = h := by
  obtain ⟨cg,fg,ag⟩ := (parseNet_correct _ _).mp hg
  obtain ⟨ch,fh,ah⟩ := (parseNet_correct _ _).mp hh
  calc
    g = encodeGuess (unpack g).1 (unpack g).2.1 (unpack g).2.2 := (encode_unpack cg fg).symm
    _ = encodeGuess (unpack h).1 (unpack h).2.1 (unpack h).2.2 :=
      congrArg (fun u : DecodeWitness n ↦ encodeGuess u.1 u.2.1 u.2.2) (accepts_unique ag ah)
    _ = h := encode_unpack ch fh

/-- A successful parse has precisely one accepting Boolean guess, and that guess
supplies exactly the program appearing in the referee's interpreter. -/
theorem unique_parse (x : Basis n) (p : Program) :
    ProgramCode.decode (List.ofFn x) = some p ↔
      ∃! g : Basis (decodeGuessWidth n),
        (parseNet n).eval (Fin.append x g) 0 = true ∧ (tableOfBits g).program = p := by
  refine ⟨fun hp ↦ ?_, ?_⟩
  · obtain ⟨u,⟨hu,hp'⟩,_⟩ := (decode_iff_unique_witness x p).mp hp
    let g := encodeGuess u.1 u.2.1 u.2.2
    have hg : (parseNet n).eval (Fin.append x g) 0 = true :=
      (parseNet_correct x g).mpr ⟨wellCoded_encodeGuess u.1 u.2.1 u.2.2,frameValid_encode u,(unpack_encode u) ▸ hu⟩
    refine ⟨g, ⟨hg, ?_⟩, fun k hk ↦ parse_guesses_equal hk.1 hg⟩
    simpa only [g,tableOfBits_encodeGuess] using hp'
  · rintro ⟨g,⟨hg,rfl⟩,_⟩
    exact parseNet_decode hg

/-- The decoder works on the original public string, leaving its payload accessible to simulation. -/
theorem invalid_iff_no_parse (x : Basis n) :
    ProgramCode.decode (List.ofFn x) = none ↔
      ∀ g : Basis (decodeGuessWidth n), (parseNet n).eval (Fin.append x g) 0 = false := by
  constructor
  · intro h g
    cases hg : (parseNet n).eval (Fin.append x g) 0 with
    | false => rfl
    | true =>
      have he := parseNet_decode hg
      rw [h] at he
      contradiction
  · intro h
    cases hp : ProgramCode.decode (List.ofFn x) with
    | none => rfl
    | some p =>
      obtain ⟨g,⟨hg,_⟩,_⟩ := (unique_parse x p).mp hp
      simp [h g] at hg

end SignedProgram.Hot

end SpectralBooks
end LinearAlgebra
end OAI
