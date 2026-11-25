import OAI.Computability.NearSquareRoot.CommonAlphabet
import OAI.Computability.NearSquareRoot.CommonAlphabetNumbering

/-! # Installing a block-serialized finite machine on the common interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type}

private theorem dataCell_whole {G : Type} (blank : G) (z : List G) (S : TM.Tape G)
    (h : TM.whole blank z S) : TM.whole (.inl blank : Universal.Letter G I)
      (z.map Sum.inl) (Universal.dataCell S) := by
  funext p
  change Sum.inl (S.absolute p) = _
  rw [congrFun h p]
  cases p with
  | ofNat i =>
    simp only [TM.Tape.absolute, TM.Tape.loaded, sub_zero, List.getElem?_map]
    cases z[i]? <;> rfl
  | negSucc i => rfl

variable [Fintype I]

/-- A ROM for the serialized finite control, with the initial block reader at row zero. -/
noncomputable def compiledROM [Finite A] [Finite Q] (c : Code A) (m : TM.Rule A Q I) (q : Q)
    (rows : List (I → Option Bool)) :=
  Universal.program (Universal.Reindex.rule
    (Universal.Reindex.finiteNumbering (readStart (I := I) c q)) (rule c m)) rows

/-- The physical interpreter does not depend on the candidate alphabet, states, or transition
table. The candidate contributes its finite program tape and block width. The time and
distinct-space coefficients are independent of the simulated input and run. -/
theorem runNumbered {states : ℕ} (c : Code A) (enum : PC A Q I c.width ≃ Fin states) (m : TM.Rule A Q I) (q : Q) (blank : A)
    (blankBlock : c.enc blank = fun _ => none) (rows : List (I → Option Bool))
    (complete : ∀ r, r ∈ rows) (s : I → List A) (n cells : ℕ) (y : TM.Config A Q I)
    (out : I) (z : List A)
    (run : Trace (TM.advance m) (loadedConfig q blank s) n y)
    (halt : TM.advance m y = none) (result : TM.whole blank z (y.tape out))
    (space : VisitsAtMost m (loadedConfig q blank s) n cells) :
    let rom := Universal.Reindex.encode enum (readStart c q) (rule c m) rows
    let L := rom.length
    let K := 4*(L+1)
    let d := fun i => TM.Tape.loaded none (c.encodeList (s i))
    let start := TapeSequence.relabel Sum.inl (Universal.Loader.initial none rom d)
    let machine := Universal.Loader.installAndRun (I := I) (none : Option Bool)
    ∃ t finish, t ≤ 2*L+3 + K*(clock c n+1) ∧
      Trace (TM.advance machine) start t finish ∧ TM.advance machine finish = none ∧
      TM.whole (.inl (none : Option Bool)) ((c.encodeList z).map Sum.inl) (finish.tape (.inl out)) ∧
      VisitsAtMost machine start t
        (Fintype.card I + 2*(L+1) + ((2*(1+5*c.width)+1)*cells*(2*K+1) + 2*(L+2*K+1))) := by
  let d (i : I) := TM.Tape.loaded none (c.encodeList (s i))
  have hr (i : I) : Represents c (d i) ((loadedConfig q blank s).tape i) :=
    c.represents_loaded blank blankBlock (s i)
  obtain ⟨R, hsim, hr'⟩ := simulate c m run d hr
  have hhalt := simulate_halt c m halt R
  have hspace := simulate_space c m run space d hr
  obtain ⟨t, finish, ht, actual, stop, tape, cells'⟩ :=
    Universal.Reindex.install_numbered enum (readStart (I := I) c q) none (rule c m) rows complete d
      hsim hhalt hspace
  refine ⟨t, finish, ht, actual, stop, ?_, cells'⟩
  rw [tape]
  exact dataCell_whole none _ _ (c.whole_of_represents blank blankBlock result (hr' out))

/-- The physical interpreter does not depend on the candidate alphabet, states, or transition
table. The candidate contributes its finite program tape and block width. The time and
distinct-space coefficients are independent of the simulated input and run. -/
theorem runInstalled [Finite A] [Finite Q] (c : Code A) (m : TM.Rule A Q I) (q : Q) (blank : A)
    (blankBlock : c.enc blank = fun _ => none) (rows : List (I → Option Bool))
    (complete : ∀ r, r ∈ rows) (s : I → List A) (n cells : ℕ) (y : TM.Config A Q I)
    (out : I) (z : List A)
    (run : Trace (TM.advance m) (loadedConfig q blank s) n y)
    (halt : TM.advance m y = none) (result : TM.whole blank z (y.tape out))
    (space : VisitsAtMost m (loadedConfig q blank s) n cells) :
    let rom := compiledROM c m q rows
    let L := rom.length
    let K := 4*(L+1)
    let d := fun i => TM.Tape.loaded none (c.encodeList (s i))
    let start := TapeSequence.relabel Sum.inl (Universal.Loader.initial none rom d)
    let machine := Universal.Loader.installAndRun (I := I) (none : Option Bool)
    ∃ t finish, t ≤ 2*L+3 + K*(clock c n+1) ∧
      Trace (TM.advance machine) start t finish ∧ TM.advance machine finish = none ∧
      TM.whole (.inl (none : Option Bool)) ((c.encodeList z).map Sum.inl) (finish.tape (.inl out)) ∧
      VisitsAtMost machine start t
        (Fintype.card I + 2*(L+1) + ((2*(1+5*c.width)+1)*cells*(2*K+1) + 2*(L+2*K+1))) :=
  runNumbered c (Finite.equivFin _) m q blank blankBlock rows complete s n cells y out z run halt result space

/-- The same interpreter starts from a computably constructed ROM when the source machine
comes with effective numberings for its finite types. -/
theorem runProgram (a : Numbering A) (q : Numbering Q) (i : Numbering I) (c : Code A)
    (m : TM.Rule A Q I) (entry : Q) (blank : A) (blankBlock : c.enc blank = fun _ => none)
    (s : I → List A) (n cells : ℕ) (y : TM.Config A Q I) (out : I) (z : List A)
    (run : Trace (TM.advance m) (loadedConfig entry blank s) n y)
    (halt : TM.advance m y = none) (result : TM.whole blank z (y.tape out))
    (space : VisitsAtMost m (loadedConfig entry blank s) n cells) :
    let rom := Numbering.program a q i c m entry
    let L := rom.length
    let K := 4*(L+1)
    let d := fun j => TM.Tape.loaded none (c.encodeList (s j))
    let start := TapeSequence.relabel Sum.inl (Universal.Loader.initial none rom d)
    let machine := Universal.Loader.installAndRun (I := I) (none : Option Bool)
    ∃ t finish, t ≤ 2*L+3 + K*(clock c n+1) ∧
      Trace (TM.advance machine) start t finish ∧ TM.advance machine finish = none ∧
      TM.whole (.inl (none : Option Bool)) ((c.encodeList z).map Sum.inl) (finish.tape (.inl out)) ∧
      VisitsAtMost machine start t
        (Fintype.card I + 2*(L+1) + ((2*(1+5*c.width)+1)*cells*(2*K+1) + 2*(L+2*K+1))) :=
  runNumbered c (Numbering.controller a q i c.width).equiv m entry blank blankBlock
    (i.arrow .ternary).all (i.arrow .ternary).mem_all s n cells y out z run halt result space

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
