import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxROM
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPublic
import OAI.Computability.NearSquareRoot.CommonAlphabetInterpreter

/-! # Running a structured program from its generated ROM on a fixed tape bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication CommonAlphabet
variable {A : Type} [Fintype A] {R : ℕ} (hR : 0 < R) (p : Prog A)

abbrev FixedTapes (R : ℕ) := Option (Option (Fin R))

noncomputable def inputWords (xs : List A) (j : FixedTapes R) : List (Data p) :=
  if j = fixedInput hR then xs.map (symbol p) else []

include hR in
private theorem register_count (bound : CommonRegisters.Within R p) :
    (idxNumbering (UnitSites p)).size ≤ R := by
  let emb : Prog.Idx (UnitSites p) ↪ Fin R :=
    ⟨fun i => ⟨i.val,CommonRegisters.used_lt hR bound i.property⟩, fun _ _ h => Subtype.ext (congrArg Fin.val h)⟩
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_embedding ((idxNumbering (UnitSites p)).equiv.symm.toEmbedding.trans emb)

/-- A register-bounded run starts at the literal loaded tape configuration and
halts with the entire result on the dedicated output tape. Its space bound
depends on the shared register cutoff and the run's two stack bounds. -/
theorem padded_run (bound : CommonRegisters.Within R p) {xs : List A} {r : Reg A} {n cap depth : ℕ}
    (run : Space.BoundedRun cap depth [] p (fun i => if i = 0 then xs else []) n r) :
    let m := paddedRule hR p bound
    let init := loadedConfig (entry p) none (inputWords hR p xs)
    let steps := 2*n + 1 + (r 0).length
    ∃ done, Trace (TM.advance m) init steps done ∧ TM.advance m done = none ∧
      TM.whole none ((r 0).map (symbol p)) (done.tape none) ∧
      VisitsAtMost m init steps ((R+2)*(4*max cap depth+6)) := by
  let e := CommonRegisters.indexEmbedding hR bound
  let cells := ((idxNumbering (UnitSites p)).size+2)*(4*max cap depth+5)
  obtain ⟨y,tr,stop,written,area⟩ := released_run p run
  obtain ⟨load,done,hl,he,htr,hstop,hout,harea⟩ :=
    CommonTapes.run_on_common_tapes e (released p) none (inputTape p) none (entry p)
      (xs.map (symbol p)) ((r 0).map (symbol p)) _ cells
      ⟨loaded p xs, y, by simp [loaded], fun i hi => by simp [loaded,hi], tr, stop, written, area⟩
  have hin : e (inputTape p) = fixedInput hR := rfl
  have eq : load = fun j => TM.Tape.loaded none (inputWords hR p xs j) := by
    funext j
    by_cases h : j = fixedInput hR
    · rw [← hin] at h
      subst j
      simpa only [inputWords, hin, ↓reduceIte] using hl
    · simpa only [inputWords, h, ↓reduceIte] using he j (by simpa only [hin] using h)
  rw [eq] at htr harea
  refine ⟨done,htr,hstop,hout,?_⟩
  obtain ⟨F,size,cover⟩ := harea
  refine ⟨F,size.trans ?_,cover⟩
  have count := register_count hR p bound
  have step := Nat.mul_le_mul_right (4*max cap depth+5) (Nat.add_le_add_right count 2)
  simp only [Fintype.card_option, Fintype.card_fin]
  dsimp only [cells]
  rw [Nat.mul_succ (R+2) (4*max cap depth+5)]
  omega

/-- The common interpreter executes the literal one-hot ROM of a structured
program. Both bounds charge the actual ROM length, and the input and output
words occupy their fixed tape indices. -/
theorem rom_run (a : Numbering A) (bound : CommonRegisters.Within R p)
    {xs : List A} {r : Reg A} {n cap depth : ℕ}
    (run : Space.BoundedRun cap depth [] p (fun i => if i = 0 then xs else []) n r) :
    let c := blockCode a p
    let program := rom a hR p bound
    let L := program.length
    let K := 4*(L+1)
    let steps := 2*n+1+(r 0).length
    let cells := (R+2)*(4*max cap depth+6)
    let tapes := fun j => TM.Tape.loaded none (c.encodeList (inputWords hR p xs j))
    let init := TapeSequence.relabel Sum.inl (Universal.Loader.initial none program tapes)
    let m := Universal.Loader.installAndRun (I := FixedTapes R) (none : Option Bool)
    ∃ t done, t ≤ 2*L+3 + K*(clock c steps+1) ∧ Trace (TM.advance m) init t done ∧
      TM.advance m done = none ∧ TM.whole (.inl (none : Option Bool))
        ((c.encodeList ((r 0).map (symbol p))).map Sum.inl) (done.tape (.inl none)) ∧
      VisitsAtMost m init t
        (Fintype.card (FixedTapes R) + 2*(L+1) +
          ((2*(1+5*c.width)+1)*cells*(2*K+1) + 2*(L+2*K+1))) := by
  obtain ⟨done,tr,halt,output,space⟩ := padded_run hR p bound run
  exact runProgram (dataNum a p) (controlNum a p) (Padding.fixed R) (blockCode a p)
    (paddedRule hR p bound) (entry p) none (oneHot_blank _ _) (inputWords hR p xs)
    _ _ done none ((r 0).map (symbol p)) tr halt output space


private theorem affine_bound (a b x : ℕ) : a + b*x ≤ (a+b)*(x+1) := by
  nlinarith only [Nat.zero_le (a*x), Nat.zero_le b]

/-- A single coefficient, fixed before choosing the input or its stack bounds,
controls both time and distinct visited cells of the installed interpreter. -/
theorem rom_run_linear (a : Numbering A) (bound : CommonRegisters.Within R p) :
    let c := blockCode a p
    let program := rom a hR p bound
    let m := Universal.Loader.installAndRun (I := FixedTapes R) (none : Option Bool)
    ∃ C : ℕ, ∀ {xs : List A} {r : Reg A} {n cap depth : ℕ},
      Space.BoundedRun cap depth [] p (fun i => if i = 0 then xs else []) n r →
      let tapes := fun j => TM.Tape.loaded none (c.encodeList (inputWords hR p xs j))
      let init := TapeSequence.relabel Sum.inl (Universal.Loader.initial none program tapes)
      ∃ t done, t ≤ C*(2*n+1+(r 0).length+1) ∧ Trace (TM.advance m) init t done ∧
        TM.advance m done = none ∧ TM.whole (.inl (none : Option Bool))
          ((c.encodeList ((r 0).map (symbol p))).map Sum.inl) (done.tape (.inl none)) ∧
        VisitsAtMost m init t (C*(max cap depth+1)) := by
  let L := (rom a hR p bound).length
  let K := 4*(L+1)
  let w := (blockCode a p).width
  let t₀ := 2*L+3+K*(2*w+1)
  let t₁ := K*(1+5*w)
  let B := (2*(1+5*w)+1)*(R+2)*(2*K+1)
  let s₀ := Fintype.card (FixedTapes R)+2*(L+1)+2*(L+2*K+1)+6*B
  let s₁ := 4*B
  let C := max (t₀+t₁) (s₀+s₁)
  refine ⟨C,?_⟩
  intro xs r n cap depth run
  obtain ⟨t,done,time,tr,stop,out,⟨cells,card,cover⟩⟩ := rom_run hR p a bound run
  let steps := 2*n+1+(r 0).length
  let height := max cap depth
  have time' : t ≤ t₀+t₁*steps := by
    convert time using 1
    dsimp only [clock,t₀,t₁,w,K,L,steps]
    ring
  have card' : cells.card ≤ s₀+s₁*height := by
    convert card using 1
    dsimp only [s₀,s₁,B,w,K,L,height]
    ring
  exact ⟨t,done,time'.trans ((affine_bound _ _ _).trans
    (Nat.mul_le_mul_right (steps+1) (le_max_left _ _))),tr,stop,out,
    cells,card'.trans ((affine_bound _ _ _).trans
      (Nat.mul_le_mul_right (height+1) (le_max_right _ _))),cover⟩

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
