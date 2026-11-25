import OAI.Computability.MultitapeWeakETH.MotifGrid

/-! # A bit-time interpreter for both fixed motif blocks -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP StackInterpreter MotifBlocks MotifGrid MotifConversion MotifSelector
open PairSimulation LocalHistory
open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram
open scoped Classical
noncomputable section

variable {k J D E : Type} [Field k] [Fintype J] [Fintype D] [Fintype E] [DecidableEq J]
  {a b : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
  (B : FixedBlock k a b P (realWidths p) (realWidths q) H H') (hp : ∀ i, 0 < p i)

abbrev FixedInput (J : Type) := ((Widths × Label J) × List Bits.Word) × List (Bits.Word × Tally) × List Tally

/-- The party and actual incident bit strings together with all demand and payload widths.
The evaluator computes the repetition count from the demand widths. -/
def fixedInput (I : EntryInput B) : FixedInput J :=
  let m := mapInput a b P I.party I.demand I.payload (MotifEntry.demandBits a b I.party I.demandBits)
    (mapHalf P (fun _ => MotifEntry.inputBits) I.supplyBits)
  (((bank (fun i => tally (I.demand i)),⟨I.party⟩),m.1.1), m.1.2.1,m.2)

local instance labels : Fintype (parameterData B).Entry := Fintype.ofFinite _

/-- One fixed polynomial program returns the ordered template label ordinals. The same
program handles all copy counts, parties, field widths and values of this block. -/
theorem fixed_program (number : (parameterData B).Entry → ℕ) :
    ∃ eval : FixedInput J → Option (List Tally), Poly eval ∧ ∀ I : EntryInput B,
      eval (fixedInput B I) =
        (runEntry B hp I.demand I.payload I.party (MotifEntry.demandBits a b I.party I.demandBits)
          (mapHalf P (fun _ => MotifEntry.inputBits) I.supplyBits)).1.map (List.map (tally ∘ number)) := by
  let z (xs : FixedInput J) := demandGrid B hp (raw xs.1.1.1)
  let j (xs : FixedInput J) := xs.1.1.2
  let fields (xs : FixedInput J) : MapInput :=
    ((xs.1.2,(xs.2.1,tally (repetitions B (raw xs.1.1.1)))),xs.2.2)
  let zero : Selector B := (⟨0,B.copyCount_pos⟩,fun _ => ⟨_,B.grid.zero_mem_supplies⟩)
  let atTable (z : B.grid.demands) (j : J) := entry a b P (baseDemand B z) (basePayload B) j
    (fun s => lookup B z s j) zero (selectorTable B) (selectorCode B)
  have width : Poly (fun xs : FixedInput J => xs.1.1.1) := by fun_prop
  have reps := width.compose (copies_poly p B.scale)
  have input : Poly fields := by
    have old : Poly (fun xs : FixedInput J => xs.1.2) := by fun_prop
    have newB : Poly (fun xs : FixedInput J => xs.2.1) := by fun_prop
    exact (old.pair (newB.pair reps)).pair (Easy.snd.compose Easy.snd).poly
  have per (z : B.grid.demands) (j : J) : Poly (fun xs => atTable z j (fields xs)) :=
    input.compose (entry_poly ..)
  have party (z : B.grid.demands) : Poly (fun xs => atTable z (j xs).val (fields xs)) :=
    select_poly j (by unfold j; fun_prop) _ (per z) _ (Code.Poly.const none)
  let names (xs : FixedInput J) := atTable (z xs) (j xs).val (fields xs)
  have run : Poly names := select_poly _ (width.compose (grid_poly B hp)) _ party _ (Code.Poly.const none)
  let numbers (ls : List (Label (parameterData B).Entry)) := ls.map fun l => tally (number l.val)
  have convertNames : Poly numbers := Poly.maps _ (Easy.finite _).poly
  have save := bind_poly [] run ((Easy.snd.poly.compose convertNames).compose Easy.some.poly)
  refine ⟨fun xs => (names xs).map numbers,?_,?_⟩
  · convert save using 1
    funext xs
    cases names xs <;> rfl
  intro I
  let d := MotifEntry.demandBits a b I.party I.demandBits
  let x := mapHalf P (fun _ => MotifEntry.inputBits) I.supplyBits
  have rawEq : raw (bank (fun i => tally (I.demand i))) = I.demand := by
    funext i
    simp only [raw,fetch_bank,tally_length]
  have grid : z (fixedInput B I) = demandGrid B hp I.demand := congrArg (demandGrid B hp) rawEq
  have data : fields (fixedInput B I) = mapInput a b P I.party I.demand I.payload d x := by
    dsimp only [fields,fixedInput,mapInput,supplyInput]
    rw [rawEq]
    rfl
  change ((atTable (z (fixedInput B I)) I.party (fields (fixedInput B I))).map numbers) = _
  rw [grid,data]
  have eqn := entry_eq a b P (baseDemand B (demandGrid B hp I.demand)) (basePayload B) I.party zero
    (selectorTable B) (selectorCode B) I.demand I.payload d x (lookup B (demandGrid B hp I.demand))
  rw [show atTable (demandGrid B hp I.demand) I.party (mapInput a b P I.party I.demand I.payload d x) =
    (runEntry B hp I.demand I.payload I.party d x).1.map (List.map Label.mk) from eqn]
  cases (runEntry B hp I.demand I.payload I.party d x).1 <;> simp [numbers,Function.comp_def]

end
end OAI.Computability.MultitapeWeakETH.MotifFields
