import OAI.Computability.NearSquareRoot.KernelEffectiveMixParameters
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyFold
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyTally
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectMix

/-! # Generating the physical row arithmetic from a literal instruction

The same fixed suite of sign, addition, shift, and packing commands serves
every instruction. The numerical weights determine how many additions to
emit, and the matrix dimensions determine how many columns and rows to emit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveMix

open IntegerMultiplication Code KernelPass KernelPass.ComputableSyntax KernelPassMix
open KernelEffectiveFamily RegisterSelect Filter

private abbrev Fixed (R : ℕ) {X Y : Type} [Codec X] [Codec Y] (f : X → Y) :=
  RegisterWitness.Easy R f

private theorem fold_scale (n : ℕ) (w : Bits.Word) :
    (List.ofFn (fun _ : Fin n => w)).foldr (fun a b => Bits.add (a,b)) [] = Bits.scale n w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.ofFn_succ,List.foldr_cons,ih]; rfl

private theorem magnitudeFamily {R : ℕ} (hR : 4 ≤ R) (hAdd : Fixed R Bits.add) :
    Family R (fun t : Entry => natScale (weightMagnitude t)) := by
  have words := Family.foldList (P := Entry) (X := Bits.Word) hR
    weightMagnitude primrec_weightMagnitude.to_comp (v := fun _ => id)
    Family.identity Bits.add hAdd []
  have scale := words.congr fun t w => fold_scale (weightMagnitude t) w
  exact Family.pair (by omega) (Family.fixed (RegisterWitness.Easy.fst hR))
    ((Family.fixed (RegisterWitness.Easy.snd (by omega))).comp scale)

private theorem signedFamily {R : ℕ} (hR : 4 ≤ R) (hAdd : Fixed R Bits.add)
    (hNeg : Fixed R Grid.neg) :
    Family R (fun t : Entry => signedScale
      (numerator (rowDenom t.1) (KernelComputableDyadic.coefficient (raw t)))) := by
  have mag := magnitudeFamily hR hAdd
  have sgn := Family.ite (fun t => decide (negative t))
    primrec_negative.decide.to_comp (mag.comp (Family.fixed hNeg)) mag
  apply sgn.congr
  intro t s
  rw [signedScale_weight]
  by_cases h : negative t <;> simp [h]

private theorem sumFamily {R : ℕ} (hR : 4 ≤ R) (hAdd : Fixed R Bits.add)
    (hNeg : Fixed R Grid.neg) (hPlus : Fixed R Grid.plusG)
    (hPick : Fixed R (Iter.pick (([],[]) : Dusk.Pair))) (hDisp : Fixed R Grid.disp) :
    Family R (fun r : Row => accumulateRow (rowCoeff r)) := by
  let z (t : Entry) := numerator (rowDenom t.1) (KernelComputableDyadic.coefficient (raw t))
  have hs : Family R (fun t => signedScale (z t)) := signedFamily hR hAdd hNeg
  have sp : Family R (fun t => scaleRecord (z t)) :=
    Family.pair (by omega) ((Family.fixed (RegisterWitness.Easy.fst hR)).comp hs)
      ((Family.fixed (RegisterWitness.Easy.snd (by omega))).comp hs)
  have term := (((Family.pair (by omega : 3 ≤ R) Family.identity
    (Family.tally (by omega) (fun t : Entry => t.2) Computable.snd)).comp
    (Family.fixed hPick)).comp (Family.fixed hDisp)).comp sp
  have sums := Family.foldList hR (fun r : Row => arg r.1 0)
    (primrec_arg.comp Primrec.fst (.const 0)).to_comp term Grid.plusG hPlus ((false,[]),(false,[]))
  apply sums.congr
  intro r x
  unfold accumulateRow sumRecords
  rw [← rowDenom_eq_raw]
  rfl

/-- A complete row opcode emits a finite physical arithmetic command with
uniform register support and an index-dependent linear time constant. -/
theorem markedFamily : ∀ᶠ R in atTop, Family R (fun op : Op => mixMarked (coeff op)) := by
  have add : Code.Easy Bits.add := Bits.easy_add Code.Easy.identity
  filter_upwards [eventually_ge_atTop 4, easy_eventually add, easy_eventually Grid.easy_neg,
    easy_eventually Grid.facile_G, easy_eventually (Iter.facile (([],[]) : Dusk.Pair)),
    easy_eventually Grid.disp_easy, easy_eventually Grid.rest_easy,
    easy_eventually Grid.fit_easy, easy_eventually Grid.spell_easy] with
    R hR hAdd hNeg hPlus hPick hDisp hRest hFit hSpell
  have accum := sumFamily hR hAdd hNeg hPlus hPick hDisp
  have shift := (Family.pair (by omega : 3 ≤ R)
    (Family.tally (X := Tally × List Dusk.Pair) (by omega) rowDenom primrec_rowDenom.to_comp)
    ((Family.fixed (RegisterWitness.Easy.snd (by omega))).comp accum)).comp (Family.fixed hRest)
  have row := ((Family.pair (by omega : 3 ≤ R) (Family.fixed (RegisterWitness.Easy.fst hR)) shift).comp
    (Family.fixed hFit)).comp (Family.fixed hSpell)
  have rows := Family.foldList hR (fun op : Op => arg op 1)
    (primrec_arg.comp Primrec.id (.const 1)).to_comp row
    (fun v : Dusk.Pair × List Dusk.Pair => v.1 :: v.2) RegisterWitness.Easy.cons []
  apply rows.congr
  intro op x
  simp only [List.foldr_cons_nil]
  apply congrArg List.ofFn
  funext b
  simp only [rowDenom_eq]
  rfl

end EffectiveMix

end NearSquareRoot
end Computability
end OAI
