import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.NearSquareRoot.ScheduleRegisterConstructors
import OAI.Computability.NearSquareRoot.KernelScaleRecord

/-! # One register budget for all finite dyadic matrices

The arithmetic leaves are fixed P192 commands on sign-and-magnitude words.
Unrolling fixed scalar multiplication, row accumulation, and matrix assembly
reuses their registers for all matrix dimensions and numerator lengths.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterSelect
open IntegerMultiplication Code KernelPass KernelPassMix Filter
open RegisterWitness (Timed)
local notation "RE" => RegisterWitness.Easy

/-- Unrolling a fixed output tuple needs no register per component. -/
theorem ofFn {X Y : Type*} [Codec X] [Codec Y] {R : ℕ} (hR : 3 ≤ R)
    {n : ℕ} (f : Fin n → X → Y) (h : ∀ j, RE R (f j)) :
    RE R (fun x => List.ofFn (fun j => f j x)) := by
  induction n with
  | zero => simpa using (RegisterWitness.Easy.const (by omega : 1 ≤ R) ([] : List Y) (X := X))
  | succ n ih =>
    simp_rw [List.ofFn_succ]
    exact ((RegisterWitness.Easy.pair hR (h 0) (ih (fun j => f j.succ) (fun j => h _))).compose
      RegisterWitness.Easy.cons)

/-- Constant natural scaling builds a sequence of additions without allocating
a register per addition. -/
theorem scale {R : ℕ} (hR : 3 ≤ R) (hAdd : RE R Bits.add) (n : ℕ) :
    RE R (Bits.scale n) := by
  induction n with
  | zero => exact RegisterWitness.Easy.const (by omega) []
  | succ n ih => exact (RegisterWitness.Easy.pair hR RegisterWitness.Easy.identity ih).compose hAdd

private theorem sums {R : ℕ} (hR : 3 ≤ R) (hPlus : RE R Grid.plusG)
    {X : Type*} [Codec X] {i : ℕ} (v : Fin i → X → Grid.Coef) (hv : ∀ j, RE R (v j)) :
    RE R (fun z => sumRecords (fun j => v j z)) := by
  induction i with
  | zero => exact RegisterWitness.Easy.const (by omega) _
  | succ i ih =>
    simp only [sumRecords,List.ofFn_succ,List.foldr_cons]
    exact (RegisterWitness.Easy.pair hR (hv 0) (ih _ fun j => hv j.succ)).compose hPlus

/-- A single cutoff works simultaneously for all matrix arities and
all dyadic coefficients, including unbounded signed numerators. -/
theorem mixMarked : ∀ᶠ R in atTop, ∀ i o (c : Fin o → Fin i → Coefficient),
    RE R (KernelPassMix.mixMarked c) := by
  have add : Code.Easy Bits.add := Bits.easy_add Code.Easy.identity
  filter_upwards [eventually_ge_atTop 4, easy_eventually add, easy_eventually Grid.easy_neg,
    easy_eventually Grid.facile_G, easy_eventually (Iter.facile (([],[]) : Dusk.Pair)),
    easy_eventually Grid.disp_easy, easy_eventually Grid.rest_easy,
    easy_eventually Grid.fit_easy, easy_eventually Grid.spell_easy] with
    R hR hAdd hNeg hPlus hPick hDisp hRest hFit hSpell
  have h1 : 1 ≤ R := by omega
  have h3 : 3 ≤ R := by omega
  have natScale (n : ℕ) : RE R (KernelPassMix.natScale n) :=
    RegisterWitness.Easy.pair h3 (RegisterWitness.Easy.fst hR)
      ((RegisterWitness.Easy.snd h1).compose (scale h3 hAdd n))
  have signed (n : ℤ) : RE R (signedScale n) := by
    cases n with
    | ofNat n => exact natScale n
    | negSucc n => exact (natScale _).compose hNeg
  have record (c : ℤ) : RE R (scaleRecord c) :=
    RegisterWitness.Easy.pair h3 ((RegisterWitness.Easy.fst hR).compose (signed c))
      ((RegisterWitness.Easy.snd h1).compose (signed c))
  have row {i : ℕ} (r : Fin i → Coefficient) : RE R (accumulateRow r) := by
    apply sums h3 hPlus
    intro j
    exact ((RegisterWitness.Easy.pair h3 RegisterWitness.Easy.identity
      (RegisterWitness.Easy.const h1 (tally j.val))).compose hPick |>.compose hDisp).compose (record _)
  intro i o c
  apply ofFn h3
  intro b
  exact (RegisterWitness.Easy.pair h3 (RegisterWitness.Easy.fst hR)
    ((RegisterWitness.Easy.pair h3 (RegisterWitness.Easy.const h1 (tally (denom (c b))))
      ((RegisterWitness.Easy.snd h1).compose (row (c b)))).compose hRest)).compose (hFit.compose hSpell)

/-- Decoding an arbitrarily large finite tag to choose a scalar function takes
the same register budget as its arbitrary finite table of continuations. -/
theorem select_map {X Y Z : Type*} [Codec X] [FiniteState X] [Codec Y] [Codec Z]
    {R : ℕ} (hR : 0 < R) (f : X → Y → Z) (h : ∀ j, RE R (f j)) :
    RE R (fun p : X × Y => f p.1 p.2) := by
  apply finite_select hR Prod.fst
  intro j
  let val (i : {z : X × Y // z.1 = j}) := i.val.2
  have branch := RegisterWitness.Timed.on (h j) val
  have b := RegisterWitness.Timed.bound branch (b := fun t => size t.val) 1 (fun t => by
    simp [size_prod,val]; omega)
  apply b.conform (fun _ => rfl) (fun _ => rfl)
  intro t
  change send (f j t.val.2) = send (f t.val.1 t.val.2)
  rw [t.property]

/-- One register cutoff covers the complete family of finite tag tables used
by the varying dyadic scale pass. -/
theorem selectedCoeff : ∀ᶠ R in atTop, ∀ n (c : Fin n → Coefficient),
    RE R (fun p : Fin n × Dusk.Pair => KernelScaleRecord.applyCoeff (c p.1) p.2) := by
  have prep : Code.Easy (fun x : Dusk.Pair => (ruler x.1,[x])) := by fun_prop
  filter_upwards [eventually_ge_atTop 1, mixMarked, easy_eventually prep,
    easy_eventually (Iter.leader (([],[]) : Dusk.Pair))] with R hR hm hp hh
  intro n c
  refine select_map hR (fun j => KernelScaleRecord.applyCoeff (c j)) (fun j => ?_)
  exact (hp.compose (hm 1 1 (fun _ _ => c j))).compose hh

end RegisterSelect

end NearSquareRoot
end Computability
end OAI
