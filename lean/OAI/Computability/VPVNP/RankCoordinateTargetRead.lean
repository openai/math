import OAI.Computability.VPVNP.RankCoordinateTargetPorts
import OAI.Computability.VPVNP.RankCoordinateSubmatrix
import OAI.Computability.VPVNP.RankQueryTagSpace
import OAI.Computability.VPVNP.MacaulayPairBounds

/-! # Physical scalar reader for the powered target row

The monomial pair scan compares the requested original column with the
powered target exponent. The returned bit selects a canonical field zero
or one. Both the exponent scan and the scalar copy restore the prepared
target parameters, so subsequent column queries use the same advice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.TargetRead

open RAMTape UniversalCountStack RadicalCertificate.MonomialIndex
open SliceArithmetic.CallClear (clear clear_bounded)

private def mount : PairCall.Port → Port
  | .external (.ordinal true) => .col
  | q => .aux (.inl q)

private theorem mount_inj : Function.Injective mount := by
  let q : PairCall.Port := .external (.ordinal true)
  have rest (a : PairCall.Port) (h : a ≠ q) : mount a = .aux (.inl a) := by
    cases a with
    | external f => cases f with
      | ordinal b => cases b <;> first | rfl | exact (h rfl).elim
      | _ => rfl
    | _ => rfl
  intro a b hab
  by_cases ha : a = q <;> by_cases hb : b = q <;> simp_all [q, mount]

private def copy (b : Bool) : FiniteRoutine Port :=
  SuccessorFields.prependCopy (.aux (.inr (.constant b))) .result (.aux (.inr .tmp))

/-- The equality word has numeric value zero or one. The tag scan reads its
low bit before the whole word is reclaimed. -/
def reader : FiniteRoutine Port :=
  ((PairCall.powered.onPorts mount).followedBy
    (TagRouter.select flagPort 1 (fun tag => copy (tag == 1)))).followedBy (clear flagPort)

/-- Inputs for a query of one target-row entry. The source ordinal is fixed and the column
ordinal is set to the requested column. -/
def live (d : PairCall.Inputs) (column : ℕ) : PairCall.Inputs :=
  {d with ordinal := fun b => if b then column else d.ordinal false}

/-- The two bounded monomial indices used by a target query, with the source at false and the
column at true. -/
def ordinals (d : PairCall.Inputs) (source : Fin (size d.arity (d.degree false)))
    (col : Fin (size d.arity (d.degree true))) : PairCall.Ordinals d
  | false => source
  | true => col

/-- Whether the enumerated column monomial equals the source monomial after applying the
specified power and coordinate shift. -/
def entryFlag (d : PairCall.Inputs) (source : Fin (size d.arity (d.degree false)))
    (col : Fin (size d.arity (d.degree true))) : Bool :=
  PairCall.powerMatch d (PairCall.monomial d (ordinals d source col) false)
    (PairCall.monomial d (ordinals d source col) true)

/-- Step bound for scanning both monomial indices, testing the powered exponents, copying the
selected field literal, and clearing the flag. -/
def clock (w B e v : ℕ) (d : PairCall.Inputs) :=
  PairCall.scanClock w B d + PairCall.powerClock d.arity w B + PairCall.clearCost w +
    (2+(5*(e*v)+2))+(w+1)

/-- Stack-height bound for the target-row reader, including the powered-monomial scan and the
copy of an `e`-limb scalar with `v` bits per limb. -/
def space (w B e v : ℕ) :=
  max (PairCall.poweredSpace w B) (max w (e*v)) + (5*(e*v)+2)

variable {p e r w v B : ℕ} [Fact p.Prime] [NeZero e] (c : SliceArithmetic.Vector p e)

/-- The packed field element returned for a Boolean entry flag, encoding one on a monomial
match and zero otherwise. -/
def literal (v : ℕ) (b : Bool) : List Bool :=
  Engine.scalar v (if b then (1 : Scalar c) else 0)

/-- The target reader’s work stacks contain the prepared monomial parameters and the two packed
field literals for this extension. -/
def Ready (w v : ℕ) (d : PairCall.Inputs) (s : Stacks Work) : Prop :=
  s = bank w d (literal c v)

omit [NeZero e] in
/-- Bound on each auxiliary stack before and after a target query. -/
theorem ready_bound (d : PairCall.Inputs) {s : Stacks Work} (hs : Ready c w v d s)
    (hword : w ≤ B) (harity : d.arity ≤ B) (k : Work) : (s k).length ≤ max B (e*v) := by
  subst s
  rcases k with (f | a | _) | a
  · have h := PairCall.values_le d (fun _ => []) [] [] hword harity (by simp) (by simp) (by simp) f
    cases f with
    | ordinal b => cases b <;> first | exact h.trans (le_max_left ..) | exact Nat.zero_le _
    | _ => exact h.trans (le_max_left ..)
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · cases a with
    | constant b => simp [bank, storage, literal]
    | tmp => exact Nat.zero_le _

private theorem mounted (d : PairCall.Inputs) (i j w : ℕ) (res flag : List Bool)
    (constants : Bool → List Bool) (q : PairCall.Port) :
    MacaulayRead.bank w i j res (storage w d constants flag) (mount q) =
      PairCall.publicBank w (live d j) (fun _ => []) [] flag q := by
  cases q with
  | external f => cases f with
    | ordinal b => cases b <;> rfl
    | _ => rfl
  | _ => rfl

private theorem outside (d : PairCall.Inputs) (i j w : ℕ) (flag : List Bool)
    (constants : Bool → List Bool) (p : Port) (hp : ∀ q, mount q ≠ p) :
    MacaulayRead.bank w i j [] (storage w d constants flag) p =
      MacaulayRead.bank w i j [] (storage w d constants []) p := by
  cases p with
  | row | col | result => rfl
  | aux p =>
    rcases p with (f | k | _) | e
    · cases f with
      | ordinal b => cases b <;> rfl
      | flag => exact (hp (.external .flag) rfl).elim
      | _ => rfl
    · rfl
    · rfl
    · cases e <;> rfl

omit [NeZero e] in
/-- The actual finite routine reads the target independently of the dense
row and uses the original column index as its second monomial address. -/
theorem correctSpace (d : PairCall.Inputs) (source : Fin (size d.arity (d.degree false)))
    (hsource : d.ordinal false = source.val) (hw : PairCall.requiredWidth d ≤ w)
    (hword : w ≤ B) (harity : d.arity ≤ B) :
    MacaulayRead.CorrectSpace reader
      (fun (_ : Fin r) j => if entryFlag d source j then (1 : Scalar c) else 0) w v
      (clock w B e v d) (space w B e v) (Ready c w v d) := by
  rintro i j _ rfl
  let data := live d j.val
  let ij : PairCall.Ordinals data := ordinals d source j
  let b := entryFlag d source j
  let fl := digits w b.toNat
  let frame (bits res : List Bool) := MacaulayRead.bank w i j res (storage w d (literal c v) bits)
  let cap := max (PairCall.poweredSpace w B) (max w (e*v))
  have hk (a : Bool) : data.ordinal a = (ij a).val := by cases a; exact hsource; rfl
  obtain ⟨hf, hx⟩ := PairCall.fits_of_width data ij hw
  have hpos : 0 < w := by
    have h := (hf false).one_lt
    by_contra! hh
    simp [show w = 0 by omega] at h
  obtain ⟨n, hn, raw⟩ := PairCall.powered_runs data ij hk hf hx [] [] hword harity (by simp) (by simp)
  have flagEq : PairCall.powerMatch data (PairCall.monomial data ij false) (PairCall.monomial data ij true) = b := rfl
  rw [flagEq, List.append_nil] at raw
  have scan : (PairCall.powered.onPorts mount).BoundedRun cap n (frame [] []) (frame fl []) := by
    refine FiniteRoutine.BoundedRun.framed mount_inj (raw.enlarge (le_max_left ..)) ?_
      (mounted d i j w [] [] _)
      (mounted d i j w [] fl _)
      (outside d i j w fl _)
    intro z
    cases z with
    | row | col =>
      simp only [frame, MacaulayRead.bank, length_digits]
      exact (le_max_left ..).trans (le_max_right ..)
    | result => exact Nat.zero_le _
    | aux z =>
      rcases z with z | z
      · by_cases he : z = .external (.ordinal true)
        · subst z; exact Nat.zero_le _
        · have hm : mount z = .aux (.inl z) := by
            cases z with
            | external f => cases f with
              | ordinal u => cases u <;> first | rfl | exact (he rfl).elim
              | _ => rfl
            | _ => rfl
          change ((frame [] []) (.aux (.inl z))).length ≤ cap
          rw [← hm, show (frame [] []) (mount z) = _ from mounted d i j w [] [] _ z]
          exact (raw.initial_cap z).trans (le_max_left ..)
      · cases z with
        | constant b =>
          simp only [frame, MacaulayRead.bank, storage, literal, Engine.scalar_length]
          exact (le_max_right ..).trans (le_max_right ..)
        | tmp => exact Nat.zero_le _
  let ans := literal c v b
  have copyRun : (copy b).Runs (5*(e*v)+2) (frame fl []) (frame fl ans) := by
    have cp := SuccessorFields.prependCopy_runs (K := Port) (.aux (.inr (.constant b))) .result (.aux (.inr .tmp))
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (frame fl []) rfl
    have endBank : Function.update (frame fl []) MacaulayRead.Port.result ans = frame fl ans := by
      funext p; cases p <;> rfl
    change (copy b).Runs (5*ans.length+2) (frame fl []) (Function.update (frame fl []) .result (ans++[])) at cp
    rw [List.append_nil, endBank] at cp
    simpa only [ans, literal, Engine.scalar_length] using cp
  have copied := spaceRun_of_steps copyRun (fun z => Nat.add_le_add_right (scan.final_cap z) _)
  have selected := TagRouter.digits_bounded flagPort (fun tag => copy (tag == 1)) hpos
    (show b.toNat < 2^1 by cases b <;> decide) (frame fl []) (frame fl ans) rfl
    (by simpa only [show (b.toNat == 1) = b by cases b <;> rfl] using copied)
  have cleared := clear_bounded flagPort (frame fl ans) (space w B e v) selected.final_cap
  have ef : Function.update (frame fl ans) flagPort [] = frame [] ans := by
    funext z; cases z with
    | aux z =>
      rcases z with (f | k | _) | e
      · cases f with | ordinal b => cases b <;> rfl | _ => rfl
      · rfl
      · rfl
      · cases e <;> rfl
    | _ => rfl
  rw [ef] at cleared
  change (clear flagPort).BoundedRun _ (fl.length+1) _ _ at cleared
  simp only [fl, length_digits] at cleared
  have all := ((scan.enlarge (Nat.le_add_right cap _)).followedBy selected).followedBy cleared
  refine ⟨_, ?_, bank w d (literal c v), rfl, all⟩
  unfold clock
  exact Nat.add_le_add_right (Nat.add_le_add_right hn _) _

/-- The native equality flag reads exactly the field-valued powered target
of a Frobenius or label operation. -/
theorem map_match {F : Type*} [Semiring F] (φ : Scalar c →+* F) {a : ℕ}
    (d : PairCall.Inputs) (S : QueryData d.arity a F) (op : QueryData.Operation d.arity)
    (source : Fin (size d.arity (d.degree false))) (j : Fin (size d.arity (d.degree true)))
    (hscale : d.scale = PairCall.targetScale S op) (hmark : d.mark = PairCall.targetMark op) :
    φ (if entryFlag d source j then (1 : Scalar c) else 0) =
      powerEntry S.power (S.target op (indexedDigits source)) j := by
  have h := PairCall.powerMatch_target d (ordinals d source j) S op hscale hmark
  change φ (if entryFlag d source j then 1 else 0) = _
  rw [apply_ite φ, map_one, map_zero]
  exact h

end RankQuery.Stack.Coordinate.TargetRead

end VPVNP
end Computability
end OAI
