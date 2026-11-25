import OAI.Computability.MultitapeWeakETH.SiteCheck
import OAI.Computability.MultitapeWeakETH.TerminalColumns
import OAI.Computability.MultitapeWeakETH.FormulaLanes

/-! # Lane and offset lookup in the packed formula endpoint addresses -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck

open IntegerMultiplication Code VPVNP Compression NearSquareRoot.Benes PackedSwitches
open TerminalWords NativeGrid

def laneBytes {g : ℕ} (v : BitWord g) : Bits.Word := List.ofFn (fun i => finTwoEquiv (v i))

theorem laneBytes_injective {g : ℕ} : Function.Injective (laneBytes (g:=g)) := by
  intro x y h
  have e := List.ofFn_injective h
  exact funext fun i => finTwoEquiv.injective (congrFun e i)

theorem bytes_addressAt {g l : ℕ} (v : BitWord g) (s : Fin (2^l)) :
    List.ofFn (addressAt v s) = laneBytes v ++ BurstRAM.wordBits s := by
  change List.ofFn (Fin.append _ _) = _
  rw [List.ofFn_fin_append]
  rfl

theorem address_halves {g l : ℕ} (x : Word (g+l)) :
    cutLists (tally g,List.ofFn x) = (laneBytes (lane x),BurstRAM.wordBits ((packed g l x).2)) := by
  have e : addressAt (lane x) ((packed g l x).2) = x := (packed g l).symm_apply_apply x
  have bytes := (congrArg List.ofFn e).symm.trans (bytes_addressAt ..)
  have len : (laneBytes (lane x)).length=g := List.length_ofFn
  have cut (xs ys : Bits.Word) : cutLists (tally xs.length,xs++ys) = (xs,ys) := by simp [cutLists]
  rw [bytes]
  exact (congrArg (fun k => cutLists (tally k,laneBytes (lane x) ++ BurstRAM.wordBits ((packed g l x).2))) len.symm).trans (cut ..)

/-- The column has the two banks of observed endpoint bits. Compute an
offset in unary only up to the length of the supplied bank. -/
def atOffset (q : (Tally × Bits.Word) × Bits.Word) : Bool :=
  Iter.pick false (q.2,capped ((cutLists q.1).2,ruler q.2))

theorem atOffset_poly : Poly atOffset := by
  have tail : Easy (fun q : (Tally × Bits.Word) × Bits.Word => (cutLists q.1).2) :=
    (easy_cut Easy.fst).sndCompose
  have off := (tail.pair (Easy.ruler Easy.snd)).poly.compose capped_poly
  exact (Easy.snd.poly.pair off).compose (Iter.facile false).poly

theorem atOffset_eq {g l : ℕ} (x : Word (g+l)) (bank : Fin (2^l) → Bool) :
    atOffset ((tally g,List.ofFn x),List.ofFn bank) = bank ((packed g l x).2) := by
  rw [atOffset,address_halves]
  simp only [capped,value_native,ruler_length,List.length_ofFn,
    Nat.min_eq_left (packed g l x).2.isLt.le,Iter.entry]

abbrev Observations := Tally × Bits.Word × Bits.Word

/-- The side tag of the end key selects the observed input or output bank. -/
def observed (q : Observations × (Bool × Bits.Word)) : Bool :=
  atOffset ((q.1.1,q.2.2),bif q.2.1 then q.1.2.1 else q.1.2.2)

theorem observed_poly : Poly observed := by
  have bank : Poly (fun q : Observations × (Bool × Bits.Word) =>
      bif q.2.1 then q.1.2.1 else q.1.2.2) := Poly.choose (by fun_prop) (by fun_prop) (by fun_prop)
  exact ((show Poly (fun q : Observations × (Bool × Bits.Word) => (q.1.1,q.2.2)) by fun_prop).pair bank).compose atOffset_poly

end OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck
