import OAI.ThreeFlat.Diagonal.CompressorNativePlacement
import OAI.ThreeFlat.Diagonal.CompressorRefreshGraph

namespace OAI
/-! # Native column updates of the port refresh

Old records are indexed by base and outgoing or incoming port. At a new
site the first slot is external, then come the ports of a fixed regular
graph, then the zero-width padding. The finite port graph is independent
of the growing old graph and is compiled into the fixed program.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Refresh
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr Placement
open scoped Fin.NatCast
variable {w k n D a : ℕ}

structure OldColumns (T : Type*) where
  neighbor : T
  mate : T
  remainingShift : T

inductive Field | neighbor | matePort | delta deriving DecidableEq

def findWord (x : Term w k n) : List (Word w × Word w) → Term w k n
  | [] => .literal 0
  | (k,v)::xs => .select .eq x (.literal k) (.literal v) (findWord x xs)

def findValue (x : Word w) : List (Word w × Word w) → Word w
  | [] => 0
  | (k,v)::xs => if x=k then v else findValue x xs

theorem eval_findWord (x : Term w k n) (xs : List (Word w × Word w)) (pub : Fin k → Word w)
    (m : Memory w) (vs : Fin n → Word w) :
    (findWord x xs).eval pub m vs = findValue (x.eval pub m vs) xs := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨key,v⟩ := e
    simp [findWord,findValue,Comparison.test,ih]

def portROM (E : SlotGraph (Fin D) a) (reverse : Bool)
    (part : Fin D × Fin a → ℕ) : List (Word w × Word w) :=
  (List.finRange D).flatMap fun i => (List.finRange a).map fun s =>
    (((i.val*a+s.val : ℕ) : Word w),
      ((part ((if reverse then E.target.symm else E.target) (i,s))) : Word w))

/-- The choice of input columns determines the orientation of external
slots; reverse also reverses the internal port graph and the padding cycle. -/
def row (E : SlotGraph (Fin D) a) (reverse : Bool) (nPad : ℕ) (which : Field)
    (old : OldColumns (Term w k 1)) (output : Term w k 1) : Term w k 1 :=
  let o := terms w k 1
  let z := o.bin .sub (.result 0) output
  let deg := o.lit (1+a+nPad)
  let vj := o.bin .div z deg
  let v := o.bin .div vj (o.lit D)
  let j := o.bin .mod vj (o.lit D)
  let edge := o.bin .mod z deg
  let external := match which with
    | .neighbor => o.bin .add (o.bin .mul (Placement.row o old.neighbor vj) (o.lit D))
        (Placement.row o old.mate vj)
    | .matePort => o.lit 0
    | .delta => Placement.row o old.remainingShift vj
  let lookup := o.bin .add (o.bin .mul j (o.lit a)) (o.bin .sub edge (o.lit 1))
  let internal := match which with
    | .neighbor => o.bin .add (o.bin .mul v (o.lit D))
        (findWord lookup (portROM E reverse fun z => z.1.val))
    | .matePort => o.bin .add (o.lit 1) (findWord lookup (portROM E reverse fun z => z.2.val))
    | .delta => o.lit 0
  let padding := match which with
    | .neighbor =>
      let jp := o.bin .mod (o.bin .add j (o.lit (if reverse then D-1 else 1))) (o.lit D)
      o.bin .add (o.bin .mul v (o.lit D)) jp
    | .matePort => edge
    | .delta => o.lit 0
  o.choose edge (o.lit 0) external (.select .lt edge (o.lit (1+a)) internal padding)

end ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

end OAI
