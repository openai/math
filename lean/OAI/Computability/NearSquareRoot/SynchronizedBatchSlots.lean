import OAI.Computability.NearSquareRoot.SynchronizedBatchWord
import OAI.Computability.NearSquareRoot.SynchronizedScheduleProgram

/-! # Physical opcode expansion of a borrowed-batch Walsh instruction

Microinstructions 1 through 8 route the active pairs, alternate the three
fixed-bit Walsh operations with three diagonal tables, and undo the route.
A directly placed phase or permutation has microinstruction number zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication IntegerMultiplication.Code SynchronizedLayers
open SynchronizedLayers.ScheduleProgram

abbrev SlotDescriptor := Descriptor × Tally

def microcode : List Tally := [tally 1,tally 2,tally 3,tally 4,tally 5,tally 6,tally 7,tally 8]

/-- Local physical instructions implementing one batch-tagged fixed-bit operation. -/
def lower (z : Descriptor) : List SlotDescriptor :=
  if z.2.2.1.length = 10 then microcode.map (fun t => (z,t)) else [(z,[])]

private theorem isTag {X : Type} [Codec X] {f : X → Tally} (h : Poly f) (n : ℕ) :
    Poly (fun x => decide ((f x).length = n)) := by
  have hp := (h.pair (Code.Poly.const (tally n))).compose (Iter.linked (X := Unit) (Y := Unit)).poly
  simpa only [tally_length] using hp

theorem lower_poly : Poly lower := by
  have ht := isTag (show Poly (fun z : Descriptor => z.2.2.1) by fun_prop) 10
  have yes := (Code.Poly.identity (X := Descriptor)).pair (Code.Poly.const microcode)
  have hpos := yes.compose (Poly.push (([],[],AxisWord.inst 0) : Descriptor) ([] : Tally)
    (Code.Poly.identity (X := Descriptor × Tally)))
  have hz : Poly (fun z : Descriptor => [(z,([] : Tally))]) := by fun_prop
  change Poly (fun z : Descriptor => if z.2.2.1.length = 10 then microcode.map (fun t => (z,t)) else [(z,[])])
  simpa only [Bool.cond_decide, polyPush] using Code.Poly.choose ht hpos hz

theorem lower_length_le (z : Descriptor) : (lower z).length ≤ 8 := by
  unfold lower
  split <;> simp [microcode]

def localSlots (w : List Descriptor) : List SlotDescriptor := w.flatMap lower

theorem localSlots_poly : Poly localSlots :=
  (Poly.maps _ lower_poly).compose Easy.flatten.poly

theorem localSlots_length_le (w : List Descriptor) : (localSlots w).length ≤ 8 * w.length := by
  induction w with
  | nil => simp [localSlots]
  | cons x xs ih =>
    simpa [localSlots, Nat.mul_succ, Nat.add_comm] using Nat.add_le_add (lower_length_le x) ih

/-- Each physical instruction has exactly one synchronized slot type. -/
def microKind (n : ℕ) : Kind :=
  if n = 1 ∨ n = 8 then .permutation
  else if n = 2 ∨ n = 4 ∨ n = 6 then .walsh else .diagonal

def slotKind (z : SlotDescriptor) : Kind :=
  if z.2.length = 0 then instructionKind z.1.2.2 else microKind z.2.length

private theorem poly_case {X : Type} [Codec X] (p : X → Prop) [DecidablePred p]
    (h : Poly (fun x => decide (p x))) (f g : X → Bool) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  simpa only [Bool.cond_decide] using Code.Poly.choose h hf hg

private theorem microKind_poly (s : Kind) : Poly (fun t : Tally => decide (microKind t.length = s)) := by
  let select (n : ℕ) (k : Kind) (f : Tally → Bool) := fun t =>
    if t.length = n then decide (k = s) else f t
  have hs (n : ℕ) (k : Kind) (f : Tally → Bool) (hf : Poly f) : Poly (select n k f) :=
    poly_case _ (isTag Code.Poly.identity n) _ _ (Code.Poly.const _) hf
  let q := select 1 .permutation <| select 8 .permutation <| select 2 .walsh <| select 4 .walsh <|
    select 6 .walsh (fun _ => decide (Kind.diagonal = s))
  have hq : Poly q := hs _ _ _ (hs _ _ _ (hs _ _ _ (hs _ _ _ (hs _ _ _ (Code.Poly.const _)))))
  convert hq using 1
  funext t
  simp only [q, select, microKind]
  split_ifs <;> simp_all

theorem slotKind_poly (s : Kind) : Poly (fun z => decide (slotKind z = s)) := by
  have h := poly_case (fun z : SlotDescriptor => z.2.length = 0) (isTag Easy.snd.poly 0) _ _
    ((show Poly (fun z : SlotDescriptor => z.1.2.2) by fun_prop).compose (instructionKind_poly s))
    (Easy.snd.poly.compose (microKind_poly s))
  convert h using 1
  funext z
  by_cases hz : z.2.length = 0 <;> simp [slotKind, hz]

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
