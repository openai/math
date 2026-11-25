import OAI.ThreeFlat.RAM.PhysicalGuardRoute
import OAI.ThreeFlat.RAM.PhysicalPinsFit
import OAI.ThreeFlat.RAM.GuardedDescriptorRecord

namespace OAI
/-! # Native source lookups for the generated approximating network -/

namespace ThreeFlat.RAM.PhysicalPinsExpr

open scoped Fin.CommRing

open Diagonal Diagonal.BoundaryWire BitLayout Computability.VPVNP.BurstRAM

variable {w b : ℕ}

def coords {α : Type*} (first second : α) : Fin 2 → α := ![first,second]

private theorem cast_coords {x y : ℕ} :
    (fun i => (coords (α:=ℕ) x y i : Word w)) = coords (x : Word w) (y : Word w) := by
  funext i
  fin_cases i <;> rfl

def pair (f : Formula 2) (s : Shape) (mem : Memory w) (first second : Word w) : Word w :=
  f.value (fun i => (s.words i : Word w)) mem (coords first second)

def readers (s : Shape) (mem : Memory w) : GuardedDescriptor.Readers w where
  copy := fun _ i j => pair (copyFormula (.reg 1) (.reg 0)) s mem j i
  pin := fun i j => pair (pinFormula (.reg 1) (.reg 0)) s mem j i
  left := fun i j => pair (guardFormula false (.reg 1) (.reg 0)) s mem j i
  right := fun i j => pair (guardFormula true (.reg 1) (.reg 0)) s mem j i

variable (s : Shape) [NeZero s.period] (mem : Memory w)
variable (params : Fin s.parameterBits → Bool)

def Shape.input (i : Fin (s.last+1)) (j : Fin (s.area+2*s.halfBits)) :
    Source s.chunks s.bits s.last s.inside s.advice :=
  ApproximateNetwork.input (fun i => ApproximateImage.select i.val params)
    (fun i => s.slots i.val) s.choice i j

omit [NeZero s.period] in
private theorem pair_nat (f : Formula 2) (cert : Small f) (margin : 5*b+128≤w)
    (hf : ∀ p,s.words p<2^b) (x y : ℕ) (hx : x<2^b) (hy : y<2^b) :
    pair f s mem (x : Word w) (y : Word w) =
      (nat (w:=w) s (fun i => (mem i).val) (coords x y) f : Word w) := by
  have hv (i : Fin 2) : coords x y i<2^b := by fin_cases i <;> first | exact hx | exact hy
  have hmem : (fun i => ((mem i).val : Word w))=mem := by funext i; exact Fin.cast_val_eq_self _
  have h := f.value_eq_natural s.words (fun i => (mem i).val) (coords x y)
    (cert.fits _ _ _ margin hf (fun i => (mem i).isLt) hv)
  simpa only [pair,nat,hmem,cast_coords] using h

variable {F : Type*} [CommSemiring F]

omit [CommSemiring F] in
/-- Sizes and the two stored source slices determine every emitted word.
The active destination cells are absent from these hypotheses. -/
theorem reads (N : BitNetwork F (s.area+2*s.halfBits)) (code : FieldCode F w)
    (margin : 5*b+128≤w) (shapeFit : ∀ p,s.words p<2^b)
    (rowsFit : N.cells≤2^b) (pinsFit : s.area+2*s.halfBits≤2^b)
    (blockFit : s.last+1≤2^b) (ticksFit : (s.last+1)*(s.inside+1)≤2^w)
    (teamFit : s.teams≤2^w)
    (readParams : ∀ j : Fin s.parameterBits, (mem (s.parameterBase+j.val)).val=(params j).toNat)
    (readRows : ∀ i j,mem (s.templateBase+11*(i:Fin N.cells).val+(j:Fin 11).val)=record N code i j)
    (eleven : 11≤2^b) :
    GuardedDescriptor.Reads (readers s mem) N (s.input params)
      (s.guardSource false) (s.guardSource true) code := by
  have guard (side : Bool) (i : Fin (s.last+1)) (j : Fin s.halfBits) :
      pair (guardFormula side (.reg 1) (.reg 0)) s mem (j.val : Word w) (i.val : Word w) =
      (sourceAddress (s.guardSource side i j) : Word w) := by
    have hj : j.val<2^b := by have := j.isLt; omega
    rw [pair_nat s mem _ (small_guard side 1 0) margin shapeFit _ _ hj (i.isLt.trans_le blockFit),
      nat_guard, s.guard_addr side i j]
    rfl
  refine ⟨?_,?_,guard false,guard true⟩
  · intro i k j
    change pair _ s mem _ _ = _
    rw [pair_nat s mem _ (small_copy 1 0) margin shapeFit _ _ (j.isLt.trans_le eleven)
      (k.isLt.trans_le rowsFit),nat_copy]
    change ((mem (s.templateBase+11*k.val+j.val)).val : Word w)=_
    rw [Fin.cast_val_eq_self,readRows]
  · intro i j
    change pair _ s mem _ _ = _
    rw [pair_nat s mem _ (small_pin 1 0) margin shapeFit _ _ (j.isLt.trans_le pinsFit)
      (i.isLt.trans_le blockFit),nat_pin]
    change (s.decode w _ i.val j.val : Word w)=(sourceAddress (s.input params i j) : Word w)
    apply congrArg (fun x : ℕ => (x : Word w))
    exact (s.decode_port w _ params readParams i teamFit ticksFit j).trans
      (ApproximateAddress.input_addr (fun k => ApproximateImage.select k.val params)
        (fun k => s.slots k.val) s.choice i j).symm

end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
