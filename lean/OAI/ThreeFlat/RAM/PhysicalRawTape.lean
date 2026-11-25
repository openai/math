import OAI.ThreeFlat.RAM.PhysicalImageData

namespace OAI
/-! # The bit-per-word tape of an H invocation -/

namespace ThreeFlat.RAM.PhysicalPrelude.Image

open Computability.VPVNP.BurstRAM BitLayout
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {w : ℕ} (I : Image F w)

/-- The finite input consists, in order, of row/column pairs, D, fixed tick
parameters, and the encoded local gate and port words. -/
noncomputable def tapeBit (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (params : Fin I.parameters → Bool) (n : ℕ) : Bool :=
  if n<I.sizes.rawParams then PhysicalPinsInput.rawBit D x y n
  else if h : n-I.sizes.rawParams<I.parameters then params ⟨_,h⟩
  else FixedTraceImage.bits (FixedTraceImage.word I.G I.field I.keys) (n-I.sizes.rawTable)

noncomputable def tape (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (par : Fin I.parameters → Bool) (tail : Memory w) : Memory w := fun n =>
  if n<I.sizes.rawCount then bitWord w (I.tapeBit D x y par n) else tail n

theorem tape_after (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (par : Fin I.parameters → Bool) (tail : Memory w) (n : ℕ) (h : I.sizes.rawCount≤n) :
    I.tape D x y par tail n=tail n := by simp [tape,Nat.not_lt_of_ge h]

theorem tape_raw (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (par : Fin I.parameters → Bool) (tail : Memory w) :
    I.Raw D x y par (I.tape D x y par tail) := by
  have table : I.sizes.rawParams+I.parameters=I.sizes.rawTable := rfl
  have len : I.sizes.rawTable+w*FixedTraceImage.count I.G=I.sizes.rawCount := rfl
  constructor
  · intro i hi
    simp only [tape,ite_eq_left (show i<I.sizes.rawCount by omega),tapeBit,ite_eq_left hi]
  · intro j
    have h := j.isLt
    simp [tape,tapeBit,show I.sizes.rawParams+j.val<I.sizes.rawCount by omega,h]
  · intro j
    have h := j.isLt
    have hr : I.sizes.rawTable+j.val<I.sizes.rawCount := by omega
    have past : ¬I.sizes.rawTable+j.val<I.sizes.rawParams := by omega
    have past' : ¬I.sizes.rawTable+j.val-I.sizes.rawParams<I.parameters := by omega
    simp [tape,tapeBit,hr,past,past',FixedTraceImage.parameter,bitWord]

theorem raw_of_agree (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (par : Fin I.parameters → Bool) (m : Memory w)
    (image : ∀ n, n<I.sizes.rawCount → m n=bitWord w (I.tapeBit D x y par n)) :
    I.Raw D x y par m := by
  have eq : m=I.tape D x y par m := by
    funext n
    by_cases h : n<I.sizes.rawCount
    · simpa [tape,h] using image n h
    · simp [tape,h]
  have ready := I.tape_raw D x y par m
  rw [← eq] at ready
  exact ready

theorem tape_pair (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (par : Fin I.parameters → Bool) (j : Fin I.endpointBits) :
    I.tapeBit D x y par (2*j.val)=x j ∧ I.tapeBit D x y par (2*j.val+1)=y j := by
  have len : I.sizes.rawParams=2*I.endpointBits+I.advice := rfl
  have h := j.isLt
  simp [tapeBit,len,show 2*j.val<2*I.endpointBits+I.advice by omega,
    show 2*j.val+1<2*I.endpointBits+I.advice by omega,PhysicalPinsInput.raw_left,PhysicalPinsInput.raw_right]

end ThreeFlat.RAM.PhysicalPrelude.Image

end OAI
