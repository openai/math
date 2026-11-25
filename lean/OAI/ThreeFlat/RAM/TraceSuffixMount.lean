import OAI.ThreeFlat.RAM.TraceSuffixPrepared
import OAI.ThreeFlat.RAM.TickMountedPins

namespace OAI
/-! # Recovering all suffix operands from the original physical tick pins
The startup-bit and metadata spans may overlap within the public parameter
vector. In particular an H image can read the entire original parameter
vector while its fixed local table occupies a slice of that same vector. -/

namespace ThreeFlat.RAM.TraceSuffixOracle

open Computability.VPVNP.BurstRAM PhysicalPrelude Diagonal.ApproximateImage
open scoped Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {W w nt ns np a : ℕ} (I : Image F w)

private def paramPin (d nt ns a : ℕ) (i : Fin np) :
    Fin (pinCount d nt ns np a) :=
  Fin.natAdd d (Fin.natAdd nt (Fin.natAdd ns (i.castAdd _)))

theorem mounted_tick (D : Fin I.advice → Bool) (team : Fin nt → Bool) (step : Fin ns → Bool)
    (params : Fin np → Bool) (oa na oc nc : Fin a → Bool) (par : Fin I.parameters → Bool)
    (pb tb codeBase textStart textLength : ℕ) (hW : 0<W)
    (hp : pb+I.parameters≤np) (ht : tb+w*FixedTraceImage.count I.G≤np)
    (parBits : ∀ i : Fin I.parameters, params ⟨pb+i.val,by have := i.isLt;omega⟩=par i)
    (tableBits : ∀ i : Fin (w*FixedTraceImage.count I.G),
       params ⟨tb+i.val,by have := i.isLt;omega⟩=FixedTraceImage.parameter I.G I.field I.keys i)
    (mem : Memory W)
    (pins : ∀ j : Fin (pinCount I.advice nt ns np a), mem (2+j.val) =
      BitLayout.bitWord W (fields D team step params oa na oc nc j)) :
    Mounted I ⟨2,2+I.advice+nt+ns+pb,2+I.advice+nt+ns+tb,codeBase,textStart,textLength⟩
      (fun j => (mem j).val) D par := by
  have bit (b : Bool) : (BitLayout.bitWord W b).val=b.toNat := by
    have cap := Nat.one_lt_two_pow hW.ne'
    cases b <;> simp [BitLayout.bitWord,Fin.ofNat, Nat.mod_eq_of_lt (show 1<2^W from cap)]
  have pbit (j : Fin np) : (mem (2+I.advice+nt+ns+j.val)).val=(params j).toNat := by
    let i := paramPin I.advice nt ns a j
    have addr : 2+i.val=2+I.advice+nt+ns+j.val := by
      change 2+(I.advice+(nt+(ns+j.val)))=_
      omega
    rw [← addr,pins i,bit]
    simp [i,paramPin,fields]
  constructor
  · intro j
    let i : Fin (pinCount I.advice nt ns np a) := j.castAdd _
    change (mem (2+i.val)).val=(D j).toNat
    rw [pins,bit]
    simp [i,fields]
  · intro i
    let j : Fin np := ⟨pb+i.val,by have := i.isLt;omega⟩
    change (mem (2+I.advice+nt+ns+pb+i.val)).val=_
    rw [Nat.add_assoc]
    exact (pbit j).trans (congrArg Bool.toNat (parBits i))
  · intro i
    let j : Fin np := ⟨tb+i.val,by have := i.isLt;omega⟩
    change (mem (2+I.advice+nt+ns+tb+i.val)).val=_
    rw [Nat.add_assoc]
    exact (pbit j).trans (congrArg Bool.toNat (tableBits i))


end ThreeFlat.RAM.TraceSuffixOracle

end OAI
