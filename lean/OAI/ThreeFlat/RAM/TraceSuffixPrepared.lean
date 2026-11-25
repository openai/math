import OAI.ThreeFlat.RAM.TraceSuffixTail
import OAI.ThreeFlat.Diagonal.TraceBitInput

namespace OAI
/-! # The oracle computes the prepared evaluator's actual public bits -/

namespace ThreeFlat.RAM.TraceSuffixOracle

open Computability.VPVNP.BurstRAM PhysicalPrelude Diagonal.TraceBitHeader
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {w S : ℕ} (I : Image F w)

/-- All addresses concern the initial tick input. -/
structure Locations where
  description : ℕ
  parameters : ℕ
  table : ℕ
  codeBase : ℕ
  textOffset : ℕ
  textSize : ℕ

noncomputable def layout (a : Locations) : Layout :=
  ⟨2*I.endpointBits,I.sizes.rawParams,I.sizes.rawTable,I.sizes.rawCount,w,
    a.description,a.parameters,a.table,a.codeBase,a.textOffset,a.textSize⟩

structure Mounted (a : Locations) (m : ℕ → ℕ) (D : Fin I.advice → Bool) (par : Fin I.parameters → Bool) : Prop where
  description : ∀ j : Fin I.advice, m (a.description+j.val)=(D j).toNat
  parameters : ∀ j : Fin I.parameters, m (a.parameters+j.val)=(par j).toNat
  table : ∀ j : Fin (w*FixedTraceImage.count I.G), m (a.table+j.val)=(FixedTraceImage.parameter I.G I.field I.keys j).toNat

theorem raw_correct (a : Locations) (m : ℕ → ℕ)
    (D : Fin I.advice → Bool) (par : Fin I.parameters → Bool) (x y : Fin I.endpointBits → Bool)
    (loaded : Mounted I a m D par) (t : ℕ) (suffix : 2*I.endpointBits≤t) (hw : 0<w) :
    raw (layout I a) m t=(I.tapeBit D x y par t).toNat := by
  have hP : I.sizes.rawParams=2*I.endpointBits+I.advice := rfl
  have hT : I.sizes.rawTable=I.sizes.rawParams+I.parameters := rfl
  have hC : I.sizes.rawCount=I.sizes.rawTable+w*FixedTraceImage.count I.G := rfl
  simp only [raw,layout,PhysicalPrelude.Image.tapeBit,not_lt.mpr suffix,ite_false]
  by_cases h : t<I.sizes.rawParams
  · let j : Fin I.advice := ⟨t-2*I.endpointBits,by omega⟩
    have hj : 2*I.endpointBits+j.val=t := by dsimp [j]; omega
    have found : PhysicalPinsInput.rawBit D x y t=D j := hj ▸ PhysicalPinsInput.raw_advice D x y j
    simpa only [h,ite_true,found,j] using loaded.description j
  · simp only [h,ite_false]
    by_cases params : t<I.sizes.rawTable
    · have hp : t-I.sizes.rawParams<I.parameters := by omega
      let j : Fin I.parameters := ⟨t-I.sizes.rawParams,hp⟩
      simpa only [params,ite_true,hp,dite_eq_left,j] using loaded.parameters j
    · have hp : ¬t-I.sizes.rawParams<I.parameters := by omega
      simp only [params,ite_false,dite_eq_right hp]
      by_cases table : t<I.sizes.rawCount
      · let j : Fin (w*FixedTraceImage.count I.G) := ⟨t-I.sizes.rawTable,by omega⟩
        simpa only [table,ite_true,FixedTraceImage.parameter,j] using loaded.table j
      · simp only [table,ite_false]
        exact (tail_bit I.G I.field I.keys _ hw (by omega)).symm

theorem header_correct (a : Locations) (m : ℕ → ℕ)
    (D : Fin I.advice → Bool) (par : Fin I.parameters → Bool) (x y : Fin I.endpointBits → Bool)
    (loaded : Mounted I a m D par) (code : Fin a.textSize → Bool)
    (text : ∀ j : Fin a.textSize, m (a.description+a.textOffset+j.val)=(code j).toNat)
    (t : Fin S) (suffix : 2*I.endpointBits≤t.val) (hw : 0<w) :
    read (layout I a) m t.val = (advicePins a.codeBase code (I.tapeBit D x y par) t).toNat := by
  by_cases lo : t.val<a.codeBase
  · have absent : ¬(a.codeBase≤t.val ∧ t.val-a.codeBase<a.textSize) := by omega
    simpa [read,layout,lo,advicePins,absent] using raw_correct I a m D par x y loaded t.val suffix hw
  · by_cases hi : t.val<a.codeBase+a.textSize
    · have inside : a.codeBase≤t.val ∧ t.val-a.codeBase<a.textSize := by omega
      simpa [read,layout,lo,hi,advicePins,inside] using text ⟨t.val-a.codeBase,inside.2⟩
    · have absent : ¬(a.codeBase≤t.val ∧ t.val-a.codeBase<a.textSize) := by omega
      simpa [read,layout,lo,hi,advicePins,absent] using raw_correct I a m D par x y loaded t.val suffix hw


end ThreeFlat.RAM.TraceSuffixOracle

end OAI
