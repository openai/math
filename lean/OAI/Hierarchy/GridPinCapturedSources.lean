import OAI.Hierarchy.GridSelfHeader
import OAI.Hierarchy.GridPinHeaderImage
import OAI.Hierarchy.FactorPinIntervals

namespace OAI
/-! # Original literal bits and selector header at the evaluator's actual input -/

namespace Hierarchy.GridPinCapturedSources
open ThreeFlat RAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {w k f e compact n ell tp tr tk ep er ek S : ℕ}
variable (X : Catalyst.Approximation F k f) (enc : FieldCode F (64*w))
variable (params : Fin n→Word (64*w)) (recv : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
variable (x : Fin (e*2)→Bool)

/-- Only original public bits occupy the literal bank. Both original external
slots and all addresses strictly beyond the input have literal value zero. -/
noncomputable def advice (j : Fin S) : Bool :=
  if e*2≤j.val ∧ j.val<GridSelfHeader.rawSize w e compact n then
    GridSelfHeader.rawTape (B:=compact) X enc params recv eval (fun _ : Fin (e*2)=>false) j.val
  else false

theorem true_bit (j : ℕ) (outside : e*2≤j) :
    GridSelfHeader.rawTape (B:=compact) X enc params recv eval x j=
      GridSelfHeader.rawTape (B:=compact) X enc params recv eval (fun _ : Fin (e*2)=>false) j := by
  simp [GridSelfHeader.rawTape,GridDescription.input,show ¬j<e*2 by omega]

theorem captured_advice {start : ℕ} (sel : Fin ell→Bool) (sep : GridSelfHeader.rawSize w e compact n≤ start)
    (j : Fin S) (lo : e*2≤j.val) (hi : j.val<GridSelfHeader.rawSize w e compact n) :
    GridSelfHeader.captured (B:=compact) X enc params recv eval x start sel j.val =
      ((advice (e:=e) (compact:=compact) X enc params recv eval j).toNat : Word (64*w)) := by
  have h := GridSelfHeader.input_at X enc params recv eval x sep sel ⟨j.val,hi⟩
  change _=((advice (e:=e) (compact:=compact) X enc params recv eval j).toNat:Word (64*w))
  rw [advice,ite_eq_left ⟨lo,hi⟩,←true_bit X enc params recv eval x j.val lo]
  exact h

theorem unscattered (j : Fin S) (off : j.val<e*2 ∨ GridSelfHeader.rawSize w e compact n≤j.val) :
    advice (e:=e) (compact:=compact) X enc params recv eval j=false := by
  simp [advice,show ¬(e*2≤j.val ∧ j.val<GridSelfHeader.rawSize w e compact n) by omega]

/-- Authentic header source and captured input after upstream immutable-bank
framing has been applied. This reads the exact memory observed by the native
header fill without encoding the source or selector in the instruction text. -/
theorem framed_header {start literal pins text : ℕ} (sel : Fin ell→Bool)
    (sep : GridSelfHeader.rawSize w e compact n≤ start) (fit : text≤w^2)
    (pos : 0<w) (t p : ℕ) (tfit : t<2^(64*w)) (pfit : p<pins)
    (o : Memory (64*w))
    (frame : ∀ a,GridPinHeaderNative.source
      (GridPinHeaderNative.captureBanks w e compact n ell start literal pins text) a →
      o a=GridSelfHeader.captured (B:=compact) X enc params recv eval x start sel a) :
    let bank := GridPinHeaderNative.captureBanks w e compact n ell start literal pins text
    let raw := GridDescription.code (q:=w^2) recv eval
    GridPinHeaderNative.initialWord (64*w) bank (fun a=>(o a).val) (literal+(p+pins*t)) =
      ((GridReceiverHeader.header text fit raw (t:Word (64*w)) params sel)[p]?.getD false).toNat := by
  intro bank raw
  exact (GridPinHeaderNative.initialWord_congr (64*w) bank _ _ _
    (fun a valid=>congrArg Fin.val (frame a valid))).trans
    (GridPinHeaderNative.captured_header X enc params recv eval x sel sep fit pos t p tfit pfit)

end Hierarchy.GridPinCapturedSources

end OAI
