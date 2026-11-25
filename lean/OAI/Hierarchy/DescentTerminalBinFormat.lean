import OAI.Hierarchy.DescentTerminalBinReaddress
import Mathlib.Data.Nat.Log

namespace OAI
/-! # A short decodable pointer table for each terminal bin -/

namespace Hierarchy.DescentTerminalBinFormat
open Computability.VPVNP.RAMSerialization DescentTerminalBinReaddress

def pointerBits (W q : ℕ) := Nat.clog 2 (W*q)
def controlBits (W q : ℕ) := W*q*(pointerBits W q+1)

private theorem pointerRoom (W q : ℕ) : W*q ≤ 2^(pointerBits W q) :=
  Nat.le_pow_clog (by decide) _

private def sourceAt (W q n : ℕ) : Option (Slot W q) :=
  if h:n<W*q then some (finProdFinEquiv.symm ⟨n,h⟩) else none

private theorem sourceAt_slot {W q:ℕ} (s:Slot W q) :
    sourceAt W q (finProdFinEquiv s).val=some s := by
  unfold sourceAt
  rw [dite_eq_left (finProdFinEquiv s).isLt]
  exact congrArg some (finProdFinEquiv.symm_apply_apply s)

/-- Each target has a defined flag and a little-endian source-slot index.
Out-of-range source ordinals decode to the empty route as well. -/
def address (W q : ℕ) : Address (controlBits W q) W q := fun code dst =>
  let field (j : Fin (pointerBits W q+1)) :=
    wordBits _ code (finProdFinEquiv (finProdFinEquiv dst,j))
  if field (Fin.last (pointerBits W q)) then
    let src := (wordBits (pointerBits W q)).symm (fun j => field j.castSucc)
    sourceAt W q src.val
  else none

def encode {W q : ℕ} (routes : Slot W q→Option (Slot W q)) : Tagged.Row (controlBits W q) :=
  (wordBits _).symm fun z =>
    let p : Fin (W*q) × Fin (pointerBits W q+1) := finProdFinEquiv.symm z
    match routes (finProdFinEquiv.symm p.1) with
    | none => false
    | some src => Fin.lastCases true
        (wordBits _ ((finProdFinEquiv src).castLE (pointerRoom W q))) p.2

theorem address_encode {W q : ℕ} (routes : Slot W q→Option (Slot W q)) (dst : Slot W q) :
    address W q (encode routes) dst=routes dst := by
  have digit (j:Fin (pointerBits W q+1)) :
      wordBits _ (encode routes) (finProdFinEquiv (finProdFinEquiv dst,j))=
        match routes dst with
        | none=>false
        | some src=>Fin.lastCases true (wordBits _ ((finProdFinEquiv src).castLE (pointerRoom W q))) j := by
    simp only [encode,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  cases h:routes dst with
  | none=>simp only [address,digit,h,ite_false,Bool.false_eq_true]
  | some src=>
    let u:=(finProdFinEquiv src).castLE (pointerRoom W q)
    have decode:(wordBits (pointerBits W q)).symm (fun j=>(wordBits (pointerBits W q)) u j)=u :=
      (wordBits (pointerBits W q)).symm_apply_apply u
    simp only [address,digit,h,Fin.lastCases_last,Fin.lastCases_castSucc,ite_true]
    exact (congrArg (fun code=>sourceAt W q code.val) decode).trans (sourceAt_slot src)

theorem read_encoded {bits W q piece : ℕ} (room : sliceWidth W q piece ≤ bits)
    (routes : Slot W q→Option (Slot W q)) (x : Payload W q piece)
    (dst : Slot W q) (j : Fin (W*piece)) :
    read room (fun u => entry bits piece (address W q) (encode routes) (gather x u)) dst j =
      (routes dst).elim false (fun src => x src j) := by
  rw [reassembled,address_encode]

theorem format_charge (W q : ℕ) : controlBits W q=W*q*(Nat.clog 2 (W*q)+1) := rfl

theorem rom_fits {bits W q piece : ℕ}
    (fit : W*q*(Nat.clog 2 (W*q)+1)+q*(W*piece) ≤ bits/2) :
    2^(controlBits W q)*2^(sliceWidth W q piece) ≤ 2^(bits/2) :=
  shared_words (c:=controlBits W q) fit

end Hierarchy.DescentTerminalBinFormat

end OAI
