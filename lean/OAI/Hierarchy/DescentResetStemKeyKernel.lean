import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # The fixed short-key gate on a signed chip and the physical peer words -/
namespace Hierarchy.DescentResetStemKey
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {D field : ℕ}

/-- The first two cells are the local shape and signed chip. The remaining D cells
are the tagged physical peer words at the same low slot. -/
def fields {α : Type} (own signed : α) (peers : Fin D→α) : Fin (D+2)→α :=
  Fin.cases own (Fin.cases signed peers)

abbrev Decoder (D field : ℕ) := Cell field → Option (Fin D × Bool)

def remote (parse : Decoder D field) (side : Bool) (x : Fin (D+2)→Cell field) : Option ℕ := do
  let chip ← parse (x (0 : Fin (D+1)).succ)
  if chip.2=side then
    let ptr := (x chip.1.succ.succ).val
    if 0< ptr then some (ptr-1) else none
  else none

def ticket (parse : Decoder D field) (side : Bool) (x : Fin (D+2)→Cell field) : Option (ℕ×Bool) :=
  (remote parse side x).map (fun far=>((x 0).val/2,decide ((x 0).val%2=0 ∧ far%2=0)))

def code (key : Option (ℕ×Bool)) : ℕ := key.elim 0 (fun k=>1+2*k.1+k.2.toNat)

def word (parse : Decoder D field) (side : Bool) (x : Fin (D+2)→Cell field) : Cell (field+2) :=
  (code (ticket parse side x):ℕ)

theorem word_val (parse : Decoder D field) (side : Bool) (x : Fin (D+2)→Cell field) :
    (word parse side x).val=code (ticket parse side x) := by
  apply Fin.val_cast_of_lt
  cases far : remote parse side x with
  | none => simp [code,ticket,far]
  | some t =>
    have size := (x 0).isLt
    have pos := Nat.two_pow_pos field
    simp only [ticket,far,Option.map_some,code,Option.elim_some,pow_add]
    cases decide ((x 0).val%2=0 ∧ t%2=0) <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem word_zero (parse : Decoder D field) (dead : parse 0=none) (s : Bool) :
    word parse s (fun _=>0)=0 := by simp [word,code,ticket,remote,dead]

end
end Hierarchy.DescentResetStemKey

end OAI
