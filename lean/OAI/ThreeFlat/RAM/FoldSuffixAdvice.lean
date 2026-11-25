import OAI.ThreeFlat.RAM.SelfAdvice

namespace OAI
/-! # A reserved slice of self advice for the folded X header suffix -/

namespace ThreeFlat.RAM.SelfAdvice

open Computability.VPVNP.BurstRAM PrivateRAM
variable {w p r k p' r' k' g q : ℕ}

/-- Replace exactly the reserved extra bits. The padding before the reservation
allows the offset to be fixed before the native H instruction table is chosen. -/
def withSuffix (start len : ℕ) (extra : Fin g → Bool) (suffix : ℕ → Bool) (i : Fin g) : Bool :=
  if start≤i.val ∧ i.val<start+len then suffix (i.val-start) else extra i

variable (tick : Machine w p r k) (H : Machine w p' r' k')
    (extra : Fin g → Bool) (suffix : ℕ → Bool) (offset len : ℕ)

/-- The prepared matrix theorem can use this slice for every pair of endpoint strings. -/
theorem description_withSuffix (room : Fits w p k p' k' g q)
    (after : textSize w p k+textSize w p' k' ≤ offset)
    (capacity : offset+len ≤ textSize w p k+textSize w p' k'+g) :
    let start := offset-(textSize w p k+textSize w p' k')
    let D := description (q:=q) tick H (withSuffix start len extra suffix)
    offset+len ≤ q ∧ ∀ (n : ℕ) (h : n<len), D ⟨offset+n,by have := room.room; omega⟩=suffix n := by
  intro start D
  have size := room.room
  refine ⟨by omega,?_⟩
  intro n hn
  let i : Fin g := ⟨start+n,by dsimp only [start]; omega⟩
  have eqn : offset+n = textSize w p k+textSize w p' k'+i.val := by dsimp only [start,i]; omega
  have h := extra_bits tick H (withSuffix start len extra suffix) room i
  change D _ = _ at h
  have pos : (⟨offset+n,by omega⟩ : Fin q) = ⟨textSize w p k+textSize w p' k'+i.val,by omega⟩ := Fin.ext eqn
  rw [pos,h]
  simp [withSuffix,i,hn]


end ThreeFlat.RAM.SelfAdvice

end OAI
