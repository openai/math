import OAI.Hierarchy.GridSelector
import OAI.Hierarchy.GridReceiverHeader

namespace OAI
/-! # The exact shared-wire offset in the receiving machine's public tape -/
namespace Hierarchy.TraceReceiverWireBits
open ThreeFlat.Diagonal.HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing

variable {F : Type*} [CommSemiring F] {S : Shape} (P : Plan F S) (C : P.Codes)
    (bits : P.History → ℕ) (cap : ℕ)

/-- In every accepted simulation selector the wire string immediately follows
the branch word and the exact canonical record. -/
theorem selector (room : GridSelector.Room P C bits cap) (sel : Fin (cap+1) → Bool)
    (z : GridSelector.Trace P bits) (ok : GridSelector.decode P C bits cap sel=some (some z))
    (n : ℕ) (fixed : (P.write C z.1).length=n) (j : Fin (bits z.1)) :
    ∃ i : Fin (cap+1), i.val=1+n+j.val ∧ sel i=z.2 j := by
  let hist := P.write C z.1
  have hj := j.isLt
  have bound := room z.1
  let i : Fin cap := ⟨hist.length+j.val,by dsimp [hist];omega⟩
  refine ⟨i.succ,by dsimp [i,hist];omega,?_⟩
  rw [←GridSelector.encode_decode P C bits cap room sel (some z) ok]
  change (GridSelector.body P C bits cap z).get _=_
  rw [List.get_eq_getElem]
  change (hist ++ List.ofFn z.2 ++ _)[hist.length+j.val]'(by simp only [List.length_append,List.length_ofFn]; omega)=_
  rw [List.getElem_append_left (by simp)]
  rw [List.getElem_append_right (Nat.le_add_right ..)]
  simp

/-- Read the bit from the actual header that precedes the receiving tick's
assigned factor data. All lengths in the address are public. -/
theorem mounted {w k : ℕ} (text : ℕ) (textRoom : text ≤ w^2) (self : Fin (w^2) → Bool)
    (index : Word (64*w)) (params : Fin k → Word (64*w)) (sel : Fin (cap+1) → Bool)
    (input : ℕ → Bool) (room : GridSelector.Room P C bits cap)
    (z : GridSelector.Trace P bits) (ok : GridSelector.decode P C bits cap sel=some (some z))
    (n : ℕ) (fixed : (P.write C z.1).length=n)
    (stored : let head:=GridReceiverHeader.header text textRoom self index params sel
      ∀ i : Fin head.length,input i.val=head[i.val])
    (j : Fin (bits z.1)) :
    input (text+((k+1)*(64*w)+GridReceiverHeader.count w*(64*w))+1+n+j.val)=z.2 j := by
  obtain ⟨i,place,read⟩ := selector P C bits cap room sel z ok n fixed j
  let first := text+((k+1)*(64*w)+GridReceiverHeader.count w*(64*w))
  have lookup := GridReceiverHeader.selector_at text textRoom self index params sel i
  have inside : first+i.val < (GridReceiverHeader.header text textRoom self index params sel).length := by
    rw [GridReceiverHeader.length]
    dsimp [first]
    have := i.isLt
    omega
  have val := (stored ⟨first+i.val,inside⟩).trans (lookup.trans read)
  simpa only [first,place,Nat.add_assoc] using val

end Hierarchy.TraceReceiverWireBits

end OAI
