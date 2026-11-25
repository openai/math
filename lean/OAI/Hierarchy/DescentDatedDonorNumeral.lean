import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! # The mixed-radix code of a donor rank and old block -/
namespace Hierarchy.DescentOrdinaryDonorHalo.Digit
open DescentSIMDLookup DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section

/-- A positive local rank token has already been reversed and compacted at the
receiver. Combine it with the old block of the *source* of the raw wire. -/
def numeral (P k out : ℕ) (block : Fin (2^k)) (r : Cell (Packed.bits P)) : Cell out :=
  (Packed.readToken P r).elim 0 (fun i=>((i.val*2^k+block.val : ℕ):Cell out))

@[simp] theorem numeral_hole (P k out : ℕ) (block : Fin (2^k)) : numeral P k out block 0=0 := by
  simp [numeral,Packed.readToken]

theorem numeral_rank (P k out : ℕ) (block : Fin (2^k)) (rank : Fin P) :
    numeral P k out block (Packed.token (some rank))=((rank.val*2^k+block.val : ℕ):Cell out) := by
  simp [numeral,Packed.token_back]

end
end Hierarchy.DescentOrdinaryDonorHalo.Digit

end OAI
