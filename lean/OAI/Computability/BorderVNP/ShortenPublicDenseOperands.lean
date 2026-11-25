import OAI.Computability.BorderVNP.ShortenPublicDenseReceiptTransport
import OAI.Computability.BorderVNP.PackedRoundSource

/-! # The selected numeric source operands on the previous physical child rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDenseReceipt

open Crossing Cover Epoch Packing DirectoryCircuit PublicPopulation StaticRows PublicParallel
open BorderVNP.PackedHistoryCircuit.Normalized VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

/-- Fixed bin code width on the actual congruence level, prior to any choice of
field table, geometric motion or histogram. -/
noncomputable def operandBits (D : ℕ) (B : Type) [Fintype B] (lev : ℕ) : ℕ :=
  Nat.clog 2 (Fintype.card B) + Cover.AddressCircuit.keyWidth (Fintype.card (Cube D)) (lev+1)

/-- The old-only numeric table of the actual selector. The public bin alphabet,
permutation and every live wire position are fixed before evaluating it. -/
structure Operands (Input A : Type) [Fintype Input] (D rows w : ℕ) where
  /-- Physical pins of the intermediate shared table. -/
  Pin : Type
  /-- Enumeration of the intermediate wires in the finite circuit. -/
  finite : Fintype Pin
  /-- Number of bits in each moved seed address. -/
  keyBits : ℕ
  /-- Compiled numeric stage on the old child words, before guessing a profile. -/
  frame : @Frame Input Pin _ finite
  /-- Active bit, moved seed key and full width at every physical cable row. -/
  pop : PublicPopulation.Pins (Fin rows) Pin keyBits w
  /-- Original occupancy, signed direction and both old endpoint pointers. -/
  col : Columns Pin rows D w
  /-- The encoded address of each absolute tile and relative bin. -/
  code : A ↪ Fin (2^keyBits)
  /-- The public permutation that pairs bins across each geometric direction. -/
  perm : Fin D → Equiv.Perm A

attribute [instance] Operands.finite

variable {Input B : Type} [Fintype Input] [Fintype B]
    {D m lev prior copies V rows seeds w : ℕ} [NeZero D] {K : Type*} [Field K]
    {P : Type} {bits : P → ℕ} {child : Fin copies → PlacedPack D P bits K (Cube D) prior}

local notation "A" => (Cube D → Deck (lev+1)) × B

/-- The observed population, width, row occupancy, endpoint pointers and
orientation of exactly the installed stage, with its own fixed seed numbering.
Vacant rows carry the certified padding pointers for the same output directory. -/
def Operands.OnStage (O : Operands Input A D rows w) (e : PaidIdentity K D m) (s : Stage m B lev child)
    (old : (raw child).layout.Site ↪ Fin V) (slot : (raw child).layout.Edge ↪ Fin rows)
    (seed : A ≃ Fin seeds) (x : Input → Bool) : Prop :=
  s.perm = O.perm ∧ ∃ dummy : Fin (edgeCapacity e rows seeds) → SiteShape e (densePack (raw child) slot) A,
    Ready e O.pop O.col O.code seed (raw child) s.bin s.positive old slot dummy (O.frame.eval x)

end Shortening.PublicDenseReceipt

end BorderVNP
end Computability
end OAI
