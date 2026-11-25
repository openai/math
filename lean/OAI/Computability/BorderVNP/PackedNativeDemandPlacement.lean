import OAI.Computability.BorderVNP.PackedNativeDemandRows

/-! # Reference bank of a sewn history's delivered words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Directory Directory.PrivateBank
open scoped Classical

variable {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    (width : ∀ j, bits (live j) = dir.block)

local notation3 (prettyPrint := false) "pp" => privatePair N cell edges ports dir old live gap
local notation3 (prettyPrint := false) "lp" => livePair N cell edges ports dir old live gap
local notation3 (prettyPrint := false) "owner" => Sum.elim
  (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin C → Fin C)) (cell ∘ old)
local notation3 (prettyPrint := false) "index" => numbered (reserveID (C:=C) (suppliedID N cell edges ports))
local notation3 (prettyPrint := false) "size" => Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin C => gap))
  (fun _ : Fin dir.entries => dir.description)

/-- Place the original description and live inputs of the fixed network in
their typed native slots before any profile or writer execution. -/
noncomputable def referenceBank : Directory.BankPlacement dir pp lp _ owner index size where
  key := { toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl (suppliedPort N cell (live j))))
           inj' := by
             rintro (a|j) (b|k) h
             · exact congrArg Sum.inl (Sum.inr.inj h)
             · cases h
             · cases h
             · exact congrArg Sum.inr (live.injective ((suppliedPort N cell).injective (Sum.inl.inj (Sum.inl.inj h)))) }
  width_eq := by rintro (j|j); exacts [rfl,width j]
  entry := keyPair N cell edges ports dir old live gap

/-- The reference-bank keys are exactly the original metadata ordinal and
the actual supplied-port ordinal used by the native writer. -/
theorem referenceBank_key (j : dir.DestinationKey) :
    (referenceBank N cell edges ports dir old live gap width).key j =
      j.elim Sum.inr (fun z => Sum.inl (Sum.inl (suppliedPort N cell (live z)))) := rfl

/-- Every returned native private placement on this history has the same
physical word key as the reference bank, including at every live input. -/
theorem networkPlacement_key_reference {s d k b w : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ)
    (ids : N.Site ↪ Fin s) (F : Fields s ne np C d k b σ) (x : σ → Bool)
    (net : Represents N cell aux ids edges ports F x) (code : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (head origin : ℕ) (before after : ℕ → ℕ)
    (pub : Image F (ids ∘ old) (ports ∘ live ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout head origin ne C dir.entries dir.description gap).Image before dir.entries after)
    (room : (privateLayout head origin ne C dir.entries dir.description gap).Fits w before) (j : dir.DestinationKey) :
    (pub.networkPlacement N cell aux ids edges ports F net code fit dir old live width head origin gap
      before after run room).key j = (referenceBank N cell edges ports dir old live gap width).key j := by
  cases j <;> rfl

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
