import OAI.Computability.BorderVNP.PackedFrozenHookTape

/-! # Physical image of the frozen hook schema on the actual dense saved run -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.HookTape

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedProfile InheritedHook FrozenTape BankSite BankJoint BankPacket CellSparse DirectoryCircuit
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open scoped Classical

variable {D m old binBits w : ℕ} [NeZero D] {S : Type} [Fintype S] {σ : Type*} [Fintype σ]
variable (pop : PublicPopulation.Pins (Fin old) σ binBits w) (binCode : S ↪ Fin (2^binBits))
variable (perm : Fin D → Equiv.Perm S)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))

variable {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {n sites np C d h : ℕ} (seed : S ↪ Fin n)
variable (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))
variable (occupied : Fin (edgeCapacity e old n) → σ)
variable {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (slot : p.layout.Edge ↪ Fin old)
variable (bin : p.layout.Edge → Option S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool)

private noncomputable abbrev dense := densePack p slot
private noncomputable abbrev which := CutCircuit.denseBin p.layout slot bin
private noncomputable abbrev priorID := CutCircuit.denseRows p.layout slot
private noncomputable abbrev orient := positive ∘ (Names.denseSlot p.layout slot).symm
variable (q : Counts e (dense p slot) (which p slot bin) perm)
private noncomputable abbrev G := (output e (dense p slot) (which p slot bin) perm (orient p slot positive) first q).layout
variable (oldSite : (dense p slot).layout.Site ↪ Fin sites) (portID : P ↪ Fin np)
variable (cell : (G perm e p slot bin positive first q).Site → Fin C)
variable (aux : (G perm e p slot bin positive first q).Site → ℕ)

local notation3 "p₀" => dense p slot
local notation3 "b₀" => which p slot bin
local notation3 "old₀" => priorID p slot
local notation3 "or₀" => orient p slot positive
local notation3 "G₀" => G perm e p slot bin positive first q
local notation3 "sID" => siteRows e p₀ oldSite seed
local notation3 "eID" => outputRows e p₀ b₀ perm or₀ first q old₀ seed

/-- On every actually represented old saved pack, the source order is the real
sparse cable order and the cut operands are supplied by the shared live cut pass.
The immutable hook schema recovers the complete tagged terminal block. -/
theorem saved_at_terminal (hc : ComputesCuts (m := m) pop binCode perm cut) (x : σ → Bool)
    (hpop : PublicPopulation.Represents pop p.layout bin slot binCode x) (htotal : ∀ a,count p.layout bin a < 2^w)
    (hwidth : ∀ z,value (x ∘ pop.width (slot z)) = p.layout.width z)
    (rep : Represents G₀ cell aux sID eID portID F x) (room : ∀ v,incoming G₀ v < 2^w)
    (mask : ∀ k,x (occupied k) = true ↔ k ∈ Set.range eID)
    (a : S) (t : Fin D × Bool) (hone : 1 < 2^w)
    (hcount : value (fun k => counts.eval x (a,none,k)) = blocks (p₀).layout b₀ perm m a)
    (fit : ∀ z : {z : (p₀).layout.Edge // b₀ z = some (perm t.1 a)},
      Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*blocks (p₀).layout b₀ perm m a +
        incoming G₀ ((G₀).dst (seedHook e p₀ b₀ perm a t.1 z (decide (or₀ z.val = t.2)))) +
        count (p₀).layout b₀ (perm t.1 a) < 2^w) :
    (schema old D w).atSite ((asTape (native e seed F counts cut occupied)).eval x)
      (F.sites (sID (seedSite e p₀ b₀ perm or₀ first q a (.inr (.inl t))))).val =
      (InheritedProfile.hookRows e p₀ b₀ perm or₀ first q a sID eID portID (fun a => (binCode a).val) t).map marked :=
  at_terminal e seed F counts cut occupied p₀ b₀ perm or₀ first q oldSite old₀ portID cell aux rep mask room
    (fun a => (binCode a).val) a t (eligible_sparse_order p bin perm slot a t.1) hone hcount
    (fun z col => saved_cut pop binCode perm cut p slot bin hc x hpop htotal hwidth _ z _ col) fit

end Packing.Inherited.HookTape

end BorderVNP
end Computability
end OAI
