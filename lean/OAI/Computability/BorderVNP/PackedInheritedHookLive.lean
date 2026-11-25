import OAI.Computability.BorderVNP.PackedInheritedHookPhysical
import OAI.Computability.BorderVNP.PackedOldDirectory

/-! # Immutable terminal hook compilation on the actual saved dense pack

The shared public cut frame is fixed before its incoming layout is known.
Its span and ordinal words are those of the stored cable after reindexing
the physical layout by stable sparse cable number. These are precisely the
intervals used by the combining step and its terminal-site verifier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedHook

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedProfile BankSite BankJoint BankPacket CellSparse DirectoryCircuit
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open scoped Classical

variable {D m old binBits w : ℕ} [NeZero D] {S : Type} [Fintype S] {σ : Type*} [Fintype σ]
variable (pop : PublicPopulation.Pins (Fin old) σ binBits w) (binCode : S ↪ Fin (2^binBits))
variable (perm : Fin D → Equiv.Perm S)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))

/-- The actual allocator's three public fields on every represented old input. -/
def ComputesCuts : Prop :=
  ∀ {P : Type} {bits : P → ℕ} (N : Network D P bits) (bin : N.Edge → Option S) (slot : N.Edge ↪ Fin old)
    (x : σ → Bool), PublicPopulation.Represents pop N bin slot binCode x →
      (∀ a, count N bin a < 2^w) → (∀ z, value (x ∘ pop.width (slot z)) = N.width z) →
      ∀ z b field, value (fun j => cut.eval x ((slot z,b),field,j)) =
        field.read (CutCircuit.liveDescriptor N slot bin perm m (fun a => (binCode a).val) z b)

/-- Existence and true gate budget of the one shared population, pool, and clipping pass.
The saved layout, charges, and all future profile branches follow this choice. -/
theorem exists_shared_cut (D m : ℕ) [NeZero D] (hm : 0 < m) :
    ∃ C exp : ℕ, ∀ (old binBits w : ℕ) {S : Type} {σ : Type*} [Fintype S] [Fintype σ]
      (pop : PublicPopulation.Pins (Fin old) σ binBits w) (binCode : S ↪ Fin (2^binBits))
      (perm : Fin D → Equiv.Perm S), ∃ cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w),
        cut.size ≤ (PublicPopulation.offsets pop).size +
          PoolCircuit.scatterCost (Fintype.card S) old D C exp binBits w +
          old*Fintype.card (Band D)*(48*w) + 1 + old*Fintype.card (Band D)*(3300*(w+1)^2) ∧
        ComputesCuts (m := m) pop binCode perm cut :=
  CutCircuit.live_cut_frames D m hm

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

/-- The chosen old live cable in the physically reordered bin, preserving its true slot. -/
noncomputable def savedCable (a : S) (i : Fin D) (z : {z : p.layout.Edge // bin z = some (perm i a)}) :
    {u : (p₀).layout.Edge // b₀ u = some (perm i a)} :=
  ⟨Names.denseSlot p.layout slot z.val,by simpa [which,CutCircuit.denseBin] using z.property⟩

/-- Exact nine-word physical output and owner of every eligible saved hook, using the
actual live population/interval frame and both directions of the original cable. -/
theorem native_saved (hc : ComputesCuts (m := m) pop binCode perm cut) (x : σ → Bool)
    (hpop : PublicPopulation.Represents pop p.layout bin slot binCode x) (htotal : ∀ a,count p.layout bin a < 2^w)
    (hwidth : ∀ z,value (x ∘ pop.width (slot z)) = p.layout.width z)
    (rep : Represents G₀ cell aux sID eID portID F x) (room : ∀ v,incoming G₀ v < 2^w)
    (a : S) (i : Fin D) (z : {z : p.layout.Edge // bin z = some (perm i a)}) (src : Bool) (hone : 1 < 2^w) :
    let z' := savedCable perm p slot bin a i z
    let edge := seedHook e p₀ b₀ perm a i z' src
    let j := blocks (p₀).layout b₀ perm m a
    let r : Row old D := (slot z.val,i,src)
    value (fun k => counts.eval x (a,none,k)) = j →
      Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*j +
        incoming G₀ ((G₀).dst edge) + count (p₀).layout b₀ (perm i a) < 2^w →
      value (fun k => (native e seed F counts cut occupied).eval x (r,.inr (.inl k))) = (F.sites (sID ((G₀).dst edge))).val ∧
        ∀ j : Fin 9, value (fun k => (native e seed F counts cut occupied).eval x (r,.inr (.inr (j,k)))) =
          (Packet.record (terminalHook e p₀ b₀ perm or₀ first q a id (workAt e p₀ b₀ perm or₀ first q)
            sID eID portID (fun a => (binCode a).val) i z' src))[j.val]?.getD 0 := by
  intro z' edge j r hcount fit
  have hslot : old₀ z'.val = slot z.val := by
    change slot ((Names.denseSlot p.layout slot).symm ((Names.denseSlot p.layout slot) z.val)) = _
    rw [Equiv.symm_apply_apply]
  have hf (col : CutCircuit.Result) : value (fun j => cut.eval x ((old₀ z'.val,some (i,true)),col,j)) =
      col.read (descriptor (p₀).layout b₀ perm m (fun a => (binCode a).val) z' (some (i,true))) := by
    rw [hslot]
    exact (hc p.layout bin slot x hpop htotal hwidth z.val (some (i,true)) col).trans
      (congrArg col.read (CutCircuit.live_charged p.layout slot bin perm m (fun a => (binCode a).val)
        z.val (perm i a) z.property (some (i,true))))
  have hz := native_live e seed F counts cut occupied p₀ b₀ perm or₀ first q oldSite old₀ portID cell aux rep room
    (fun a => (binCode a).val) a i z' src hcount hf hone fit
  have hr : (old₀ z'.val,i,src) = r := Prod.ext hslot rfl
  exact hr ▸ hz

end Packing.InheritedHook

end BorderVNP
end Computability
end OAI
