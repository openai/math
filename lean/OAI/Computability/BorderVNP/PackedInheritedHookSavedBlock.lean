import OAI.Computability.BorderVNP.PackedInheritedProfileEmit

/-! # Complete immutable terminal packet on the genuine shared population pass

The frame is chosen before the old saved layout is known. For any represented
layout, all of its active words at a terminal are precisely the fixed profile
prefix followed by the nine-word rows in the physical sparse cable order.
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

omit [Fintype S] [Field K] [Fintype P] in
/-- All three actual cut words for every charged saved cable come from the one
public population, pool, and clipping frame on the prior sparse records. -/
theorem saved_cut (hc : ComputesCuts (m := m) pop binCode perm cut) (x : σ → Bool)
    (hpop : PublicPopulation.Represents pop p.layout bin slot binCode x) (htotal : ∀ a,count p.layout bin a < 2^w)
    (hwidth : ∀ z,value (x ∘ pop.width (slot z)) = p.layout.width z) (a : S)
    (z : {u : (p₀).layout.Edge // b₀ u = some a}) (b : Band D) (col : CutCircuit.Result) :
    value (fun k => cut.eval x ((old₀ z.val,b),col,k)) =
      col.read (descriptor (p₀).layout b₀ perm m (fun a => (binCode a).val) z b) := by
  let u := (Names.denseSlot p.layout slot).symm z.val
  have hu : bin u = some a := z.property
  have hr := CutCircuit.live_charged p.layout slot bin perm m (fun a => (binCode a).val) u a hu b
  let z' : {z : (p₀).layout.Edge // b₀ z = some a} := ⟨(Names.denseSlot p.layout slot) u,by
    change bin ((Names.denseSlot p.layout slot).symm ((Names.denseSlot p.layout slot) u)) = _
    rw [Equiv.symm_apply_apply]; exact hu⟩
  have hz : z' = z := Subtype.ext ((Names.denseSlot p.layout slot).apply_symm_apply z.val)
  have h : CutCircuit.liveDescriptor p.layout slot bin perm m (fun a => (binCode a).val) u b =
      descriptor (p₀).layout b₀ perm m (fun a => (binCode a).val) z' b := hr
  rw [hz] at h
  exact (hc p.layout bin slot x hpop htotal hwidth u b col).trans (congrArg col.read h)

/-- The whole field-word list of the saved terminal, supplied by the immutable
birth packet compiler and its shared live hook frame. -/
theorem saved_terminal_records (hc : ComputesCuts (m := m) pop binCode perm cut) (x : σ → Bool)
    (hpop : PublicPopulation.Represents pop p.layout bin slot binCode x) (htotal : ∀ a,count p.layout bin a < 2^w)
    (hwidth : ∀ z,value (x ∘ pop.width (slot z)) = p.layout.width z)
    (rep : Represents G₀ cell aux sID eID portID F x) (room : ∀ v,incoming G₀ v < 2^w)
    (a : S) (t : Fin D × Bool) (hone : 1 < 2^w)
    (hcount : value (fun k => counts.eval x (a,none,k)) = blocks (p₀).layout b₀ perm m a)
    (fit : ∀ z : {z : (p₀).layout.Edge // b₀ z = some (perm t.1 a)},
      Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*blocks (p₀).layout b₀ perm m a +
        incoming G₀ ((G₀).dst (seedHook e p₀ b₀ perm a t.1 z (decide (or₀ z.val = t.2)))) +
        count (p₀).layout b₀ (perm t.1 a) < 2^w) :
    (emitted e first (relativeRaw e p₀ b₀ perm or₀ first q a eID portID) (.inr (.inl t))).map Packet.record ++
      (eligible p₀ b₀ perm a t.1).map (fun z => payload (native e seed F counts cut occupied) x
        (old₀ z.val,t.1,decide (or₀ z.val = t.2))) =
      (terminalSite e p₀ b₀ perm or₀ first q a sID eID portID (fun a => (binCode a).val) t).rows.map Packet.record := by
  have hp := terminal_payloads e seed F counts cut occupied p₀ b₀ perm or₀ first q oldSite old₀ portID cell aux rep room
    (fun a => (binCode a).val) a t hone hcount (fun z col =>
      saved_cut pop binCode perm cut p slot bin hc x hpop htotal hwidth _ z _ col) fit
  let pre := emitted e first (relativeRaw e p₀ b₀ perm or₀ first q a eID portID) (.inr (.inl t))
  have he := terminal_emitted e p₀ b₀ perm or₀ first q a sID eID portID (fun a => (binCode a).val) t
  exact (congrArg (pre.map Packet.record ++ ·) hp).trans
    ((List.map_append (f := Packet.record)).symm.trans (congrArg (List.map Packet.record) he))

end Packing.InheritedHook

end BorderVNP
end Computability
end OAI
