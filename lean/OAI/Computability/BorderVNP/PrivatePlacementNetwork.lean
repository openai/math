import OAI.Computability.BorderVNP.PrivatePlacementAddressed
import OAI.Computability.BorderVNP.PrivatePlacementSupplied

/-! # Native placement for the packed network with private report-tail capacity -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.PrivateBank

open Crossing CellAddresses RoutingISA Function
open scoped Classical

/-- Extend bounded supplied IDs by one reserved report region per cell. -/
def reserveID {A : Type*} {M C : ℕ} (id : A ↪ Fin M) : (A ⊕ Fin C) ↪ Fin (M+C) where
  toFun a := ⟨numbered id a, by
    cases a with
    | inl a => change (id a).val < M+C; have := (id a).isLt; omega
    | inr c => change M+c.val < M+C; exact Nat.add_lt_add_left c.isLt _⟩
  inj' := fun _ _ e => (numbered id).injective (congrArg Fin.val e)

private theorem reserve_val {A : Type*} {M C : ℕ} (id : A ↪ Fin M) :
    ((reserveID (C := C) id).trans Fin.valEmbedding) = numbered id := by ext x; rfl

/-- One fixed reserved interval follows the true supplied words of each cell. It is
used only for address capacity; the machine never guesses or scans its unused suffix. -/
theorem reservedSize {A : Type*} [Fintype A] {C : ℕ} (sc : A → Fin C) (sw : A → ℕ) (gap : ℕ) (c : Fin C) :
    DataSlabs.size (Sum.elim sc id) (Sum.elim sw (fun _ : Fin C => gap)) c = DataSlabs.size sc sw c + gap := by
  simp only [DataSlabs.size, Fintype.sum_sum_type, Sum.elim_inl,Sum.elim_inr,id_eq]
  congr 1
  rw [Finset.sum_eq_single c]
  · exact ite_eq_left rfl
  · intro a _ h; exact ite_eq_right h
  · simp

variable {D C m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- The actual frame64 image from the native prefix pass, together with frame65's true
network-port offsets, gives separated absolute addresses for every private or live
data lane. This includes the complete crossing-incidence prefix and the fixed report
capacity before any private description. -/
noncomputable def networkPlacement (d : Layout) {w : ℕ} (l : PrivatePlacement.Layout)
    (before after : ℕ → ℕ) (image : l.Image before l.entries after) (fit : l.Fits w before)
    (entries : l.entries = d.entries) (desc : l.desc = d.description)
    (oldCell : Fin d.entries → Fin C) (owners : ∀ j : Fin d.entries, l.owner before j.val = (oldCell j).val)
    (live : (Fin d.teams × Fin d.sites) ↪ P) (liveWidth : ∀ k, bits (live k) = d.block)
    (counts : ∀ c : Fin C, before (l.supplied+c.val) = suppliedSize N cell c)
    (liveBase : ℕ) (separateRaw : l.raw+2*l.entries ≤ liveBase) (separateCounters : l.scratch+l.cells ≤ liveBase)
    (liveRows : ∀ k : Fin d.teams × Fin d.sites,
      let p := live k
      let c := cell (N.attach p)
      ISA.placement before liveBase (k.1.val*d.sites+k.2.val) =
        (c.val,CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) (.inr ⟨p,rfl⟩))) :
    let genuine := SuppliedWord N cell
    let sc := Sum.elim (fun x : genuine => x.1) (id : Fin C → Fin C)
    let sw := Sum.elim (supplyWidth N cell) (fun _ : Fin C => l.gap)
    let si := reserveID (C := C) (suppliedID N cell edgeID portID)
    BankPlacement d (ISA.placement after l.raw) (ISA.placement after liveBase) ((genuine ⊕ Fin C) ⊕ Fin d.entries)
      (Sum.elim sc oldCell) (numbered si) (Sum.elim sw fun _ => d.description) := by
  intro genuine sc sw si
  let keys : (Fin d.teams × Fin d.sites) ↪ genuine ⊕ Fin C :=
    (live.trans (suppliedPort N cell)).trans Embedding.inl
  apply ofNativeImage sc si sw oldCell keys liveWidth l before after image fit entries desc owners _ liveBase
    separateRaw separateCounters
  · intro k
    rw [liveRows k]
    congr 1
    change _ = DataSlabs.base (Sum.elim (fun x : genuine => x.1) id)
      ((reserveID (C := C) (suppliedID N cell edgeID portID)).trans Fin.valEmbedding)
      (Sum.elim (supplyWidth N cell) (fun _ => l.gap)) (.inl (suppliedPort N cell (live k)))
    rw [reserve_val,base_supplied]
    exact (dataSlabs_base N cell edgeID portID _ (.inr ⟨live k,rfl⟩)).symm
  · intro c
    rw [counts, reservedSize, dataSlabs_size]

end Packing.Directory.PrivateBank

end BorderVNP
end Computability
end OAI
