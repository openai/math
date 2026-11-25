import OAI.ThreeFlat.BitNetwork
import OAI.ThreeFlat.Diagonal.HistogramBitAddresses
import OAI.ThreeFlat.Diagonal.ShrinkOwnerKernel

namespace OAI
/-! # Old source pointers for the AB and CD bits of all six parties -/

namespace ThreeFlat.Diagonal.CompressorPacking

open MotifBinaryPacking Computability.VPVNP.Compression HistoryContraction
open scoped Classical

variable {V H Tag L : Type} {d c Q : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
  [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c)
  (code : Arc V H Tag L d c ↪ ℕ) (w : Arc V H Tag L d c → ℕ) (hQ : 0<Q)
  (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)

/-- Resolve each local demand bit to one old incident half-index and bit.
The requester supplies a reader for a specific original edge and side. -/
noncomputable def demandBit {X : Type*} (source : (a : Arc V H Tag L d c) → Bool → Fin (w a) → X)
    (m : P.Motif) (side : Bool) (e : Fin 2) : Fin (demandWidth P w num m e) → X :=
  Fin.cases (motive := fun a => Fin (demandWidth P w num m a) → X)
    (fun j => let old := (oldBit P code w (num m).1).symm (SlotEnergy.pieceIndex _ _ hQ ⟨(num m).2,j⟩)
              source old.1.val side old.2)
    (Fin.cases (fun j => source m.val (if P.thick (sourcePosition m.val) then !side else side) j) (fun z => z.elim0)) e

private theorem demandBit_map {X Y : Type*} (f : X → Y) (s : (a : Arc V H Tag L d c) → Bool → Fin (w a) → X)
    (m : P.Motif) (side : Bool) (e : Fin 2) (j : Fin (demandWidth P w num m e)) :
    f (demandBit P code w hQ num s m side e j) =
      demandBit P code w hQ num (fun a b t => f (s a b t)) m side e j := by fin_cases e <;> rfl

theorem demandBit_read {h p : ℕ} (s : (a : Arc V H Tag L d c) → Bool → Fin (w a) → BitSource h p)
    (z : Bool → OldWords w) (g : Fin h → Bool) (pin : Fin p → Bool)
    (read : ∀ a b t, (s a b t).read g pin = (word _).symm (z b a) t)
    (m : P.Motif) (side : Bool) (e : Fin 2) (j : Fin (demandWidth P w num m e)) :
    (demandBit P code w hQ num s m side e j).read g pin =
      (word _).symm (demandEnd P code w hQ num m (z false) (z true) side e) j := by
  rw [demandBit_map P code w hQ num (fun s => s.read g pin) s m side e j]
  simp only [read]
  fin_cases e
  · cases side <;> exact (abWord_bit ..).symm
  · cases side <;> by_cases thick : P.thick (sourcePosition m.val) <;>
      simp [demandBit,demandEnd,cdWord,thick] <;> rfl'

/-- Reads are restricted to the current owner's old row. Off-owner reads
are literal zeros, agreeing with the compressor's default word. -/
noncomputable def ownerSource {h p : ℕ} (layout : Bool) (v : Site V Tag L)
    (s : (i : {i // P.placement layout i = v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → BitSource h p)
    (a : Arc V H Tag L d c) (b : Bool) (t : Fin (w a)) : BitSource h p :=
  if yes : P.placement layout ((oldGraph P).vertex a b) = v then s ⟨_,yes⟩ ⟨(a,b),rfl⟩ t else .constant false

theorem ownerSource_read {h p : ℕ} (layout : Bool) (v : Site V Tag L)
    (s : (i : {i // P.placement layout i = v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → BitSource h p)
    (row : OwnedRow P w layout v) (g : Fin h → Bool) (pin : Fin p → Bool)
    (read : ∀ i a t, (s i a t).read g pin = (word _).symm (row i a) t)
    (a : Arc V H Tag L d c) (b : Bool) (t : Fin (w a)) :
    (ownerSource P w layout v s a b t).read g pin = (word _).symm (ownedWords P w layout v row b a) t := by
  unfold ownerSource ownedWords
  by_cases yes : P.placement layout ((oldGraph P).vertex a b) = v
  · simp only [dite_eq_left yes,read]
    apply congrArg (fun z : Fin (2 ^ w a) => (word (w a)).symm z t)
    symm
    first
    | exact dite_eq_left yes
  · simp [yes,word_bit,BitSource.read]

end ThreeFlat.Diagonal.CompressorPacking

end OAI
