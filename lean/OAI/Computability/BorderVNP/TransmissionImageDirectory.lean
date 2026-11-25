import OAI.Computability.BorderVNP.TransmissionScheduled
import OAI.Computability.BorderVNP.TransmissionReadPreservation

/-! # Reading the scheduler's physical directory throughout transmission -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM
open private addFieldVal cursorVal from OAI.Computability.BorderVNP.TransmissionScheduled

variable {l : TableLayout} {row : ℕ → TableRow} {w : ℕ} {before : ℕ → ℕ} {m : Memory w}

private theorem frame_slot (image : l.Image row before (readings m)) (al : l.Allocated w)
    (pub : Arg → Word w) (hf : (pub 0).val = l.frame) {j : ℕ} (hj : j < 21) :
    (directoryFrame pub m (Fin.ofNat _ j)).val = before (l.frame + j) := by
  have inside := l.contains_offset (a := .frame) hj
  have hfit : l.frame + j < 2^w := al.address inside
  have addr := addFieldVal (pub 0) j (hf ▸ hfit)
  change readings m (pub 0 + Fin.ofNat _ j).val = _
  rw [addr,hf]
  exact image.outside _ (al.separate .frame .widths _ (by decide) inside)
    (al.separate .frame .ordinals _ (by decide) inside)
    (al.separate .frame .offsets _ (by decide) inside) (al.separate .frame .used _ (by decide) inside)

/-- The count read by the transmission setup is the actual scheduler's record count. -/
theorem image_count (image : l.Image row before (readings m)) (al : l.Allocated w)
    (pub : Arg → Word w) (hf : (pub 0).val = l.frame) (loaded : l.frameFields before) :
    (directoryFrame pub m 13).val = l.count :=
  (frame_slot image al pub hf (j := 13) (by decide)).trans loaded.2.2.1

/-- The descriptor cursor starts at the base of the allocated seven-word records. -/
theorem image_records (image : l.Image row before (readings m)) (al : l.Allocated w)
    (pub : Arg → Word w) (hf : (pub 0).val = l.frame) (loaded : l.frameFields before) :
    directoryFrame pub m 12 = Fin.ofNat _ l.records := by
  have h : (directoryFrame pub m 12).val = l.records :=
    (frame_slot image al pub hf (j := 12) (by decide)).trans loaded.2.1
  rw [← h, Fin.ofNat_val_eq_self]

/-- The separate ordinal cursor starts at its allocated base. -/
theorem image_ordinals (image : l.Image row before (readings m)) (al : l.Allocated w)
    (pub : Arg → Word w) (hf : (pub 0).val = l.frame) (loaded : l.frameFields before) :
    directoryFrame pub m 20 = Fin.ofNat _ l.ordinals := by
  have h : (directoryFrame pub m 20).val = l.ordinals :=
    (frame_slot image al pub hf (j := 20) (by decide)).trans loaded.2.2.2.2.2.2
  rw [← h, Fin.ofNat_val_eq_self]

/-- Each local destination interval fits a machine word and excludes the descriptor
and ordinal arrays. A pure sender has no destination to check. -/
def Range.directorySeparated (r : Range w) (self : Word w) (l : TableLayout) : Prop :=
  ∀ mode, r.selected self = some (some mode) → ∀ d ∈ mode.destinations,
    (r.bank self d).val+r.width.val ≤ 2^w ∧ ∀ a, l.contains .records a ∨ l.contains .ordinals a →
      a < (r.bank self d).val ∨ (r.bank self d).val+r.width.val ≤ a

private theorem prefix_at (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w)
    (bits : ℕ → ℕ → Bool) (k : ℕ) (a : ℕ) (inside : l.contains .records a ∨ l.contains .ordinals a)
    (sep : ∀ i < k, (rows i).directorySeparated self l) :
    tableMemory rows self pub m bits k a = m a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tableMemory,Range.apply]
    have prior := ih (fun i hi => sep i (hi.trans k.lt_succ_self))
    cases sel : (rows k).selected self with
    | none => exact prior
    | some role =>
      cases role with
      | none => exact prior
      | some mode =>
        let r := rows k
        have h := sep k k.lt_succ_self mode sel
        exact (rangeMemory_eq_of_outside mode pub (r.bank self) _ _ r.width.val a
          (fun d hd => (h d hd).1) (fun d hd => (h d hd).2 a inside)).trans prior

/-- At every iteration the physical load from the current memory reads the original
seven record words and the ordinal installed by the scheduler. -/
theorem image_directory (image : l.Image row before (readings m)) (al : l.Allocated w)
    (pub : Arg → Word w) (hf : (pub 0).val = l.frame) (loaded : l.frameFields before)
    (sep : ∀ j < l.count, (tableRange l m j).directorySeparated (directoryFrame pub m 0) l)
    (bits : ℕ → ℕ → Bool) (i : ℕ) (hi : i < (directoryFrame pub m 13).val) :
    rangeAt (tableMemory (tableRange l m) (directoryFrame pub m 0) pub m bits i)
      (cursorAt (directoryFrame pub m 12) 7 i) (cursorAt (directoryFrame pub m 20) 1 i) = tableRange l m i := by
  rw [image_count image al pub hf loaded] at hi
  rw [image_records image al pub hf loaded, image_ordinals image al pub hf loaded]
  let base : Word w := cursorAt (Fin.ofNat _ l.records) 7 i
  let ord : Word w := cursorAt (Fin.ofNat _ l.ordinals) 1 i
  let M := tableMemory (tableRange l m) (directoryFrame pub m 0) pub m bits i
  have stay (a : ℕ) (h : l.contains .records a ∨ l.contains .ordinals a) : M a = m a :=
    prefix_at _ _ _ bits i a h (fun j hj => sep j (hj.trans hi))
  have fieldAddr (k : Fin 7) : l.contains .records (7*i+l.records+k.val) := l.contains_record hi k.isLt
  have baseVal : base.val = 7*i+l.records := by
    have room := al.address (fieldAddr 0)
    have bound : l.records+i*7 < 2^w := by omega
    exact (cursorVal l.records 7 i bound).trans (by omega)
  have first : M base.val = m base.val := by
    rw [baseVal]
    exact stay _ (Or.inl (by simpa using fieldAddr 0))
  have field (k : Fin 7) : M (base + Fin.ofNat _ k.val).val = m (base + Fin.ofNat _ k.val).val := by
    have addr := fieldAddr k
    have bound := al.address addr
    rw [addFieldVal base k.val (baseVal ▸ bound),baseVal]
    exact stay _ (Or.inl addr)
  have ordinal : M ord.val = m ord.val := by
    have inside := l.contains_offset (a := .ordinals) hi
    have bound : l.ordinals+i*1 < 2^w := by simpa only [TableLayout.base, Nat.mul_one] using al.address inside
    have val : ord.val = l.ordinals+i := (cursorVal l.ordinals 1 i bound).trans (by rw [Nat.mul_one])
    rw [val]
    exact stay _ (Or.inr inside)
  change rangeAt M base ord = rangeAt m base ord
  unfold rangeAt
  congr 1
  · exact field 1
  · exact field 2
  · exact field 3
  · exact field 4
  · exact field 5
  · exact field 6

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
