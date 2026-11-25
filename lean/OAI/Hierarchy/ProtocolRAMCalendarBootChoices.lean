import OAI.Hierarchy.ProtocolRAMCalendarCTAgree
import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.TaggedWireHeaderRestore

namespace OAI
/-! # Original private choices commute with the concrete CT and controller boot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.Boot
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT
open ThreeFlat.RAM
open WireTelescope.CalendarTape
open scoped Classical Fin.CommRing
variable {z d k jobs : ℕ}
local notation "W" => wordBits z d copies
local notation "H" => heapEnd z d copies

private theorem static_fill {w : ℕ} (base count : ℕ) (f : ℕ→Word w) (m n : Memory w)
    (x : ℕ) (same : m x=n x) : fillSegment base count f m x=fillSegment base count f n x := by
  unfold fillSegment
  split <;> first | rfl | exact same

private theorem controller_cell (s : Fin jobs→Market z d k) (m n : Tape z d) (x : ℕ) (same : m x=n x) :
    controller s m x=controller s n x := by
  unfold controller ProtocolRAMStaticSlabs.mounted
  split
  · rename_i i hi
    let v:=s i
    have priced : price v m x=price v n x := by
      unfold price PurchaseFrozen.Shelf.quoteTape PurchaseMarks.mount
      exact static_fill _ _ _ _ _ _ same
    change localData v m x=localData v n x
    simp only [localData,PurchaseFrozen.Shelf.mountROM,ProtocolRAMStaticSlabs.mounted]
    split
    · rename_i t ht
      let l:=v.shelf.L v.sampler v.depth t
      have sampler : ProtocolRAMPurchaseSampler.install l.start l.groups (v.sampler.rows l.sockets)
          (reverseDigits v.sampler l.sockets) (price v m) x=
          ProtocolRAMPurchaseSampler.install l.start l.groups (v.sampler.rows l.sockets)
          (reverseDigits v.sampler l.sockets) (price v n) x := by
        unfold ProtocolRAMPurchaseSampler.install
        exact static_fill _ _ _ _ _ _ priced
      change GateColumns.mount _ _ (PurchaseDirectory.install _ _ _ _ _) x=
        GateColumns.mount _ _ (PurchaseDirectory.install _ _ _ _ _) x
      unfold GateColumns.mount
      split
      · rfl
      · unfold PurchaseDirectory.install
        exact static_fill _ _ _ _ _ _ sampler
    · exact priced
  · exact same

private theorem input_cell (m n : Tape z d) (x : ℕ) (same : m x=n x) :
    inputTape z d W m x=inputTape z d W n x := by
  simp only [inputTape,geometryTape,Function.extend]
  split <;> first | rfl | split <;> first | rfl | exact same

private theorem initialized_cell (size : ℕ) (left right : Tape z d) (x : ℕ) (h : left x=right x) :
    Computability.VPVNP.RAMMemory.initialMemory size left x=Computability.VPVNP.RAMMemory.initialMemory size right x := by
  simp [Computability.VPVNP.RAMMemory.initialMemory,h]

/-- The input image of the native chronological program depends at every
address only on that input word. The address layout is public. -/
theorem header_cell (v : Fin jobs→Market z d k) (size : ℕ) (left right : Tape z d)
    (x : ℕ) (eqn : left x=right x) : header v size left x=header v size right x :=
  input_cell _ _ _ (controller_cell v _ _ _ (initialized_cell size left right x eqn))

/-- The only genuine input dependence of a high final word is its original
value at that same address. Inside the CT heap a separate full induction
tracks every ordinal allocator update on the same actual permutation. -/
theorem booted_off_pages (v : Fin jobs→Market z d k) {size : ℕ} (layout : Layout v size)
    (hd : 1≤d) (π : Equiv.Perm (Fin (2^z))) (left right : Tape z d)
    (read : ∀i : Fin (2^z),left i.val=((π i).val:Word W))
    (gone : ℕ→Prop) (late : ∀x,gone x→H≤x) (same : ∀x,¬gone x→left x=right x) :
    ∀x,¬gone x→booted v size left x=booted v size right x := by
  let l:=controller v (Computability.VPVNP.RAMMemory.initialMemory size left)
  let r:=controller v (Computability.VPVNP.RAMMemory.initialMemory size right)
  have outside (x) (off:¬gone x) : l x=r x :=
    controller_cell v _ _ _ (initialized_cell _ _ _ _ (same x off))
  have low (x : ℕ) (hx:x<H) : l x=r x := outside x fun on=>(Nat.not_lt_of_ge (late x on)) hx
  have supplied (i : Fin (2^z)) : l i.val=((π i).val:Word W) := by
    have small:=i.isLt.trans_le (root_extent (z:=z) (d:=d))
    have miss (j : Fin jobs) : ¬ProtocolRAMStaticSlabs.Inside (fun t=>Boot.low (v t)) (fun t=>high (v t)) j i.val :=
      fun hit=>(small.trans_le (layout.afterHeap j)).not_ge hit.1
    change controller v _ i.val=_
    rw [controller,ProtocolRAMStaticSlabs.outside _ _ miss]
    simpa only [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (small.trans_le layout.subdivision)] using read i
  have suppliedR (i : Fin (2^z)) : r i.val=((π i).val:Word W) :=
    (low i.val (i.isLt.trans_le (root_extent (z:=z) (d:=d)))).symm.trans (supplied i)
  have both:=images_low hd π l r supplied suppliedR (fun x hx=>input_cell _ _ _ (low x hx)) (rounds d) le_rfl
  have al:=after_levels hd π l supplied (physical_ordinal hd π) (rounds d) le_rfl
  have ar:=after_levels hd π r suppliedR (physical_ordinal hd π) (rounds d) le_rfl
  intro x off
  simp only [booted,initial_eq v layout]
  by_cases below:x<H
  · exact both x below
  · exact (images_above l al (Nat.le_of_not_gt below)).trans
      ((outside x off).trans (images_above r ar (Nat.le_of_not_gt below)).symm)

variable {X : Type} {slot : Event→WireTelescope.CalendarTape.Slot X}

private theorem raw_off (L : WordSlots slot W) (es : List Event) (raw : Tagged.Bits (bits slot es))
    (m : Tape z d) (u : ℕ) (miss : ¬∃e∈es,L.inside e u) : L.header es raw m u=m u := by
  induction es with
  | nil=>rfl
  | cons e es ih=>
    have outside : ¬L.inside e u:=fun on=>miss ⟨e,List.mem_cons_self ..,on⟩
    rw [WordSlots.header,L.install_off _ _ _ _ outside]
    exact ih _ (fun ⟨t,ht,on⟩=>miss ⟨t,List.mem_cons_of_mem _ ht,on⟩)

/-- Install a completely arbitrary binary selector tape either before
the native subdivision or over its genuine baseline result. Both orders
give exactly the same complete physical memory, including dead scratch. -/
theorem booted_header (v : Fin jobs→Market z d k) {size : ℕ} (layout : Layout v size)
    (hd : 1≤d) (π : Equiv.Perm (Fin (2^z))) (m : Tape z d)
    (input : ∀i : Fin (2^z),m i.val=((π i).val:Word W)) (L : WordSlots slot W)
    (es : List Event) (raw : Tagged.Bits (bits slot es)) (apart : L.disjoint es)
    (pages : ∀e∈es,∀x,L.inside e x→H≤x ∧ x<size ∧
      ∀i,¬ProtocolRAMStaticSlabs.Inside (fun j=>low (v j)) (fun j=>high (v j)) i x) :
    booted v size (L.header es raw m)=L.header es raw (booted v size m) := by
  let packed:=L.header es raw m
  let touched:=fun x=>∃e∈es,L.inside e x
  have late : ∀x,touched x→H≤x := by
    rintro x ⟨e,he,hx⟩
    exact (pages e he x hx).1
  have off:∀x,¬touched x→packed x=m x:=fun x hx=>raw_off L es raw m x hx
  have permutation (i : Fin (2^z)) : packed i.val=((π i).val:Word W) :=
    (off _ (fun on=>(i.isLt.trans_le (root_extent (z:=z) (d:=d))).not_ge (late _ on))).trans (input i)
  have unchanged:=booted_off_pages v layout hd π packed m permutation touched late off
  have correct:=(start v layout hd π packed permutation).2
  have rawBits:L.static es packed=raw:=L.static_header es raw m apart
  funext x
  have installed:=L.header_at es packed (booted v size m) x
  rw [rawBits] at installed
  rw [installed]
  by_cases yes:touched x
  · obtain ⟨e,he,inside⟩:=yes
    obtain ⟨above,small,free⟩:=pages e he x inside
    rw [ite_eq_left (show ∃e∈es,L.inside e x from ⟨e,he,inside⟩)]
    change booted v size packed x=packed x
    rw [correct.kept x above free]
    simp [Computability.VPVNP.RAMMemory.initialMemory,small]
  · rw [ite_eq_right yes]
    exact unchanged x yes

end Hierarchy.ProtocolRAM.Calendar.Boot
end

end OAI
