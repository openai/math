import OAI.Hierarchy.ProtocolRAMPackedAnchorPair
import OAI.Hierarchy.ProtocolRAMPackedPlacement

namespace OAI
/-! # Interpreting the two genuine remapping passes on the mixed report -/

namespace Hierarchy.ProtocolRAMAnchoredRows

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMReportedPorts ProtocolRAMPackedPlacement TaggedShorterSupergroups
open scoped Fin.CommRing

variable {W K N H lanes w : ℕ} {G : Type*} {size : G → ℕ}

def rows (g : ℕ) (source : Fin N → Row) (mem : Memory W) : Fin N → Row :=
  translated source (fun i => (mem (g+i.val)).val)

def starts (left right : ℕ) (mem : Memory W) (side : Bool) (i : Fin N) : ℕ :=
  (mem ((if side then right else left)+i.val)).val

/-- Replacing only the group column leaves unchanged which original rows
transport nonempty pieces. Even an empty old incidence type is admitted. -/
theorem pieces_eq (g : ℕ) (source : Fin N → Row) (mem : Memory W) (i : Fin N) :
    pieces (rows g source mem) w i = pieces source w i := rfl

theorem run {g₁ l g₂ r start : ℕ} (owners : Fin K ≃ G) (dir : Directory size H)
    (left right : Bank) (old : Expr) (source : Fin N → Row) (raw : Memory W)
    (receipt : Receipt source w size) (numbered : K ≤ 2^W) (groupRoom : dir.groups ≤ 2^W)
    (portRoom : H*lanes ≤ 2^W)
    (low : old.Fits W g₁) (gf : (ProtocolRAMSupergroupDirectory.groupBank start K).Fits W g₁)
    (bf : (ProtocolRAMSupergroupDirectory.offsetBank start K).Fits W g₁)
    (lf : left.Fits W g₁) (rf : right.Fits W g₁)
    (sep1 : g₁+N ≤ l) (apart : l+N ≤ g₂) (sep2 : g₂+N ≤ r) (endFit : r+N < 2^W)
    (ownerData : ∀ (b : Bool) (i : Live source w),old.eval
      (ProtocolRAMSupergroupDirectory.mount start lanes owners dir raw) (i.val.val:Word W)=
      ((owners.symm (receipt b i).1).val:Word W))
    (portData : ∀ (b : Bool) (i : Live source w),(if b then right else left).read
      (ProtocolRAMSupergroupDirectory.mount start lanes owners dir raw) (i.val.val:Word W)=
      (((receipt b i).2.val*lanes:ℕ):Word W)) :
    let gm := ProtocolRAMSupergroupDirectory.groupBank start K
    let off := ProtocolRAMSupergroupDirectory.offsetBank start K
    let mem := ProtocolRAMSupergroupDirectory.mount start lanes owners dir raw
    let cost := ProtocolRAMSupergroupPorts.work N old
    ∃ out,(ProtocolRAMPackedAnchorPair.program W N g₁ l g₂ r gm off left right old).Exec mem out (cost+cost) ∧
      (∀ (b : Bool) (i : Live source w),
        (dir.group (receipt b i).1).val=(rows g₂ source out i.val).group ∧
        starts l r out b i.val = (dir.slot (receipt b i).1 (receipt b i).2).val*lanes) ∧
      ∀ a < g₁,out a=mem a := by
  intro gm off mem cost
  obtain ⟨out,exec,words,frame⟩ := ProtocolRAMPackedAnchorPair.run g₁ l g₂ r gm off left right old
    mem low gf bf lf rf sep1 apart sep2 endFit
  refine ⟨out,exec,?_,frame⟩
  intro b i
  let own := (receipt b i).1
  let port := (receipt b i).2
  have directory := ProtocolRAMSupergroupDirectory.resident start lanes owners dir raw numbered own
  have entry := ownerData b i
  change old.eval mem (i.val.val:Word W)=((owners.symm own).val:Word W) at entry
  change gm.read mem ((owners.symm own).val:Word W)=_ ∧ off.read mem ((owners.symm own).val:Word W)=_ at directory
  have groupWord := (words i.val).1
  rw [entry,directory.1] at groupWord
  have baseWord : out ((if b then r else l)+i.val.val) =
      off.read mem (old.eval mem (i.val.val:Word W))+(if b then right else left).read mem (i.val.val:Word W) := by
    cases b
    · exact (words i.val).2.1
    · exact (words i.val).2.2
  rw [entry,directory.2,portData b i] at baseWord
  have physical : out ((if b then r else l)+i.val.val)=(((dir.slot own port).val*lanes:ℕ):Word W) := by
    simpa only [Directory.slot,Nat.add_mul,Nat.cast_add] using baseWord
  have small : (dir.slot own port).val*lanes < 2^W := by
    by_cases zero : lanes=0
    · simp [zero]
    · exact (Nat.mul_lt_mul_of_pos_right (dir.slot own port).isLt (Nat.pos_of_ne_zero zero)).trans_le portRoom
  constructor
  · change (dir.group own).val=(out (g₂+i.val.val)).val
    rw [groupWord,Fin.val_cast_of_lt ((dir.group own).isLt.trans_le groupRoom)]
  · change (out ((if b then r else l)+i.val.val)).val=(dir.slot own port).val*lanes
    rw [physical,Fin.val_cast_of_lt small]

end Hierarchy.ProtocolRAMAnchoredRows

end OAI
