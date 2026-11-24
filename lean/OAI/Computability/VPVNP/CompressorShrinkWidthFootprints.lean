import OAI.Computability.VPVNP.CompressorShrinkBundleAbsolute
import OAI.Computability.VPVNP.CompressorRefreshStageFrame
import OAI.Computability.VPVNP.CompressorSlotFillFootprint

/-!
# Probes of dense shrinking width, prefix, AB and absolute-ID workers

All bounds concern the chronological source events. For both scattered
payloads the rank and owner cells keep their original values throughout
the scan, so indirect writes stay in the two reserved rectangles.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkWidthFootprints

open BurstRAM PrimedStackRAM SourceTransport
open SlotFillFootprint (InColumn)
open scoped Fin.CommRing

variable {w : ℕ}

/-- A scan covers cursor ordinals from zero to the bound and confines all its external reads
and writes to their respective allowed regions. -/
abbrev Checked (N : ℕ) (rd wr : ℕ → Prop) (rs : List (Report w)) :=
  StageFrame.Scanned 0 N rs ∧ Reads rd (eventLog rs) ∧ Writes wr (eventLog rs)

private theorem add_in (base off : Word w) {n : ℕ} (fit : base.val+n ≤ 2^w) (within : off.val < n) :
    InColumn base.val n (base+off).val := by
  rw [Fin.val_add,Nat.mod_eq_of_lt (by omega)]
  exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left within _⟩

/-- The same quotient and remainder index the sorted prefixes and AB pieces. -/
private theorem coordinates (p : Fin 5 → Word w) {B : ℕ} (positive : 0 < (p 0).val)
    (stride : (p 0).val ≤ (p 1).val) {i : Word w} (hi : i.val < B*(p 0).val) :
    (BundlePrefixRAM.row p i).val < B ∧ (BundlePrefixRAM.index p i).val < B*(p 1).val := by
  have hr : (BundlePrefixRAM.row p i).val = i.val/(p 0).val :=
    Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt i.isLt)
  have hp : (BundlePrefixRAM.pos p i).val = i.val%(p 0).val :=
    Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt i.isLt)
  have row := (Nat.div_lt_iff_lt_mul positive).mpr hi
  have col := (Nat.mod_lt i.val positive).trans_le stride
  have cap := Nat.mul_le_mul_right (p 1).val row
  rw [Nat.succ_mul] at cap
  refine ⟨hr ▸ row,?_⟩
  rw [BundlePrefixRAM.index,Fin.val_add,Fin.val_mul,hr,hp,Nat.mod_add_mod]
  exact (Nat.mod_le ..).trans_lt (by omega)

/-- Addresses the prefix worker may read in the per-bundle width rectangle and the column of
running bundle totals. -/
def prefixReads (p : Fin 5 → Word w) (B x : ℕ) :=
  InColumn (p 2).val (B*(p 1).val) x ∨ InColumn (p 4).val B x

/-- Addresses the prefix worker may write in the per-bundle start-offset rectangle and the
totals column. -/
def prefixWrites (p : Fin 5 → Word w) (B x : ℕ) :=
  InColumn (p 3).val (B*(p 1).val) x ∨ InColumn (p 4).val B x

theorem prefix_scan (p : Fin 5 → Word w) (B : ℕ) (layout : BundlePrefixRAM.Layout p B)
    (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template BundlePrefixRAM.visit 0).instantiate w p).program 25
      (some 0) m (List.replicate (B*(p 0).val) []) = some rs) :
    Checked (B*(p 0).val) (prefixReads p B) (prefixWrites p B) rs := by
  have step (j : ℕ) (hj : j < B*(p 0).val) (mem : Memory w) :
      Reads (prefixReads p B) (BundlePrefixRAM.events p mem (j : Word w)) ∧
      Writes (prefixWrites p B) (BundlePrefixRAM.events p mem (j : Word w)) := by
    obtain ⟨hr,hi⟩ := coordinates p (B := B) (i := (j : Word w)) layout.positive layout.size_le_stride ((Nat.mod_le j (2^w)).trans_lt hj)
    have width := add_in _ _ layout.widthsFit hi
    have offset := add_in _ _ layout.startsFit hi
    have total := add_in _ _ layout.totalsFit hr
    constructor <;> intro addr val he <;> simp [BundlePrefixRAM.events] at he
    · rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩; exact .inl width; exact .inr total
    · rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩; exact .inl offset; exact .inr total
  obtain ⟨shape,_,rd,wr⟩ := StageFrame.scan _ 25 0 (B*(p 0).val) (fun _ _ ↦ True)
    (BundlePrefixRAM.events p) (prefixReads p B) (prefixWrites p B)
    (fun j _ _ mem ↦ BundlePrefixRAM.native p mem j) (fun j _ hj mem _ ↦ ⟨trivial,step j hj mem⟩)
    (Nat.zero_le _) m rs trivial run
  exact ⟨shape,rd,wr⟩

/-- The bundle-total column from which the AB worker reads its balancing inputs. -/
def abReads (p : Fin 5 → Word w) (B x : ℕ) := InColumn (p 2).val B x

/-- Allowed write addresses for the AB worker. The two rectangles reserve a full row stride per
bundle for piece widths and starting offsets. -/
def abWrites (p : Fin 5 → Word w) (B x : ℕ) :=
  ∃ t : Fin 2, InColumn (p (t.natAdd 3)).val (B*(p 1).val) x

theorem ab_scan (p : Fin 5 → Word w) (B : ℕ) (layout : ABWidths.Layout p B)
    (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template ABWidths.visit 0).instantiate w p).program 30 (some 0) m
      (List.replicate (B*(p 0).val) []) = some rs) : Checked (B*(p 0).val) (abReads p B) (abWrites p B) rs := by
  have step (j : ℕ) (hj : j < B*(p 0).val) (mem : Memory w) :
      Reads (abReads p B) (ABWidths.events p mem (j : Word w)) ∧
      Writes (abWrites p B) (ABWidths.events p mem (j : Word w)) := by
    obtain ⟨hr,hi⟩ := coordinates p (B := B) (i := (j : Word w)) layout.positive layout.stride ((Nat.mod_le j (2^w)).trans_lt hj)
    have total := add_in _ _ layout.totalFit hr
    have out (t : Fin 2) := add_in _ _ (layout.outFit t) hi
    constructor <;> intro addr val he <;> simp [ABWidths.events] at he
    · obtain ⟨rfl,_⟩ := he; exact total
    · rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩; exact ⟨0,out 0⟩; exact ⟨1,out 1⟩
  obtain ⟨shape,_,rd,wr⟩ := StageFrame.scan _ 30 0 (B*(p 0).val) (fun _ _ ↦ True)
    (ABWidths.events p) (abReads p B) (abWrites p B) (fun j _ _ mem ↦ ABWidths.native p mem j)
    (fun j _ hj mem _ ↦ ⟨trivial,step j hj mem⟩) (Nat.zero_le _) m rs trivial run
  exact ⟨shape,rd,wr⟩

open BundleWidthScatter

/-- Addresses in the owner, rank and old-width columns consulted by the width scatter. -/
def scatterReads (p : Fin 5 → Word w) (A x : ℕ) := ∃ t : Fin 3, InColumn (p (t.castAdd 2)).val A x

/-- The two consecutive sorted-width rectangles, one for thick entries and one for CD entries,
that receive the scatter writes. -/
def scatterWrites (p : Fin 5 → Word w) (B x : ℕ) := InColumn (p 4).val ((B+B)*(p 3).val) x

private theorem scatter_scan {C : Type*} (P : BurstRAM.Program w C) (fuel : ℕ) (p : Fin 5 → Word w)
    (A B : ℕ) (m : Memory w) (rs : List (Report w)) (log : Memory w → Word w → List (Event w))
    (native : ∀ mem i, execute P fuel (P.start i) mem [] = some ⟨log mem i,some (i+1)⟩)
    (probes : ∀ mem i, Reads (fun x ↦ ∃ t : Fin 3, x = (source p t i).val) (log mem i) ∧
      Writes (fun x ↦ x = (outAddress p mem i).val) (log mem i))
    (fit : ∀ t : Fin 3, (p (t.castAdd 2)).val+A ≤ 2^w)
    (write : ∀ j < A, scatterWrites p B (outAddress p m (j : Word w)).val)
    (reg : Regions p m A)
    (run : runSegment P fuel (some 0) m (List.replicate A []) = some rs) :
    Checked A (scatterReads p A) (scatterWrites p B) rs := by
  let I (_ : ℕ) (mem : Memory w) := ∀ t : Fin 3, ∀ j < A,
    mem (source p t (j : Word w)).val = m (source p t (j : Word w)).val
  have step (j : ℕ) (hj : j<A) (mem : Memory w) (h : I j mem) :
      I (j+1) (after mem (log mem (j : Word w))) ∧ Reads (scatterReads p A) (log mem (j : Word w)) ∧
      Writes (scatterWrites p B) (log mem (j : Word w)) := by
    have dst : outAddress p mem (j : Word w) = outAddress p m (j : Word w) := by
      rw [outAddress,h 0 j hj,h 1 j hj]; rfl
    obtain ⟨rd,wr⟩ := probes mem (j : Word w)
    refine ⟨?_,?_,?_⟩
    · intro t k hk
      apply (after_outside mem wr ?_).trans (h t k hk)
      rw [dst]
      exact fun eqn ↦ reg.apart t k hk j hj eqn
    · intro addr val he
      obtain ⟨t,e⟩ := rd addr val he
      rw [e]; exact ⟨t,add_in _ _ (fit t) ((Nat.mod_le ..).trans_lt hj)⟩
    · intro addr val he
      rw [wr addr val he,dst]; exact write j hj
  obtain ⟨shape,_,rd,wr⟩ := StageFrame.scan P fuel 0 A I log (scatterReads p A) (scatterWrites p B)
    (fun j _ _ mem ↦ native mem j) (fun j _ hj mem inv ↦ step j hj mem inv) (Nat.zero_le _) m rs
    (fun _ _ _ ↦ rfl) run
  exact ⟨shape,rd,wr⟩

theorem width_scan (p : Fin 5 → Word w) (A B : ℕ) (m : Memory w) (rs : List (Report w))
    (fit : ∀ t : Fin 3, (p (t.castAdd 2)).val+A ≤ 2^w)
    (write : ∀ j < A, scatterWrites p B (outAddress p m (j : Word w)).val)
    (reg : Regions p m A)
    (run : runSegment ((template BundleWidthScatter.visit 0).instantiate w p).program 19 (some 0) m
      (List.replicate A []) = some rs) : Checked A (scatterReads p A) (scatterWrites p B) rs := by
  apply scatter_scan _ 19 p A B m rs (BundleWidthScatter.events p) (BundleWidthScatter.native p) _ fit write reg run
  intro mem i
  constructor <;> intro addr val he <;> simp [BundleWidthScatter.events] at he
  · rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩
  · exact congrArg Fin.val he.1

theorem absolute_scan (p : Fin 7 → Word w) (A B : ℕ) (m : Memory w) (rs : List (Report w))
    (fit : ∀ t : Fin 3, ((MotifAbsolute.columns p) (t.castAdd 2)).val+A ≤ 2^w)
    (write : ∀ j < A, scatterWrites (MotifAbsolute.columns p) B (outAddress (MotifAbsolute.columns p) m (j : Word w)).val)
    (reg : Regions (MotifAbsolute.columns p) m A)
    (run : runSegment ((template MotifAbsolute.visit 0).instantiate w p).program 25 (some 0) m
      (List.replicate A []) = some rs) :
    Checked A (scatterReads (MotifAbsolute.columns p) A) (scatterWrites (MotifAbsolute.columns p) B) rs := by
  apply scatter_scan _ 25 _ A B m rs (MotifAbsolute.events p) (MotifAbsolute.native p) _ fit write reg run
  intro mem i
  constructor <;> intro addr val he <;> simp [MotifAbsolute.events] at he
  · rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩
  · exact congrArg Fin.val he.1

end CompressorRecords.ShrinkWidthFootprints

end VPVNP
end Computability
end OAI
