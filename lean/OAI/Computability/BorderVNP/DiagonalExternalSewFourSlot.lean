import OAI.Computability.BorderVNP.DiagonalExternalSewGlobalRecords
import OAI.Computability.BorderVNP.DiagonalExternalSewRow

/-! # Inverse addresses in the four-slot exterior directory

An occupied interval selects one of the two probes in the low team's
site block and one of the two possible blocks at the high team. Reading
that address recovers its physical team, processor, field rank, remote
block, starting offset and width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FourSlot

open scoped Classical

variable {R r literal stride link g : ℕ}
private abbrev C := Pieces (fieldStart (R := R) (r := r) literal stride link) g link

/-- The first probe owns a repeated local field. -/
def rightProbe (c : C (R := R) (r := r) (literal := literal) (stride := stride) (link := link) (g := g)) : Bool :=
  let A := fieldStart literal stride link c.1 false
  decide (¬(A ≤ c.2.val.1*g ∧ c.2.val.1*g < A+link))

/-- The first block at the partner is measured from the local clipped field start. -/
def remoteBase (c : C (R := R) (r := r) (literal := literal) (stride := stride) (link := link) (g := g)) : ℕ :=
  let A := fieldStart literal stride link c.1 false
  let B := fieldStart literal stride link c.1 true
  (B+(c.2.val.1*g-A))/g

/-- The other selector distinguishes the two possible blocks at the partner. -/
def nextBlock (c : C (R := R) (r := r) (literal := literal) (stride := stride) (link := link) (g := g)) : Bool :=
  decide (c.2.val.2 ≠ remoteBase c)

/-- Addresses are allocated at the low team and at the initial block of that end. -/
def index (V : ℕ) (hg : 0 < g) (fit : literal+R*link ≤ stride) (room : r*stride ≤ V*g)
    (c : C (R := R) (r := r) (literal := literal) (stride := stride) (link := link) (g := g)) :
    Fin (R+1) × Fin V × (Bool × Bool) :=
  (c.1.1.val.1,⟨c.2.val.1,fieldBlock_lt _ _ _ _ V hg fit room c false⟩,rightProbe c,nextBlock c)

private theorem lowRanks (b : Routing.Block (R+1)) :
    b.val.1.val ≤ (fieldRank b false).val ∧
      (fieldRank b false).val+1 = b.val.2.val ∧ (fieldRank b true).val = b.val.1.val := by
  have h : b.val.1.val < b.val.2.val := b.property
  change b.val.1.val ≤ (if b.val.2.val < b.val.1.val then b.val.2.val else b.val.2.val-1) ∧
    (if b.val.2.val < b.val.1.val then b.val.2.val else b.val.2.val-1)+1 = b.val.2.val ∧
    (if b.val.1.val < b.val.2.val then b.val.1.val else b.val.1.val-1) = b.val.1.val
  rw [ite_eq_right (not_lt_of_gt h),ite_eq_left h]
  omega

variable (c : C (R := R) (r := r) (literal := literal) (stride := stride) (link := link) (g := g))

/-- Reading the inverse address gives exactly the nonempty, ordered physical
cable interval, including its two actual endpoint names. -/
theorem row_index (hg : 0 < g) (small : g ≤ link) (fit : literal+R*link ≤ stride) :
    row R r literal stride link g c.1.1.val.1.val c.2.val.1 (rightProbe c) (nextBlock c) =
      ⟨true,c.1.2.val,(fieldRank c.1.1 false).val,c.1.1.val.2.val,c.2.val.2,
        (pieceBounds _ _ c).1,pieceWidth _ _ c⟩ := by
  let A := fieldStart literal stride link c.1 false
  let B := fieldStart literal stride link c.1 true
  let i := pieceOffset _ _ c ⟨0,pieceWidth_pos _ _ c⟩
  have h := pieceOffset_blocks _ _ c ⟨0,pieceWidth_pos _ _ c⟩
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change (A+i.val)/g = c.2.val.1 at hl
  change (B+i.val)/g = c.2.val.2 at hr
  let x := c.2.val.1*g + if rightProbe c then g-1 else 0
  have hm : A ≤ x ∧ x < A+link := probe_mem hg small i.isLt hl
  have hd := decode_probe c.1.2 (fieldRank c.1.1 false) x (hg.trans_le small) fit hm
  have ho := remote_eq (B := B) hg hl
  rw [hr] at ho
  change c.2.val.2 = remoteBase c ∨ c.2.val.2 = remoteBase c+1 at ho
  have hnext : remoteBase c+(nextBlock c).toNat = c.2.val.2 := by
    rcases ho with h | h
    · simp [nextBlock,h]
    · simp [nextBlock,h]
  obtain ⟨hu,hpartner,hother⟩ := lowRanks c.1.1
  have hA : c.1.2.val*stride+literal+(fieldRank c.1.1 false).val*link = A := rfl
  have hB : c.1.2.val*stride+literal+c.1.1.val.1.val*link = B := by
    change _ = c.1.2.val*stride+literal+(fieldRank c.1.1 true).val*link
    rw [hother]
  have dup : rightProbe c = false ∨ ¬(A ≤ c.2.val.1*g ∧ c.2.val.1*g < A+link) := by
    by_cases hit : A ≤ c.2.val.1*g ∧ c.2.val.1*g < A+link
    · exact Or.inl (decide_eq_false (not_not_intro hit))
    · exact Or.inr hit
  have hremote : (B+(c.2.val.1*g-A))/g + (nextBlock c).toNat = c.2.val.2 := hnext
  have hcut := bounds_piece c
  change bounds A B g link c.2.val.1 c.2.val.2 = pieceBounds _ _ c at hcut
  have hwidth := pieceWidth_eq_bounds _ _ hg c
  have hpos := pieceWidth_pos _ _ c
  have hlt : (pieceBounds _ _ c).1 < (pieceBounds _ _ c).2 := by omega
  dsimp only [x] at hd
  dsimp only [row]
  simp only [hd.1,hd.2.2,hA,hB,hremote,hcut,hd.2.1,hu,dup,hlt,c.1.2.isLt,(fieldRank c.1.1 false).isLt,
    hpartner,← hwidth,true_and,decide_true]

/-- Two live intervals cannot occupy the same address, even when some of the
four padded candidates are empty. -/
theorem index_injective (V : ℕ) (hg : 0 < g) (small : g ≤ link) (fit : literal+R*link ≤ stride)
    (room : r*stride ≤ V*g) :
    Function.Injective (index (R := R) (r := r) V hg fit room) := by
  intro a b h
  have ht := congrArg (fun x : Fin (R+1) × Fin V × (Bool × Bool) => x.1) h
  have hs := congrArg (fun x : Fin (R+1) × Fin V × (Bool × Bool) => x.2.1.val) h
  have he := congrArg (fun x : Fin (R+1) × Fin V × (Bool × Bool) =>
    row R r literal stride link g x.1.val x.2.1.val x.2.2.1 x.2.2.2) h
  change row _ _ _ _ _ _ a.1.1.val.1.val a.2.val.1 (rightProbe a) (nextBlock a) =
    row _ _ _ _ _ _ b.1.1.val.1.val b.2.val.1 (rightProbe b) (nextBlock b) at he
  rw [row_index a hg small fit,row_index b hg small fit] at he
  have hproc := congrArg Row.proc he
  have hpartner := congrArg Row.partner he
  have hremote := congrArg Row.remote he
  rcases a with ⟨⟨⟨⟨u,v⟩,hu⟩,i⟩,⟨⟨s,t⟩,h₁⟩⟩
  rcases b with ⟨⟨⟨⟨u',v'⟩,hv⟩,j⟩,⟨⟨s',t'⟩,h₂⟩⟩
  change u = u' at ht
  change s = s' at hs
  change t = t' at hremote
  change v.val = v'.val at hpartner
  change i.val = j.val at hproc
  obtain rfl := Fin.ext hpartner
  obtain rfl := Fin.ext hproc
  subst u'; subst s'; subst t'
  rfl

end Diagonal.ExternalSew.FourSlot

end BorderVNP
end Computability
end OAI
