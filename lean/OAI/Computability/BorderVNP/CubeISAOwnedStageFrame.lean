import OAI.Computability.BorderVNP.CubeISAOwnedScatterSingleRow
import OAI.Computability.BorderVNP.CubeISAOwnedRowSetupSingle

/-! # Transfer of the outer pair-loop state across an addressed scatter stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open VPVNP.BurstRAM DiagonalResidueRAM Owned

/-- Fixed control registers retained by every complete side of a pair, including
the two outer-loop registers and the growing vertex directory cursor. -/
abbrev Control (j : Reg) : Prop := j ∈ ([0,1,3,4,7,14,15,22,23] : List Reg)

/-- Word equality of all outer control registers. -/
def Keeps {w : ℕ} (u v : Bank w) : Prop := ∀ j, Control j → v j = u j

/-- Inputs whose actual addresses must remain resident between row stages. -/
structure Protected (l : OwnedRowSetup.Layout) (n frame : ℕ) (src : Set ℕ) : Prop where
  /-- Only the five primary scalar words actually loaded by the adapter. -/
  fields : ∀ j ∈ [59,60,61,62,63], frame+j ∈ src
  /-- The block count and packet-bank pointer of the secondary header. -/
  secondary : l.header+7 ∈ src ∧ l.header+8 ∈ src
  /-- Power entries for all possible chosen axes. -/
  powers : ∀ j ≤ n, l.power+j ∈ src

/-- The frame addresses remain loaded after any scatter retaining the protected words. -/
theorem Protected.loaded {w n : ℕ} {l : OwnedRowSetup.Layout} {pub : Arg → Word w} {src : Set ℕ}
    (protect : Protected l n (pub 0).val src) {m mu : Memory w}
    (h : l.Loaded n (readings pub) (readings m)) (keep : ∀ j ∈ src, mu j = m j) :
    l.Loaded n (readings pub) (readings mu) := by
  have field (j : ℕ) (hj : j ∈ [59,60,61,62,63]) :
      frameField (readings pub) (readings mu) j = frameField (readings pub) (readings m) j :=
    congrArg Fin.val (keep _ (protect.fields j hj))
  exact ⟨(field 59 (by decide)).trans h.d,(field 60 (by decide)).trans h.axes,
    (field 61 (by decide)).trans h.bc,(field 62 (by decide)).trans h.power,
    (field 63 (by decide)).trans h.header,(congrArg Fin.val (keep _ protect.secondary.1)).trans h.blocks,
    (congrArg Fin.val (keep _ protect.secondary.2)).trans h.bank,fun j hj =>
      (congrArg Fin.val (keep _ (protect.powers j hj))).trans (h.powers j hj)⟩

/-- Symbol and grouping inputs left by the outer pair scan. -/
structure Entry {w n d : ℕ} (i : Fin (n+1)) (a b : Fin d) (r : Bank w) : Prop where
  /-- Zero word. -/
  zero : readings r 0 = 0
  /-- Unit word. -/
  one : readings r 1 = 1
  /-- Selected grouping coordinate. -/
  axis : readings r 4 = i.val
  /-- First symbol in this pass. -/
  left : readings r 14 = a.val
  /-- Second symbol in this pass. -/
  right : readings r 15 = b.val

/-- Restore the entry state from the actual persistent control words. -/
theorem Entry.keep {w n d : ℕ} {i : Fin (n+1)} {a b : Fin d} {r t : Bank w}
    (h : Entry i a b r) (keep : Keeps r t) : Entry i a b t :=
  ⟨(congrArg Fin.val (keep 0 (by decide))).trans h.zero,(congrArg Fin.val (keep 1 (by decide))).trans h.one,
    (congrArg Fin.val (keep 4 (by decide))).trans h.axis,(congrArg Fin.val (keep 14 (by decide))).trans h.left,
    (congrArg Fin.val (keep 15 (by decide))).trans h.right⟩

/-- Preserve the external control words through both a setup and a full native scatter loop. -/
theorem keeps_setup_loop {w : ℕ} {r u t : Bank w}
    (first : ∀ j, OwnedRowSetup.Held j → readings u j = readings r j)
    (second : ∀ j : Reg, j.val < 24 → j ≠ 18 → t j = u j) : Keeps r t := by
  intro j hj
  have props := (by decide : ∀ j : Reg, Control j → j.val < 24 ∧ j ≠ 18 ∧ OwnedRowSetup.Held j) j hj
  exact (second j props.1 props.2.1).trans (Fin.ext (first j props.2.2))

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
