import OAI.Computability.BorderVNP.CubePhysicalTally
import OAI.Computability.BorderVNP.CubeMeanPacked
import OAI.Computability.BorderVNP.DiagonalNumberedTallies
import OAI.Computability.BorderVNP.DiagonalTaggedStep

/-!
# Actual fully assigned terms of the packed substituted row

A passing path fixes the public pack history, one private assignment per
bottom copy, and the surviving cell, singleton and cube bits. The final
subtype only checks zero-one factors and padding. A chosen scalar table
position with field value zero is retained.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening MvPolynomial BorderVNP.Cube BorderVNP.Cube.Physical
open scoped BigOperators Classical

set_option synthInstance.maxSize 900

variable {D n d b h K s exp : ℕ} {Team Param Gadget E : Type}
    [Fintype Team] [Fintype Param] [Fintype Gadget] [Field E]
    {P : Type} {bits : P → ℕ}

/-- Public layout for the cube packets of one attained history. -/
structure PacketPlacement (Team : Type) (n d b h K : ℕ) (N : Network D P bits) where
  /-- Cell names on the final site cover. -/
  Cell : Type
  [finiteCell : Fintype Cell]
  [decCell : DecidableEq Cell]
  /-- Assignment of every true host vertex to its cell. -/
  cell : N.Site → Cell
  /-- Number of padded cube blocks per label pair. -/
  blocks : ℕ
  /-- The occupied crossing-bit positions. -/
  slot : LiveBit N cell ↪ Slot n d blocks (h*b)
  /-- Actual cell labels from the chosen public scan. -/
  label : Cell → Label (n+1) d
  /-- Team assigned to each symbol after the declared selector and crossing
  lengths fix the group weights. -/
  team : (Packet n d blocks → Selector n K h) → Fin d → Team

attribute [instance] PacketPlacement.finiteCell PacketPlacement.decCell

namespace PacketPlacement

/-- Select the true packed intervals using the deterministic conditional
mean label algorithm executed by the native public scan. -/
noncomputable def ofMean {Cell A : Type} [Fintype Cell] [DecidableEq Cell] [Fintype A]
    (N : Network D P bits) (cell : N.Site → Cell)
    (recv : A → Cell) (dataWidth : A → ℕ) {m : ℕ} (ord : N.CrossingEdge cell ≃ Fin m)
    (cs : List Cell) (hn : cs.Nodup) (hc : cs.toFinset = Finset.univ)
    (hd : 0 < d) (hb : 0 < h*b) {W : ℝ} {M : ℕ}
    (budget : PackedLabelBudget N cell recv dataWidth W M (d^(n+1)))
    (team : (Packet n d (blocksFor W (h*b) (d^(n+1))) → Selector n K h) → Fin d → Team) :
    PacketPlacement Team n d b h K N :=
  ⟨Cell,cell,blocksFor W (h*b) (d^(n+1)),
    meanPackedEmbedding N cell recv dataWidth ord cs hn hc n d hd hb budget,
    meanPackedLabel N cell recv dataWidth cs n d hd,team⟩

variable {N : Network D P bits} (packet : PacketPlacement Team n d b h K N)
    (t : Tracked Team Param Gadget exp N) (x : Ports bits)
    (pos : TableEntry n b h K s → Gadget)

/-- A complete assignment with its actual zero-one and padding checks. -/
abbrev Passing := {a : Physical.Path N packet.cell n d packet.blocks b h K s //
  pathTag N packet.cell packet.slot t.tags x (fun _ => pos) a ≠ 0}

/-- Enumerate the exact subset of assigned bits that pass the local tests. -/
@[instance_reducible] noncomputable def passingFintype : Fintype (packet.Passing t x pos) := by
  unfold Passing
  infer_instance

/-- Exactly the exponents and selected table multiplicities read on this path. -/
noncomputable def tally (a : packet.Passing t x pos) : Tally Team Param Gadget exp :=
  pathTally packet.slot t.tags x (fun _ => pos) t.words packet.label (packet.team a.val.2.2.2.1) a.val

/-- Conditional on the public history and private bottom choices, the final
network value is the sum of the monomials read on its passing cube paths. -/
theorem value_eq_passing (values : Gadget → E) (valid : ValidTables (values ∘ pos)) :
    (t.valued values).tensor x =
      ∑ a : packet.Passing t x pos, monomial (packet.tally t x pos a).exponents
        ((packet.tally t x pos a).coefficient values) := by
  let tag := pathTag N packet.cell packet.slot t.tags x (fun _ => pos)
  refine (value_eq_physical_paths N packet.cell packet.slot t.tags x (fun _ => pos) values
    (fun _ => valid)).trans ?_
  trans ∑ a ∈ Finset.univ.filter (fun a => tag a ≠ 0), interpret values (tag a)
  · apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro a _ ha
    have hz : tag a = 0 := by
      by_contra hn
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    change interpret values (tag a) = 0
    rw [hz, map_zero]
  rw [Finset.sum_subtype (p := fun a => tag a ≠ 0) (Finset.univ.filter (fun a => tag a ≠ 0))
    (fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  exact Finset.sum_congr rfl fun a _ => interpret_path_tally packet.slot t.tags x (fun _ => pos)
    t.words packet.label (packet.team a.val.2.2.2.1) values a.val a.property

end PacketPlacement

namespace Assigned

variable {History Hidden Pin : Type} [Fintype History] [Fintype Hidden]
    {Port : History → Type} {width : (q : History) → Port q → ℕ}
    (N : (q : History) → Network D (Port q) (width q))
    (packet : ∀ q, PacketPlacement Team n d b h K (N q))
    (tags : ∀ q, Hidden → Tracked Team Param Gadget exp (N q))
    (pin : Pin → ∀ q, Ports (width q)) (pos : TableEntry n b h K s → Gadget)

/-- The index of one monomial occurrence in a complete substituted row.
Distinct paths remain distinct even when their gadget values coincide. -/
abbrev Path (i : Pin) := Σ q : History, Σ z : Hidden, (packet q).Passing (tags q z) (pin i q) pos

noncomputable instance pathFintype (i : Pin) : Fintype (Path N packet tags pin pos i) := by
  letI (q : History) (z : Hidden) : Fintype ((packet q).Passing (tags q z) (pin i q) pos) :=
    (packet q).passingFintype (tags q z) (pin i q) pos
  unfold Path
  infer_instance

/-- Read this actual row's term, still on the original parameter names. -/
noncomputable def term (i : Pin) (a : Path N packet tags pin pos i) : Tally Team Param Gadget exp :=
  (packet a.1).tally (tags a.1 a.2.1) (pin i a.1) pos a.2.2

/-- Actual terminal layouts, hidden choices and all passing bits form the
single finite path sum needed by the coefficient reader. -/
theorem sum_terms (values : Gadget → E) (valid : ValidTables (values ∘ pos)) (i : Pin) :
    (∑ q, ∑ z, ((tags q z).valued values).tensor (pin i q)) =
      ∑ a : Path N packet tags pin pos i, monomial (term N packet tags pin pos i a).exponents
        ((term N packet tags pin pos i a).coefficient values) := by
  let (q : History) (z : Hidden) : Fintype ((packet q).Passing (tags q z) (pin i q) pos) :=
    (packet q).passingFintype (tags q z) (pin i q) pos
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun z _ => (packet q).value_eq_passing (tags q z) (pin i q) pos values valid

end Assigned
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
