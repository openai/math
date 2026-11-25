import OAI.Computability.BorderVNP.PackedGridRepeat
import OAI.Computability.BorderVNP.DiagonalTaggedStep

/-! # Public external port intervals for the bottom bundle

Fine external bits are injected into named lanes of a few public bundle ports. Unused
external lanes may be supplied arbitrarily. The topology, private tensor contraction
and selected unary use bits of the original network are all preserved on the live lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped Classical
variable {D : ℕ} {P A : Type} (N : Network D P (fun _ => 1)) (width : A → ℕ)
variable (lane : P ↪ (a : A) × Fin (width a)) (owner : A → N.Site)

/-- Public interval ports attached to their owning sites. The internal cables and boxes
of the physical network retain their actual indices. -/
abbrev packExternal : Network D A width where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src := N.src
  dst := N.dst
  width := N.width
  attach := owner
  position := N.position
  in_ball := N.in_ball

/-- Recover the original fine bit assignments from their specified group and lane. -/
def readExternal (x : Ports width) : Ports (fun _ : P => 1) := fun p _ => x (lane p).1 (lane p).2

/-- A site may read each of its old external bits at its numbered location in a
public word owned by that same site. -/
def externalTables (aligned : ∀ p, owner (lane p).1 = N.attach p) {R : Type*} (t : N.Tables R) :
    (N.packExternal width owner).Tables R := fun v a x =>
  t v a (fun p _ => x ⟨(lane p.val).1,(aligned p.val).trans p.property⟩ (lane p.val).2)

/-- Exact value on all grouped external inputs. In particular, irrelevant positions
never contribute a multiplicity to the contraction. -/
theorem value_packExternal (aligned : ∀ p, owner (lane p).1 = N.attach p)
    {R : Type*} [CommSemiring R] (table : N.Tables R) (x : Ports width) :
    (N.packExternal width owner).value (N.externalTables width lane owner aligned table) x =
      N.value table (readExternal width lane x) := rfl

/-- Put copy-number slices side by side in each physical group word. -/
def externalCopyEquiv (b : ℕ) : Fin b × ((a : A) × Fin (width a)) ≃
    ((a : A) × Fin (b*width a)) where
  toFun p := ⟨p.2.1,finProdFinEquiv (p.1,p.2.2)⟩
  invFun p := ((finProdFinEquiv.symm p.2).1,⟨p.1,(finProdFinEquiv.symm p.2).2⟩)
  left_inv := by rintro ⟨i,a,k⟩; simp
  right_inv := by rintro ⟨a,k⟩; exact congrArg (Sigma.mk a) (finProdFinEquiv.apply_symm_apply k)

/-- Live fine ports in all copies are still injected, even with partially empty groups. -/
def repeatLane (b : ℕ) : Fin b × P ↪ ((a : A) × Fin (b*width a)) :=
  ((Function.Embedding.refl _).prodMap lane).trans (externalCopyEquiv width b).toEmbedding

/-- Grouping every copy into the same interval port yields one public external
descriptor of width `b*width a`, exactly like the `b` slices of each internal cable. -/
abbrev groupedRepeat (b : ℕ) : Network D A (fun a => b*width a) :=
  (N.repeatGrid b).packExternal (fun a => b*width a) owner

/-- The actual external descriptor charge at each site, with a single charge for each
interval rather than a charge per live bit. -/
theorem groupedRepeat_records [Fintype A] (b : ℕ) (expanded : Bool) (prior payload : N.Site → ℕ)
    (test : N.Site → Prop) :
    Shortening.localRecords (N.groupedRepeat width owner b) expanded prior payload test =
      Shortening.testedWidth (fun v => Shortening.boxCost expanded (prior v) (payload v)) test +
      Shortening.testedWidth (fun e => Shortening.recordCost expanded (b*N.width e)) (fun e => test (N.src e)) +
      Shortening.testedWidth (fun e => Shortening.recordCost expanded (b*N.width e)) (fun e => test (N.dst e)) +
      Shortening.testedWidth (fun a => Shortening.recordCost expanded (b*width a)) (fun a => test (owner a)) := rfl

/-- The bottom bundle computes independent tensor copies after their external lanes
are concatenated. Unused positions in any group word can have any values. -/
theorem value_groupedRepeat (aligned : ∀ p, owner (lane p).1 = N.attach p) (b : ℕ)
    {R : Type*} [CommSemiring R] (table : N.Tables R) (x : Ports (fun a => b*width a)) :
    (N.groupedRepeat width owner b).value
      ((N.repeatGrid b).externalTables _ (repeatLane width lane b) owner
        (fun p => aligned p.2) (N.repeatTables b table)) x =
      ∏ i : Fin b, N.value table (fun p _ => x (lane p).1 (finProdFinEquiv (i,(lane p).2))) :=
  N.value_repeatGrid b table (readExternal _ (repeatLane width lane b) x)

end Crossing.Network

namespace Diagonal.CellEntries

open Crossing
variable {D b : ℕ} {P A : Type} {N : Network D P (fun _ => 1)}
variable {Team Param Gadget : Type*} [Fintype Team] [Fintype Param]
variable (width : A → ℕ) (lane : P ↪ (a : A) × Fin (width a)) (owner : A → N.Site)
variable (aligned : ∀ p, owner (lane p).1 = N.attach p)

/-- External interval grouping only changes the argument reader of the same local
tables. Every selected power retains its original host site and fine bit value. -/
def PowerWords.packExternal {tags : N.Tables (Entry Param Gadget)}
    (words : PowerWords Team Param Gadget b N tags) :
    PowerWords Team Param Gadget b (N.packExternal width owner)
      (N.externalTables width lane owner aligned tags) where
  site := words.site
  selected := N.externalTables width lane owner aligned words.selected
  located := fun v a _ w hw => words.located v a _ w hw
  exact := fun v a _ => words.exact v a _

/-- Transport the tagged physical term with its original named uses to the interval
port layout. -/
def Tracked.packExternal (t : Tracked Team Param Gadget b N) :
    Tracked Team Param Gadget b (N.packExternal width owner) :=
  ⟨N.externalTables width lane owner aligned t.tags,t.words.packExternal width lane owner aligned⟩

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
