import OAI.Computability.BorderVNP.CoverLorentzFrames
import OAI.Computability.BorderVNP.CoverHeckeDenominators

/-!
# Moving a frame with a finite tile-address table

A denominator-`7^a` motion can consult the fixed low residue of an input tile,
move one chosen representative, and multiply the resulting frame by an integral
correction. Its correction at output depth `d` depends only on the input
address at depth `d + 2a`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open BorderVNP.Hecke

/-- Right cosets of a congruence subgroup within the base lattice. -/
abbrev Tile (d : ℕ) := Cosets ((lattice d).subgroupOf (lattice 1))

/-- Tile address of a member of the base lattice. -/
noncomputable abbrev tile (d : ℕ) (x : lattice 1) : Tile d := coset _ x

/-- The right-coset address criterion, evaluated in the real matrix group. -/
theorem tile_eq_iff (d : ℕ) (x y : lattice 1) :
    tile d x = tile d y ↔ (y:SL) * (x:SL)⁻¹ ∈ lattice d := by
  exact Quotient.eq.trans QuotientGroup.rightRel_apply

/-- Congruence levels in the real matrix group are nested. -/
theorem lattice_antitone : Antitone lattice := by
  intro i j hij x hx
  obtain ⟨u,rfl⟩ := hx
  exact ⟨⟨u.val,Cover.gamma_antitone hij u.property⟩,rfl⟩

/-- The representative from the fixed low-level table. -/
noncomputable def lowRepresentative (a : ℕ) (x : lattice 1) : lattice 1 :=
  (tile (1+2*a) x).out

/-- A finite-residue correction before passage to its output address. -/
noncomputable def correction {g : SL} {a : ℕ} (hg : Clears g a) (x : lattice 1) : lattice 1 :=
  ⟨g * ((x:SL) * ((lowRepresentative a x : lattice 1):SL)⁻¹) * g⁻¹,
    conjugate_lattice hg 1 <| (tile_eq_iff _ _ _).mp
      (show tile (1+2*a) (lowRepresentative a x) = tile (1+2*a) x from Quotient.out_eq _)⟩

/-- The low-level motion and the deck correction implement the same motion as the full matrix. -/
theorem correction_formula {g : SL} {a : ℕ} (hg : Clears g a) (x : lattice 1) :
    (correction hg x : SL) * (g * (lowRepresentative a x : SL)) = g * (x:SL) := by
  change g * ((x:SL) * (lowRepresentative a x : SL)⁻¹) * g⁻¹ * (g * (lowRepresentative a x : SL)) = _
  group

/-- The correction at output depth `d` is determined by the input residue at `d+2a`. -/
theorem correction_residue {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d)
    (x y : lattice 1) (h : tile (d+2*a) x = tile (d+2*a) y) :
    tile d (correction hg x) = tile d (correction hg y) := by
  have hr := (tile_eq_iff _ _ _).mp h
  have hl : lowRepresentative a x = lowRepresentative a y :=
    congrArg Quotient.out ((tile_eq_iff _ _ _).mpr (lattice_antitone (by omega) hr))
  apply (tile_eq_iff _ _ _).mpr
  change (g*((y:SL)*(lowRepresentative a y : SL)⁻¹)*g⁻¹) *
      (g*((x:SL)*(lowRepresentative a x : SL)⁻¹)*g⁻¹)⁻¹ ∈ lattice d
  rw [hl, show (g*((y:SL)*(lowRepresentative a y : SL)⁻¹)*g⁻¹) *
      (g*((x:SL)*(lowRepresentative a y : SL)⁻¹)*g⁻¹)⁻¹ =
      g*((y:SL)*(x:SL)⁻¹)*g⁻¹ from by group]
  exact conjugate_lattice hg d hr

/-- A motion implemented on addresses alone. The output is the address of the
integral correction, to be composed with the finite precomputed low-residue table. -/
noncomputable def motionAddress {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d) :
    Tile (d+2*a) → Tile d :=
  Quotient.lift (fun x => tile d (correction hg x)) (fun x y h =>
    correction_residue hg hd x y (Quotient.sound h))

/-- Computing on the finite address agrees with the full representative. -/
theorem motionAddress_tile {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d) (x : lattice 1) :
    motionAddress hg hd (tile (d+2*a) x) = tile d (correction hg x) := rfl

/-- The motion on a whole frame descends to the advertised level. -/
noncomputable def moveFrame {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    Cosets (lattice (d+2*a)) → Cosets (lattice d) :=
  Quotient.lift (fun x => coset _ (g*x)) fun x y h => by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    rw [show g*y*(g*x)⁻¹ = g*(y*x⁻¹)*g⁻¹ from by group]
    exact conjugate_lattice hg d (QuotientGroup.rightRel_apply.mp h)

/-- The lifted frame law transports every point of a network by the very same motion. -/
theorem moveFrame_tile_frame {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ)
    (x : lattice 1) (frame : SL) :
    moveFrame hg d (coset _ ((x:SL)*frame)) =
    coset _ ((correction hg x : SL) * ((g*(lowRepresentative a x : SL))*frame)) := by
  change coset _ (g*((x:SL)*frame)) = _
  rw [← mul_assoc (correction hg x : SL), correction_formula, mul_assoc]

end Cover.Frame

end BorderVNP
end Computability
end OAI
