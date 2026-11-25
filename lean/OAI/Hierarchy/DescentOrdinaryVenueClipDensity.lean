import OAI.Hierarchy.DescentOrdinaryVenueClip
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # Occupancy of the ordinary venue pitches before and after the native gather -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentSIMDLookup
noncomputable section

private theorem round_to_radix (x r : ℕ) (positive : 0<r) (fits : r≤x) :
    x≤2*((x/r)*r) := by
  have used : r≤(x/r)*r := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right r (Nat.div_pos fits positive)
  have rem := Nat.mod_lt x positive
  have cover := Nat.mod_add_div x r
  rw [Nat.mul_comm r (x/r)] at cover
  omega

variable (c : Clip)

/-- Units per working lane for the two rounded old pitches and the local lookup. -/
def densityUnit (panelFull actorFull : ℕ) :=
  max (2*panelFull) (max (2*actorFull) (8*c.unit))

theorem working_density (panelFull actorFull : ℕ) (panel : c.radix≤c.panelPitch)
    (actor : c.radix≤c.actorPitch) (wide : 4*c.unit*c.radix≤c.payload)
    (panelDense : c.payload≤c.panelPitch*panelFull)
    (actorDense : c.payload≤c.actorPitch*actorFull) :
    c.payload≤c.working*c.densityUnit panelFull actorFull := by
  let d:=c.densityUnit panelFull actorFull
  let r:=c.radix
  have rad : 0<r := Nat.two_pow_pos _
  have old {x f : ℕ} (fit : r≤x) (dense : c.payload≤x*f) (short : 2*f≤d) :
      c.payload≤((x/r)*r)*d := calc
    c.payload ≤ x*f := dense
    _ ≤ (2*((x/r)*r))*f := Nat.mul_le_mul_right _ (round_to_radix x r rad fit)
    _ = ((x/r)*r)*(2*f) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ short
  have panelFit := old panel panelDense (show 2*panelFull≤d from le_max_left ..)
  have actorFit := old actor actorDense (show 2*actorFull≤d from
    (le_max_left ..).trans (le_max_right ..))
  have unitPos : 0<c.unit := (show 0<c.localUnit from (by decide : 0<2).trans_le (le_max_left ..)).trans_le (le_max_left ..)
  have localWide : 2*((2*c.unit)*r)≤c.payload := by
    calc _ = 4*c.unit*r := by ring
         _ ≤ _ := wide
  let t:=lanes c.payload ((2*c.unit)*r)
  have occ:= (occupancy c.payload ((2*c.unit)*r) (Nat.mul_pos (Nat.mul_pos (by decide) unitPos) rad) localWide).2
  have native : c.payload≤(t*r)*d := calc
    c.payload ≤ 4*t*((2*c.unit)*r) := occ
    _ = (t*r)*(8*c.unit) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ ((le_max_right (2*actorFull) (8*c.unit)).trans (le_max_right ..))
  have takeMin {x y : ℕ} (a : c.payload≤(x*r)*d) (b : c.payload≤(y*r)*d) :
      c.payload≤(min x y*r)*d := by
    rcases le_total x y with h|h
    · simpa only [min_eq_left h] using a
    · simpa only [min_eq_right h] using b
  exact takeMin panelFit (takeMin actorFit native)

theorem post_density (panelFull actorFull : ℕ) (panel : c.radix≤c.panelPitch)
    (actor : c.radix≤c.actorPitch) (wide : 4*c.unit*c.radix≤c.payload)
    (panelDense : c.payload≤c.panelPitch*panelFull)
    (actorDense : c.payload≤c.actorPitch*actorFull) :
    c.payload≤c.postPitch*(c.radix*c.densityUnit panelFull actorFull) := by
  simpa only [working, Nat.mul_assoc] using c.working_density panelFull actorFull panel actor wide panelDense actorDense

theorem working_volume (H G panelFull actorFull : ℕ) (panel : c.radix≤c.panelPitch)
    (actor : c.radix≤c.actorPitch) (wide : 4*c.unit*c.radix≤c.payload)
    (panelDense : c.payload≤c.panelPitch*panelFull)
    (actorDense : c.payload≤c.actorPitch*actorFull) :
    (H*chunks G c.working)*c.payload ≤ H*c.payload+H*G*c.densityUnit panelFull actorFull :=
  DescentDatedSeedStartup.chunk_work _ _ _ _ _
    (c.working_density panelFull actorFull panel actor wide panelDense actorDense)

theorem post_volume (H G panelFull actorFull : ℕ) (panel : c.radix≤c.panelPitch)
    (actor : c.radix≤c.actorPitch) (wide : 4*c.unit*c.radix≤c.payload)
    (panelDense : c.payload≤c.panelPitch*panelFull)
    (actorDense : c.payload≤c.actorPitch*actorFull) :
    (H*chunks G c.postPitch)*c.payload ≤ H*c.payload+H*G*(c.radix*c.densityUnit panelFull actorFull) :=
  DescentDatedSeedStartup.chunk_work _ _ _ _ _
    (c.post_density panelFull actorFull panel actor wide panelDense actorDense)

/-- A previous donor that issued both banks with its full register pitch pays
eight times the larger of its original short width and the new lookup width. -/
theorem donor_density (oldAmount : ℕ) (pos : 0<oldAmount) (fits : 2*oldAmount≤c.payload)
    (p : c.panelPitch=lanes c.payload oldAmount) (a : c.actorPitch=lanes c.payload oldAmount)
    (panel : c.radix≤c.panelPitch) (actor : c.radix≤c.actorPitch) (wide : 4*c.unit*c.radix≤c.payload) :
    c.payload≤c.working*(8*max oldAmount c.unit) := by
  have full := (occupancy c.payload oldAmount pos fits).2
  have panelDense : c.payload≤c.panelPitch*(4*oldAmount) := by
    rw [p]
    calc
      c.payload ≤ 4*lanes c.payload oldAmount*oldAmount := full
      _ = _ := by ring
  have actorDense : c.payload≤c.actorPitch*(4*oldAmount) := by simpa only [a,p] using panelDense
  apply (c.working_density _ _ panel actor wide panelDense actorDense).trans
  apply Nat.mul_le_mul_left
  have old : 2*(4*oldAmount)≤8*max oldAmount c.unit := by
    calc _ = 8*oldAmount := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ (le_max_left ..)
  exact max_le old (max_le old (Nat.mul_le_mul_left _ (le_max_right ..)))

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI
