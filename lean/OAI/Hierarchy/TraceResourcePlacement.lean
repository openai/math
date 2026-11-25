import OAI.Hierarchy.TraceResourceHeaders
import OAI.Hierarchy.TraceParentScanner

namespace OAI
/-! # The registration scans in the fixed sectors of the grid interpreter -/
namespace Hierarchy.TraceAdmission.Resources
open ThreeFlat RAM
open scoped Classical

def gridRows (w lanes roots directions pairSpan band cap charges first : ℕ) : Parameters ℕ :=
  let β:=16*2^(32*w)
  let g:=2^(16*w)
  ⟨lanes,roots,directions,pairSpan,band,cap,β+2*g,β+3*g,β+4*g,β+5*g,charges,first⟩

/-- The matrix copied to 14J ends before the archive sector, including every
source column when the number of grid directions is zero. -/
theorem grid_output_end {w roots directions : ℕ} (hw : 1≤w)
    (rt : roots≤2^(3*w)) (ds : directions≤2^(3*w)) :
    14*2^(32*w)+roots*(directions+2)≤16*2^(32*w) := by
  let q:=2^(3*w)
  have two : 2≤q := Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤3*w by omega)
  have square : q^2≤2^(32*w) := by
    change (2^(3*w))^2≤2^(32*w)
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have cells : roots*(directions+2)≤2*q^2 := calc
    _ ≤ q*(2*q) := Nat.mul_le_mul rt (by change directions≤q at ds;omega)
    _ = _ := by ring
  omega

/-- The scan and output addresses use less than one scratch subbank per matrix.
The charge bank is the authenticated output of the preceding publisher. -/
theorem grid_room {w : ℕ} (hw : 7≤w) (lanes roots directions pairSpan band cap charges first stages : ℕ)
    (positive : 0<lanes) (lbound : lanes≤2^(3*w)) (rbound : roots≤2^(3*w))
    (dbound : directions≤2^(3*w)) (sbound : stages≤2^(3*w)) (pbound : pairSpan≤2^(3*w))
    (bbound : band≤2^(32*w)) (cbound : cap≤2^(32*w))
    (chargeEnd : charges+2*(first+roots)≤16*2^(32*w)+2^(16*w)) :
    let J:=2^(32*w)
    let g:=2^(16*w)
    let β:=16*J
    let H:=β+6*(2^w)^4+64
    let p:=gridRows w lanes roots directions pairSpan band cap charges first
    Parents.Layout (64*w) H (H+1) (β+g) lanes stages (β+64+44) ∧
    TraceIntervalScanner.Layout (64*w) ((β+g)+stages*lanes) p.heads p.links lanes roots ∧
    Room (64*w) (H+5) (H+6) p ∧ H+22≤β+g ∧ (14*J≤p.resources) ∧
    H+22<2^(64*w) := by
  intro J g β H p
  let q:=2^(3*w)
  let S:=(2^w)^4
  have qlarge : 2≤q := Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤3*w by omega)
  have small : 128*q^2≤g := by
    change 2^7*(2^(3*w))^2≤2^(16*w)
    rw [←pow_mul,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have sides : 128*S≤g := by
    change 2^7*(2^w)^4≤2^(16*w)
    rw [←pow_mul,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have inflate : 16*g≤J := by
    change 2^4*2^(16*w)≤2^(32*w)
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have all : 32*J<2^(64*w) := by
    change 2^5*2^(32*w)<2^(64*w)
    rw [←pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have bandFit : (directions+1)*band<2^(64*w) := calc
    _ ≤ (2*q)*J := Nat.mul_le_mul (by omega) bbound
    _ = 2^(1+3*w+32*w) := by dsimp [q,J];rw [pow_add,pow_add];rfl
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  have qsq : q≤q^2 := Nat.le_self_pow (by decide) _
  have laneRows : (stages+1)*lanes ≤ 2*q^2 := by
    calc
      _ ≤ (2*q)*q := Nat.mul_le_mul (by omega) lbound
      _ = _ := by ring
  have suffixRows : (lanes+1)*(directions+1)≤4*q^2 := by
    calc
      _ ≤ (2*q)*(2*q) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have matrix : roots*(directions+2) ≤ 2*q^2 := by
    calc
      _ ≤ q*(2*q) := Nat.mul_le_mul rbound (by omega)
      _ = _ := by ring
  have pairEnd : 2*((lanes+1)*pairSpan) ≤ 4*q^2 := by
    calc
      _ ≤ 2*((2*q)*q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) pbound)
      _ = _ := by ring
  have ss : 1≤S := Nat.pow_pos (Nat.two_pow_pos w)
  change lanes≤q at lbound
  change roots≤q at rbound
  change directions≤q at dbound
  change stages≤q at sbound
  change charges+2*(first+roots)≤β+g at chargeEnd
  change Parents.Layout (64*w) H (H+1) (β+g) lanes stages (β+64+44) ∧
    TraceIntervalScanner.Layout (64*w) ((β+g)+stages*lanes) (β+2*g) (β+3*g) lanes roots ∧
    Room (64*w) (H+5) (H+6) p ∧ H+22≤β+g ∧ 14*J≤β+5*g ∧ H+22<2^(64*w)
  have listRows : stages*lanes+lanes≤2*q^2 := by simpa [Nat.add_mul] using laneRows
  refine ⟨⟨positive,?_,?_,?_,?_⟩,⟨?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,bandFit,?_⟩,?_,?_,?_⟩
  all_goals dsimp only [p,gridRows,H,β,S,J,g] at *; omega

end Hierarchy.TraceAdmission.Resources

end OAI
