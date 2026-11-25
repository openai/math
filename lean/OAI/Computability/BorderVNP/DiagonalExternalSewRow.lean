import OAI.Computability.BorderVNP.DiagonalExternalSewIntervals

/-! # Four arithmetic candidates for a low-team exterior cable record

A candidate inspects the first or last position of a public site block. Its
other selector chooses the first or next block at the partner. All offsets
are computed from the two field starts and block endpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FourSlot

/-- Numerical fields for one position in the fixed four-slot exterior directory. -/
structure Row where
  /-- Only live candidates represent a shared cable. -/
  live : Bool
  /-- Processor owning both field ends. -/
  proc : ℕ
  /-- Rank of the other team in the low team's exterior field list. -/
  rank : ℕ
  /-- High team at the opposite end. -/
  partner : ℕ
  /-- Public site block at the high-team end. -/
  remote : ℕ
  /-- First bit in the shared field. -/
  first : ℕ
  /-- Length of the shared interval. -/
  width : ℕ
  deriving DecidableEq

/-- Field-relative bounds of the intersection of the two site blocks. -/
def bounds (A B g link site remote : ℕ) : ℕ × ℕ :=
  (max (site*g-A) (remote*g-B),min link (min (site*g+g-A) (remote*g+g-B)))

/-- Produce one sparse candidate without visiting any individual field bits
or enumerating the set of live cables. A repeated first/last field is emitted
only by the first probe. -/
def row (R r literal stride link g team site : ℕ) (right next : Bool) : Row :=
  let base := site*g
  let pos := base + if right then g-1 else 0
  let proc := pos/stride
  let col := pos%stride
  let rank := (col-literal)/link
  let A := proc*stride + literal + rank*link
  let B := proc*stride + literal + team*link
  let remote := (B+(base-A))/g + next.toNat
  let cut := bounds A B g link site remote
  let live := proc<r ∧ literal≤col ∧ rank<R ∧ team≤rank ∧
    (right=false ∨ ¬(A≤base ∧ base<A+link)) ∧ cut.1<cut.2
  ⟨decide live,proc,rank,rank+1,remote,cut.1,cut.2-cut.1⟩

/-- Closed expression for an actual cable's clipped endpoints. -/
theorem bounds_piece {F : Type} {start : F → Bool → ℕ} {g link : ℕ} (c : Pieces start g link) :
    bounds (start c.1 false) (start c.1 true) g link c.2.val.1 c.2.val.2 = pieceBounds start g c := rfl

/-- A block containing a field bit meets the field at one of its two probe positions. -/
theorem probe_mem {A g link site i : ℕ} (hg : 0 < g) (small : g ≤ link) (hi : i < link)
    (hit : (A+i)/g = site) :
    let base := site*g
    let right := decide (¬ (A≤base ∧ base<A+link))
    let x := base + if right then g-1 else 0
    A ≤ x ∧ x < A+link := by
  have h := (Nat.div_eq_iff hg).mp hit
  dsimp only
  split <;> rename_i hside
  · simp only [decide_eq_true_eq] at hside
    omega
  · simp only [decide_eq_true_eq,not_not] at hside
    omega

/-- Decoding the processor and exterior partner rank at a probe in its true
field returns the original ordinals. -/
theorem decode_probe {R r literal stride link : ℕ} (p : Fin r) (k : Fin R) (x : ℕ)
    (positive : 0 < link) (fit : literal+R*link ≤ stride)
    (mem : p.val*stride+literal+k.val*link ≤ x ∧ x < p.val*stride+literal+k.val*link+link) :
    x/stride = p.val ∧ literal ≤ x%stride ∧ (x%stride-literal)/link = k.val := by
  have hk := Nat.mul_le_mul_right link (Nat.succ_le_of_lt k.isLt)
  rw [Nat.succ_mul] at hk
  have hs : 0 < stride := by omega
  have hp : x/stride = p.val := (Nat.div_eq_iff hs).mpr (by omega)
  have hx := Nat.div_add_mod' x stride
  rw [hp] at hx
  refine ⟨hp,by omega,(Nat.div_eq_iff positive).mpr ?_⟩
  omega

/-- At a clipped local field the partner block is either the first or the next. -/
theorem remote_eq {A B g site i : ℕ} (hg : 0 < g) (hit : (A+i)/g = site) :
    (B+i)/g = (B+(site*g-A))/g ∨ (B+i)/g = (B+(site*g-A))/g+1 := by
  have ha := (Nat.div_eq_iff hg).mp hit
  let lo := site*g-A
  have low : lo ≤ i := by dsimp [lo]; omega
  have high : i < lo+g := by dsimp [lo]; omega
  have hd : i-lo < g := by omega
  have h := Packing.interval_two_blocks (B+lo) g g le_rfl ⟨i-lo,hd⟩
  dsimp only at h
  rwa [show B+lo+(i-lo) = B+i by omega] at h

/-- A raw slot whose intra-processor position lies at or after the literal
belongs to the link-sized field decoded by division. -/
theorem mem_decoded {literal stride link x : ℕ} (positive : 0 < link) (h : literal ≤ x%stride) :
    let A := (x/stride)*stride + literal + ((x%stride-literal)/link)*link
    A ≤ x ∧ x < A+link := by
  have hp := Nat.div_add_mod' x stride
  have hk := Nat.div_add_mod' (x%stride-literal) link
  have hm := Nat.mod_lt (x%stride-literal) positive
  omega

/-- The live interval test can be performed on an arbitrary candidate before
constructing its proof of occupancy. -/
theorem mem_bounds_iff {A B g link s t i : ℕ} (hg : 0 < g) (hi : i < link) :
    (bounds A B g link s t).1 ≤ i ∧ i < (bounds A B g link s t).2 ↔
      (A+i)/g = s ∧ (B+i)/g = t := by
  simp only [bounds,max_le_iff,lt_min_iff,Nat.div_eq_iff hg]
  omega

end Diagonal.ExternalSew.FourSlot

end BorderVNP
end Computability
end OAI
