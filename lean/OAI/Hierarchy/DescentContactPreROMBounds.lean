import OAI.Hierarchy.DescentContactPreROMLayout
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Address bounds for the contact marker's three finite dictionary families -/
namespace Hierarchy.DescentContactPreROM.Layout
open Filter DescentDatedAddressBook DescentSIMDLookup
open DescentResetCandidateDate
variable {ι : ℕ → Type*}

/-- Moving the first column translates the raw candidate, projection, pitch,
marker dictionary and scratch segments by the same number of words. -/
theorem translate (A : Layout) (base : ℕ) :
    ({A with first := base} : Layout).endAddress =
      base + ({A with first := 0} : Layout).endAddress := by
  simp [endAddress, scratchBase, markerBase, pitchBase, projectionBase, old,
    DescentContactProbeBook.stop, Shape.endAddress, Shape.base, Shape.scratch, Shape.size,
    Shape.width, Shape.stride, Shape.rowBits, Shape.rows, oldFields, rows, slab,
    jobs, sockets, donors, half, viewBits, viewCount, Nat.add_assoc]

/-- Address inputs for the original contact publisher, measured before any layout
is placed. The width bounds concern the arguments of the three actual lookup tables. -/
structure ScalarRoom (P : ∀ h, ι h → Layout) : Prop where
  hosts : Bounded (fun h i => (P h i).hosts)
  shapes : Bounded (fun h i => (P h i).shapes)
  chunks : Bounded (fun h i => DescentSIMDLookup.chunks (P h i).groups (P h i).batch)
  lows : Bounded (fun h i => (P h i).lows)
  cap : Bounded (fun h i => (P h i).cap)
  sockets : Bounded (fun h i => (P h i).sockets)
  oldFields : Bounded (fun h i => (P h i).oldFields)
  oldWidth : ∃ K : ℕ, ∀ᶠ h : ℕ in atTop, ∀ i,
    (P h i).old.width (P h i).oldFields (P h i).fieldBits ≤ K*h
  projectionWidth : ∃ K : ℕ, ∀ᶠ h : ℕ in atTop, ∀ i,
    ((P h i).viewBits*1+(P h i).viewBits)*(P h i).batch ≤ K*h
  markerWidth : ∃ K : ℕ, ∀ᶠ h : ℕ in atTop, ∀ i,
    ((P h i).fieldBits*8+(P h i).fieldBits)*(P h i).batch ≤ K*h

private theorem book (N : ℕ) (b H G M : ∀ h, ι h → ℕ)
    (rows : Bounded (fun h i => H h i * chunks (G h i) (M h i)))
    (width : ∃ K : ℕ, ∀ᶠ h : ℕ in atTop, ∀ i, (b h i*N+b h i)*M h i ≤ K*h) :
    Bounded (fun h i => DescentContactProbeBook.step N (b h i) (H h i) (G h i) (M h i)) := by
  obtain ⟨K, le⟩ := width
  have both := Bounded.pow_of_linear le
  have inputs : Bounded (fun h i => 2^((b h i*N)*M h i)) :=
    both.of_le fun h i => Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  exact (((Bounded.const 1).add ((Bounded.const N).mul ((Bounded.const 2).mul both))).add
    inputs).add rows.padded

/-- The complete physical word count at origin zero has a single date-independent
address exponent. It includes both domain tables of every printed gather. -/
theorem rate (P : ∀ h, ι h → Layout) (R : ScalarRoom P) :
    Bounded (fun h i => ({P h i with first := 0} : Layout).endAddress) := by
  let H := fun h i => (P h i).hosts
  let S := fun h i => (P h i).shapes
  let G := fun h i => (P h i).groups
  let M := fun h i => (P h i).batch
  have rawRows : Bounded (fun h i => H h i * chunks (G h i) (M h i)) := R.hosts.mul R.chunks
  have workers : Bounded (fun h i => H h i * S h i) := R.hosts.mul R.shapes
  have contactRows := workers.mul R.chunks
  have halfRoom : Bounded (fun h i => (P h i).half) := R.lows.mul ((Bounded.const 2).mul R.cap)
  have views : Bounded (fun h i => (P h i).viewCount) :=
    (Bounded.const 2).mul (halfRoom.mul (Bounded.const 2))
  have jobsRoom : Bounded (fun h i => (P h i).jobs) := R.sockets.mul ((Bounded.const 2).mul halfRoom)
  obtain ⟨K, rawWidth⟩ := R.oldWidth
  have imageRoom := ((R.oldFields.mul (Bounded.const 2)).add (Bounded.const 2)).mul
    (Bounded.pow_of_linear rawWidth)
  have raw := (((Bounded.const 0).add imageRoom).add rawRows.padded).add
    ((Bounded.const 1).mul rawRows.padded)
  have projection := book 1 (fun h i => (P h i).viewBits) H G M rawRows R.projectionWidth
  have pitch := (Bounded.const 5).mul (workers.max' contactRows).padded
  have marked := book 8 (fun h i => (P h i).fieldBits) (fun h i => H h i*S h i) G M
    contactRows R.markerWidth
  exact (((raw.add (views.mul projection)).add pitch).add (R.sockets.mul marked)).add
    (jobsRoom.mul ((Bounded.const 2).mul contactRows.padded))

end Hierarchy.DescentContactPreROM.Layout

end OAI
