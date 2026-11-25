import OAI.ThreeFlat.RAM.TickMemoryLayout
import OAI.ThreeFlat.Diagonal.TickScratchRegion
import OAI.ThreeFlat.RAM.TickReadFields

namespace OAI
/-! # Physical memory shared by the compressor navigation and slot preparation -/

namespace ThreeFlat.RAM.TickPhysicalABI

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace Diagonal.TickChronology
open scoped Fin.CommRing

/-- The first eleven scratch regions belong to the physical tick. Region 11
contains the compact work, owner, stage directory, and root directory in order.
Regions 12 onward are temporary storage available for selected subtrees. -/
def layout (u a teams capacity oldAux newAux oldChunk newChunk initial : ℕ) : TickActiveROM.Layout where
  bits := a
  teams := teams
  capacity := capacity
  oldAux := oldAux
  newAux := newAux
  oldChunk := oldChunk
  newChunk := newChunk
  zero := initial
  control := base u 0
  clockWords := base u 1
  bounds := base u 2
  auxRequest := base u 3
  chunkRequest := base u 4
  intervalTable := base u 5
  intervalCount := base u 6
  intervalMap := base u 7
  groupCounts := base u 8
  metadata := base u 9
  lut := base u 10

/-- All visible segment addresses are computed from the physical field
concatenation at word offset two, including the immutable initial region beyond
the final input bit. -/
def mounted (u a teams capacity q nt ns np : ℕ) : TickActiveROM.Layout :=
  let first := 2+q+nt+ns+np
  layout u a teams capacity first (first+a) (first+2*a) (first+3*a)
    (2+Diagonal.ApproximateImage.pinCount q nt ns np a)

def directory (u : ℕ) (i : Fin 4) := base u 11 + i.val*(stride u/4)

structure NavigationHeader where
  buckets : ℕ
  roots : ℕ
  work : ℕ
  stages : ℕ

def NavigationHeader.words (h : NavigationHeader) (u : ℕ) : Fin 8 → ℕ :=
  ![h.buckets,h.roots,h.work,directory u 0,directory u 1,directory u 2,h.stages,directory u 3]

def NavigationHeader.stored {w : ℕ} (h : NavigationHeader) (u : ℕ) (m : Memory w) :=
  ∀ i : Fin 8, m (base u 6 + i.val) = ((h.words u i : ℕ) : Word w)

/-- The histogram parser and all later stage arithmetic read the marker-selected
endpoint. The first raw history bit follows the marker at offset zero. -/
def rawHistory (A : TickActiveROM.Layout) (ph : Phase) :=
  (if ph = .opening then A.newAux else A.oldAux)+1

def Inputs {w : ℕ} (A : TickActiveROM.Layout) (clock : Clock) (m : Memory w)
    (team step : ℕ) : Prop :=
  (∀ i : Fin 4, m (A.control+i.val) =
    (![team,step,(clock.phase step).tag,1] i : ℕ)) ∧
  (∀ i : Fin 4, m (A.clockWords+i.val) =
    (TickClockWords.values clock A.bits A.teams team step i : ℕ))

theorem directory_apart {u : ℕ} (i j : Fin 4) (ij : i.val < j.val) :
    directory u i + stride u/4 ≤ directory u j := by
  unfold directory
  have := Nat.mul_le_mul_right (stride u/4) ij
  rw [Nat.succ_mul] at this
  omega

@[simp] theorem history_opening (A : TickActiveROM.Layout) :
    rawHistory A .opening = A.newAux+1 := rfl

theorem history_later (A : TickActiveROM.Layout) {ph : Phase} (hp : ph ≠ .opening) :
    rawHistory A ph = A.oldAux+1 := by simp [rawHistory,hp]

end ThreeFlat.RAM.TickPhysicalABI

end OAI
