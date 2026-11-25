import OAI.Hierarchy.DescentTerminalRowPlan
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Consecutive physical banks for the terminal row allocator -/

namespace Hierarchy.DescentTerminalRowArena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalSpanBook
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

/-- The existing book sources, dictionaries and frozen home array precede the
first newly allocated word. Bank capacities depend only on the row counts. -/
structure Arena where
  make ::
  start : ℕ
  sites : ℕ
  rows : ℕ
  packets : ℕ
  parts : Book.Parts
  countTable : Bank
  boundaries : ℕ
  modulo : Bank
  homes : Bank

namespace Arena
variable (A : Arena) {w : ℕ}

def stride := ProtocolRAMPurchaseSampler.span (2*A.sites+A.rows+A.packets+1)
def atBand (j : ℕ) := A.start+j*A.stride
def bank (j : ℕ) : Bank := ⟨A.atBand j,ProtocolRAMPurchaseSampler.bits (2*A.sites+A.rows+A.packets+1)⟩
def finish := A.atBand 22

theorem bank_size (i : ℕ) : (A.bank i).size=A.stride := rfl
theorem stride_min : 2*A.sites+A.rows+A.packets+1 < A.stride := ProtocolRAMPurchaseSampler.lt_span _
theorem band_mono {i j : ℕ} (ij : i ≤ j) : A.atBand i ≤ A.atBand j :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ ij) _
theorem band_after {i j : ℕ} (ij : i < j) : A.atBand i+A.stride ≤ A.atBand j := by
  have next := A.band_mono ij
  simpa only [atBand,Nat.succ_mul,Nat.add_assoc] using next
theorem start_le (j : ℕ) : A.start ≤ A.atBand j := Nat.le_add_right ..

theorem fits_band (fit : A.finish < 2^w) {i j : ℕ} (ij : i < j) (hi : j ≤ 22) :
    (A.bank i).Fits w (A.atBand j) := by
  have sep := A.band_after ij
  have endAt := (A.band_mono hi).trans_lt fit
  have size := A.stride_min
  change 0 < A.stride ∧ A.stride < 2^w ∧ A.atBand i+A.stride ≤ A.atBand j
  omega

theorem end_word (fit : A.finish < 2^w) {i n : ℕ} (i_lt : i < 22) (size : n ≤ A.stride) :
    A.atBand i+n < 2^w :=
  ((Nat.add_le_add_left size _).trans (A.band_after i_lt)).trans_lt fit

structure Lower (w : ℕ) : Prop where
  source (f : Fin 6) : (A.parts f).source.Fits w A.start
  weights (f : Fin 6) : (A.parts f).weights.Fits w A.start
  counts : A.countTable.Fits w A.start
  modulo : A.modulo.Fits w A.start
  homes : A.homes.Fits w A.start

theorem lower_band {b : Bank} (old : b.Fits w A.start) (j : ℕ) : b.Fits w (A.atBand j) :=
  ⟨old.1,old.2.1,old.2.2.trans (A.start_le j)⟩

/-- The first two bands contain the local parity and half-index dictionaries.
The remaining banks hold only the actual intermediate or output arrays. -/
def row : DescentTerminalRowPlan.Layout where
  parts := A.parts
  books := A.bank 2
  counts := A.bank 3
  countTable := A.countTable
  boundaries := A.boundaries
  cursors := A.bank 4
  siteFirst := A.bank 5
  siteLast := A.bank 6
  mark := ⟨A.bank 5,A.bank 1,A.bank 0,A.bank 7⟩
  markedScratch := A.atBand 8
  locate := ⟨A.bank 7,A.bank 9,A.bank 5,A.bank 6,A.bank 10,A.bank 11,A.bank 12⟩

theorem row_room (low : A.Lower w) (fit : A.finish < 2^w) :
    DescentTerminalRowPlan.Room A.row A.sites A.rows w := by
  have cap := A.stride_min
  have sites : A.sites ≤ A.stride := by omega
  have rows : A.rows ≤ A.stride := by omega
  have part (f : Fin 6) : (A.parts f).fetch.Fits w (A.atBand 2) :=
    ⟨A.lower_band (low.weights f) 2,A.lower_band (low.source f) 2,trivial⟩
  refine ⟨⟨part 0,part 1,part 2,part 3,part 4,part 5⟩,A.end_word fit (by decide : 2 < 22) sites,
    A.fits_band fit (by decide : 2 < 3) (by decide),A.lower_band low.counts 3,
    A.end_word fit (by decide : 3 < 22) sites,A.end_word fit (by decide : 4 < 22) sites,
    A.fits_band fit (by decide : 4 < 5) (by decide),A.fits_band fit (by decide : 3 < 5) (by decide),
    (Nat.add_le_add_left sites _).trans (A.band_after (by decide : 5 < 6)),
    A.end_word fit (by decide : 6 < 22) sites,?_,?_⟩
  · refine ⟨A.fits_band fit (by decide : 7 < 8) (by decide),rows,
      A.fits_band fit (by decide : 5 < 7) (by decide),
      A.fits_band fit (by decide : 1 < 7) (by decide),A.fits_band fit (by decide : 0 < 7) (by decide),?_,
      A.end_word fit (by decide : 8 < 22) (show 2*A.sites ≤ A.stride by omega)⟩
    have lane := A.fits_band fit (by decide : 0 < 8) (by decide)
    have half := A.fits_band fit (by decide : 1 < 8) (by decide)
    have first := A.fits_band fit (by decide : 5 < 8) (by decide)
    simp only [row,DescentTerminalHeaderScatter.stage,DescentTerminalHeaderScatter.bounded,
      MarkerBanks.startExpr,Expr.Fits,and_true,first,half,lane]
  · exact ⟨A.fits_band fit (by decide : 7 < 9) (by decide),A.fits_band fit (by decide : 5 < 9) (by decide),
      A.fits_band fit (by decide : 6 < 9) (by decide),A.fits_band fit (by decide : 9 < 10) (by decide),
      A.fits_band fit (by decide : 10 < 11) (by decide),A.fits_band fit (by decide : 11 < 12) (by decide),
      ⟨rows,rows,rows⟩,A.end_word fit (by decide : 12 < 22) rows⟩

/-- Install the two public indexed dictionaries once, leaving earlier physical
ports intact. The untouched remainder of both allocated bands is padding. -/
def mount (m : Memory w) : Memory w :=
  fillSegment (A.atBand 1) (2*A.sites) (fun x => (((x-A.atBand 1)/2 : ℕ) : Word w))
    (fillSegment (A.atBand 0) (2*A.sites) (fun x => (((x-A.atBand 0)%2 : ℕ) : Word w)) m)

theorem mount_before (m : Memory w) {x : ℕ} (old : x < A.start) : A.mount m x=m x := by
  have a := old.trans_le (A.start_le 0)
  have b := old.trans_le (A.start_le 1)
  simp [mount,fillSegment,not_le.mpr a,not_le.mpr b]

theorem mount_low (m : Memory w) {i : ℕ} (hi : i < 2*A.sites) :
    A.mount m (A.atBand 0+i)=((i%2 : ℕ) : Word w) := by
  have cap := A.stride_min
  have first := A.band_after (by decide : 0 < 1)
  have b : ¬A.atBand 1 ≤ A.atBand 0+i := by omega
  have a : A.atBand 0+i < A.atBand 0+2*A.sites := Nat.add_lt_add_left hi _
  simp [mount,fillSegment,b,a]

theorem mount_half (m : Memory w) {i : ℕ} (hi : i < 2*A.sites) :
    A.mount m (A.atBand 1+i)=((i/2 : ℕ) : Word w) := by
  have a : A.atBand 1+i < A.atBand 1+2*A.sites := Nat.add_lt_add_left hi _
  simp [mount,fillSegment,a]

theorem header_before (m : Memory w) {x : ℕ} (old : x < A.atBand 2) :
    DescentTerminalRowPlan.header A.row A.sites m x=m x := by
  have old3 := old.trans_le (A.band_mono (by decide : 2 ≤ 3))
  have old4 := old.trans_le (A.band_mono (by decide : 2 ≤ 4))
  have old5 := old.trans_le (A.band_mono (by decide : 2 ≤ 5))
  have old6 := old.trans_le (A.band_mono (by decide : 2 ≤ 6))
  simp only [DescentTerminalRowPlan.header,DescentTerminalRowPlan.allocated,DescentTerminalRowPlan.sized,
    DescentTerminalRowPlan.printed,DescentTerminalBinPackCheap.headerImage,DescentTerminalUniversalWrite.image,
    ProtocolRAM.image,fillSegment,row,bank,not_le.mpr old,not_le.mpr old3,not_le.mpr old4,
    not_le.mpr old5,not_le.mpr old6,false_and,ite_false]

theorem marker_fixed (fit : A.finish < 2^w) (m : Memory w)
    (lane : ∀ j < 2*A.sites,m (A.atBand 0+j)=((j%2 : ℕ) : Word w)) :
    A.row.mark.Fixed A.sites (DescentTerminalRowPlan.header A.row A.sites m) := by
  intro i j
  let q := DescentTerminalHeaderScatter.field i j
  have inside : q.val < 2*A.sites := q.isLt
  have cap := A.stride_min
  have span : q.val < A.stride := by omega
  have fitBank := A.fits_band fit (by decide : 0 < 2) (by decide)
  have wide := Fin.val_cast_of_lt (span.trans fitBank.2.1)
  have sep := A.band_after (by decide : 0 < 2)
  have left : A.atBand 0+q.val < A.atBand 2 := by omega
  change DescentTerminalRowPlan.header A.row A.sites m
    (A.atBand 0+(q.val : Word w).val%A.stride)=(j.val : Word w)
  rw [wide,Nat.mod_eq_of_lt span,A.header_before m left,lane q.val inside]
  have parity : q.val%2=j.val := by
    change (2*i.val+j.val)%2=j.val
    have laneBound : j.val < 2 := j.isLt
    omega
  exact congrArg (fun z : ℕ => (z : Word w)) parity

theorem mounted_fixed (fit : A.finish < 2^w) (m : Memory w) :
    A.row.mark.Fixed A.sites (DescentTerminalRowPlan.header A.row A.sites (A.mount m)) :=
  A.marker_fixed fit _ (fun _ hi => A.mount_low m hi)

end Arena
end
end Hierarchy.DescentTerminalRowArena

end OAI
