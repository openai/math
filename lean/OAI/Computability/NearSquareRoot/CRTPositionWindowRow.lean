import OAI.Computability.NearSquareRoot.CRTControlledReservePack
import OAI.Computability.NearSquareRoot.CRTControlledReserveNative
import OAI.Computability.NearSquareRoot.CRTPositionProgramTableBreeze
import OAI.Computability.NearSquareRoot.CRTPositionClock
import OAI.Computability.NearSquareRoot.CRTControlledRowControls

/-! # A uniform physical permutation of the interior bits of one row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom PositionProgram
noncomputable section

/-- One universal row instance. The record data never appears in its header. -/
structure Window where
  k : ℕ
  lo : ℕ
  hi : ℕ
  w : ℕ
  pos : 0 < w
  fit : lo + hi ≤ k
  perm : Equiv.Perm (Fin (k-lo-hi))
  record : Block 2 k → Fin w → Bead

namespace Window

def mid (x : Window) := x.k-x.lo-x.hi

def header (x : Window) :=
  (tally x.hi, tally x.mid, tally x.lo, Reflections.table x.perm)

def regime : Regime Window where
  scale := k
  header x := send (header x)
  gauge := by
    refine ⟨2,13,fun x => ?_⟩
    change size (header x) ≤ _
    simp only [header,size_prod,size_tally,tally_length]
    have ht := Reflections.table_size x.perm
    have fit := x.fit
    have hm : x.mid ≤ x.k := by unfold mid; omega
    have e : 2*(x.mid+1)^2 ≤ 2*(x.k+1)^2 := by gcongr
    change size (Reflections.table x.perm) ≤ 2*(x.mid+1)^2 at ht
    nlinarith

theorem hasHeader : regime.Has header := regime.self

theorem hasHi : regime.Has (tally ∘ hi) := hasHeader.ez Easy.fst
theorem hasMid : regime.Has (tally ∘ mid) := hasHeader.ez (Easy.snd.compose Easy.fst)
theorem hasLo : regime.Has (tally ∘ lo) := hasHeader.ez (Easy.snd.compose (Easy.snd.compose Easy.fst))

theorem hasPerm : regime.Has (fun x => Reflections.table x.perm) :=
  hasHeader.ez (Easy.snd.compose (Easy.snd.compose Easy.snd))

def outer (x : Window) : Adopt ((line 2 x.hi).cart (line 2 (x.mid+x.lo))) (line 2 x.k) :=
  prefixView (by have := x.fit; unfold mid; omega)

def routed (x : Window) : Equiv.Perm (Block 2 x.k) :=
  ReserveTile.lift x.fit (flatBitPullback x.perm)

abbrev Row := (x : Window) × Block 2 x.hi
abbrev rowRegime := fixedRowRegime regime hi hasHi

def src (z : Row) (b : Block 2 (z.1.mid+z.1.lo)) : Fin z.1.w → Bead :=
  z.1.record ((outer z.1).cast (z.2,b))

def dst (z : Row) (b : Block 2 (z.1.mid+z.1.lo)) : Fin z.1.w → Bead :=
  z.1.record (routed z.1 ((outer z.1).cast (z.2,b)))

def natural (z : Row) := Series.natural z.1.w

private theorem dst_chunk (z : Row) (a : Block 2 z.1.mid) (b : Block 2 z.1.lo) :
    dst z ((prefixView rfl).cast (a,b)) =
      src z ((prefixView rfl).cast (flatBitPullback z.1.perm a,b)) :=
  congrArg z.1.record (ReserveTile.lift_view z.1.fit (flatBitPullback z.1.perm) z.2 a b)

private def wide (z : Row) := (line 2 z.1.lo).cart (natural z)

private def data (z : Row) (a : Block 2 z.1.mid) (j : Block 2 z.1.lo × Fin z.1.w) : Bead :=
  src z ((prefixView rfl).cast (a,j.1)) j.2


private theorem groupedBreeze {ρ : ℝ} (hρ : 1/2 < ρ) :
    Breeze (fun z : Row => positionRate ρ z.1.mid) rowRegime (fun z => 2^z.1.mid)
      (fun z => 2^z.1.lo*z.1.w)
      (together rowRegime.header (ReservePack.grouped natural (fun z => z.1.mid) (fun z => z.1.lo) src))
      (ReservePack.grouped natural (fun z => z.1.mid) (fun z => z.1.lo) dst) := by
  have inv := ReserveProgram.inverseTable_has (fun x : Window => x.perm) hasPerm
  have ready : rowRegime.Has (fun z : Row => Reflections.table z.1.perm.symm) := fixedRowGlobal hi hasHi inv
  have bound (z : Row) : (wide z).count ≤ 2^z.1.lo*z.1.w := by
    rw [wide,Series.count_cart,lineSize,natural,Series.count_natural]
  have base := tableScheduleBreeze hρ (fun z : Row => z.1.mid) (fun z => 2^z.1.lo*z.1.w)
    (fun z => z.1.perm.symm) ready (tableWidth_dom ready) wide bound data
  have dest : cloth (fun z : Row => line 2 z.1.mid) wide
      (fun z a => data z ((permuteNative z.1.perm.symm).symm a)) =
      ReservePack.grouped natural (fun z => z.1.mid) (fun z => z.1.lo) dst := by
    funext z
    have eq (a : Block 2 z.1.mid) : data z ((permuteNative z.1.perm.symm).symm a) =
        fun j => dst z ((prefixView rfl).cast (a,j.1)) j.2 := by
      funext j
      rw [permuteNative_symm_pullback,Equiv.symm_symm,dst_chunk]
      rfl
    change stripe _ (fun a => strip _ (data z _)) = stripe _ _
    simp only [eq]
    rfl
  have source : ReservePack.grouped natural (fun z => z.1.mid) (fun z => z.1.lo) src =
      cloth (fun z : Row => line 2 z.1.mid) wide data := by rfl
  rw [source, ← dest]
  simp only [lineSize] at base
  convert! base using 3

theorem rawBreeze {ρ : ℝ} (hρ : 1/2 < ρ) :
    Breeze (fun z : Row => positionRate ρ z.1.mid) rowRegime (fun z => 2^z.1.mid)
      (fun z => 2^z.1.lo*z.1.w)
      (together rowRegime.header (ReservePack.raw natural (fun z => z.1.mid) (fun z => z.1.lo) src))
      (ReservePack.raw natural (fun z => z.1.mid) (fun z => z.1.lo) dst) := by
  have hm := fixedRowGlobal hi hasHi hasMid
  have hb := fixedRowGlobal hi hasHi hasLo
  exact ReservePack.around natural (fun z => z.1.mid) (fun z => z.1.lo) src
    (fun z => z.1.w) (fun z => z.1.pos) (fun z => by simp [natural])
    hm hb dst rowRegime.self 1 (fun _ _ _ => le_rfl) (groupedBreeze hρ)

end Window
end
end Controlled.PositionRows

end NearSquareRoot
end Computability
end OAI
