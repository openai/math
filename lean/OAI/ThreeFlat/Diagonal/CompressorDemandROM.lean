import OAI.ThreeFlat.Diagonal.CompressorDemandEval
import OAI.ThreeFlat.Diagonal.CompressorDemandOrdinal
import OAI.ThreeFlat.Diagonal.CompressorArcBridge

namespace OAI
/-! # The address and geometric tests read by the bounded demand loops -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Demand
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Computability.VPVNP.Compression
open scoped Fin.NatCast
variable {n w d c t l : ℕ} {B H : Type*} [AddCommGroup H]
variable (P : PackingData B H (BitWord t) (BitWord l) d c) (E : Codec B w c t l)
variable (base : B ↪ ℕ)
abbrev key := demandOrdinal P base (tagOrdinal t).toEmbedding (tagOrdinal l).toEmbedding
variable (data : Param → Word w) (m : Memory w) (vs : Fin n → Word w)

def layout (table tagCount laneCount : Formula n) (d c : ℕ) : WidthLayout n :=
  ⟨table,laneCount,tagCount,d,c⟩

theorem tag_cast {z : ℕ} (hz : z ≤ w) (u : BitWord z) :
    (((tagOrdinal z u).val : ℕ) : Word w) = tagWord hz u :=
  Fin.ext (Nat.mod_eq_of_lt (tagWord hz u).isLt)

variable {P E base data m vs}
variable (table tagCount laneCount : Formula n)

structure WidthReads (P : PackingData B H (BitWord t) (BitWord l) d c) (E : Codec B w c t l)
    (base : B ↪ ℕ) (data : Param → Word w) (m : Memory w) (vs : Fin n → Word w)
    (table tagCount laneCount : Formula n) (widths : Arc B H (BitWord t) (BitWord l) d c → ℕ) : Prop where
  baseWord : ∀ b, E.base b = (base b : Word w)
  tags : Formula.value data m vs tagCount = ((2^t : ℕ) : Word w)
  lanes : Formula.value data m vs laneCount = ((2^l*2^t*d*2^c : ℕ) : Word w)
  ordinalFits : ∀ a, key P base a < 2^w
  readWidth : ∀ a, m (Formula.value data m vs table+(key P base a : Word w)).val = (widths a : Word w)

variable {table tagCount laneCount}
variable {widths : Arc B H (BitWord t) (BitWord l) d c → ℕ}
variable (W : WidthReads P E base data m vs table tagCount laneCount widths)
include W

open scoped Fin.CommRing in
omit [AddCommGroup H] in
theorem address_code (a : Arc B H (BitWord t) (BitWord l) d c) (x : Placement.Position (Formula n)) (s : Formula n)
    (hp : x.map (Formula.value data m vs) = posCode P E (sourcePosition a)) (hs : (Formula.value data m vs) s = (a.1.2.val:Word w)) :
    (Formula.value data m vs) (physical (layout table tagCount laneCount d c) x s) = (key P base a : Word w) := by
  have ba := congrArg (fun z => z.site.base) hp
  have ta := congrArg (fun z => z.site.tag) hp
  have la := congrArg (fun z => z.site.lane) hp
  have bi := congrArg Placement.Position.bits hp
  have sl := congrArg Placement.Position.slot hp
  simp only [Placement.Position.map,Placement.Site.map,posCode,siteCode,sourcePosition] at ba ta la bi sl
  rw [physical_word]
  simp only [layout,ba,W.baseWord,ta,la,bi,sl,hs,W.tags,W.lanes,key,demandOrdinal_formula,
    Nat.cast_add,Nat.cast_mul,Equiv.toEmbedding_apply,← tag_cast]

omit [AddCommGroup H] in
theorem read_code (a : Arc B H (BitWord t) (BitWord l) d c) (x : Placement.Position (Formula n)) (s : Formula n)
    (hp : x.map (Formula.value data m vs) = posCode P E (sourcePosition a)) (hs : (Formula.value data m vs) s = (a.1.2.val:Word w)) :
    (Formula.value data m vs) (width (layout table tagCount laneCount d c) x s) = (widths a : Word w) := by
  rw [width_word,address_code W a x s hp hs]
  exact W.readWidth a

omit W in
theorem bit_code (g : ArcColumns (Formula n)) (R : ArcReads P E (g.map (Formula.value data m vs)) m)
    (x : Placement.Position (Formula n)) (a : Computability.VPVNP.Compression.Position B H (BitWord t) (BitWord l) c)
    (hp : x.map (Formula.value data m vs) = posCode P E a) :
    (Formula.value data m vs) (thickBit (formulaOps n) g.toColumns x) = 1 ↔ P.thick a := by
  rw [eval_thick,hp]
  exact thick_bit R.toGraphReads a

omit W in
theorem ends_code (g : ArcColumns (Formula n)) (R : ArcReads P E (g.map (Formula.value data m vs)) m)
    (dir : Bool) (x : Placement.Position (Formula n)) (i : Formula n)
    (a : Computability.VPVNP.Compression.Position B H (BitWord t) (BitWord l) c) (slot : Fin d)
    (hp : x.map (Formula.value data m vs) = posCode P E a) (hi : (Formula.value data m vs) i = (slot.val:Word w)) :
    (ends (formulaOps n) g d dir x i).map (Formula.value data m vs) =
      encodeEnds P E (if dir then P.actual.symm ((a.1,slot),a.2) else ((a.1,slot),a.2)) := by
  rw [eval_ends,hp,hi]
  cases dir
  · exact out_code R a slot
  · exact in_code R a slot

end ThreeFlat.Diagonal.CompressorPacking.Native.Demand

end OAI
