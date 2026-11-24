import OAI.Computability.VPVNP.CompressorShrinkWidthFootprints
import OAI.Computability.VPVNP.CompressorShrinkBundleWalk

/-!
# External accesses of the last five dense shrinking visits

The width scatter, both prefixes, the AB pass and the absolute-ID scatter
have increasing ordinal cursors. Their concrete read and write intervals
are derived from the shrinking run's allocated physical columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBundlePlan.Scheduled

open BurstRAM Compression Compression.PackingData BundleWidthScatter ShrinkWidthFootprints
open SlotFillFootprint (InColumn)
open scoped Fin.CommRing Classical
open private offset_lt from OAI.Computability.VPVNP.CompressorRecordsBundleWidthScatter

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : ShrinkInput.Run X T start m)

local notation "Z" => ShrinkInput.plan X start
local notation "N" => Fintype.card X.Base
local notation "A" => ShrinkRankSpace.Shape.A (ShrinkInput.plan X start)
local notation "B" => ShrinkRankSpace.Shape.B (ShrinkInput.plan X start)
local notation "Q" => ShrinkRankSpace.Shape.Q (ShrinkInput.plan X start)
local notation "q" => ShrinkRankSpace.Shape.collectBank (ShrinkInput.plan X start) w
local notation "rankWord" => Fin.ofNat (2^w) (ShrinkRankSpace.Shape.ranks (ShrinkInput.plan X start))
local notation "W" => ShrinkInput.widthBase X start
local notation "s" => ShrinkWidthArena.scatterBank T q rankWord W
local notation "t" => ShrinkWidthArena.prefixBank X T q rankWord W false
local notation "u" => ShrinkWidthArena.prefixBank X T q rankWord W true
local notation "ab" => ShrinkWidthArena.abBank X T q rankWord W
local notation "ap" => absoluteBank Z w
local notation "acols" => MotifAbsolute.columns (absoluteBank Z w)
local notation "arcOrder" => BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "nSites" => (Fintype.card X.Base*(2^(Shrink.J a)*2^g) : ℕ)

private theorem write_bound {p : Fin 5 → Word w} {mem : Memory w} {old : BundleKeys.OldArc X.Base a g → ℕ}
    (layout : Layout p A nSites (2^a) (Shrink.colors a))
    (ranked : RankedInput X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites p mem old)
    (j : ℕ) (hj : j<A) : scatterWrites p B (outAddress p mem (j : Word w)).val := by
  let e := (arcOrder).symm ⟨j,hj⟩
  have he : (arcOrder e).val = j := congrArg Fin.val ((arcOrder).apply_symm_apply _)
  have out := output_eq X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites layout ranked e
  have hb := offset_lt X.packingData X.shrinkNumber X.shrinkOrder sites layout e
  unfold arcWord at out
  rw [he] at out
  change _ < (B+B)*(p 3).val at hb
  rw [scatterWrites,InColumn,show (outAddress p mem (j : Word w)).val = _ from out]
  exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left hb _⟩

/-- The guard shape and exact intervals for all five reports lists, starting
at their actual post-memories in the eleven-visit walk. -/
theorem width_sources {abs : List (Report w)} (last : AbsoluteRun r abs) (room : ShrinkInput.stop X start < 2^w) :
    Checked A (scatterReads s A) (scatterWrites s B) r.scatter ∧
    Checked (B*thickCount a) (prefixReads t B) (prefixWrites t B) r.thickPrefixes ∧
    Checked (B*Q) (prefixReads u B) (prefixWrites u B) r.cdPrefixes ∧
    Checked (B*Q) (abReads ab B) (abWrites ab B) r.abPieces ∧
    Checked A (scatterReads acols A) (scatterWrites acols B) abs := by
  have ranges := ShrinkInput.range_bounds X start
  have fit : (Z).stop < 2^w := ranges.2.2.2.trans_lt room
  have v := (Z).values T (ShrinkInput.placementBank X T start) Fintype.card_pos fit
  have old := r.greedy.old 5
  change T.width.val+A ≤ start at old
  have hw : T.width.val+A ≤ W := old.trans (ranges.1.trans (ranges.2.1.trans ranges.2.2.1))
  have own : (q 1).val+A ≤ W := by
    rw [show (q 1).val = (Z).owner from v.owner]
    change (Z).owner+A ≤ (Z).ranks+A
    apply Nat.add_le_add_right
    unfold ShrinkRankSpace.Shape.owner ShrinkRankSpace.Shape.ranks ShrinkRankSpace.Shape.gathered
      ShrinkRankSpace.Shape.ids ShrinkRankSpace.Shape.counts
    omega
  have hr : (rankWord).val+A ≤ W := by rw [v.ranks]; rfl
  have endWidth : ShrinkWidthArena.stop X q W < 2^w := by
    change W+2*(B*(q 4).val)+2*(B*(q 4).val)+2*B+2*(B*Q) < 2^w
    rw [v.stride]; change W+6*(B*Q)+2*B < _ at room; omega
  have layout := ShrinkWidthArena.scatterLayout X T q rankWord W v.stride.ge own hr hw endWidth
  have ai := absolute_inputs r fit
  have keep (k : Fin 2) (e : BundleKeys.OldArc X.Base a g) :
      r.post (source s (k.castAdd 1) (arcWord arcOrder e)).val =
        r.rankPost (source s (k.castAdd 1) (arcWord arcOrder e)).val := by
    apply r.afterRank
    have before : (s ((k.castAdd 1).castAdd 2)).val+A ≤ W := by fin_cases k <;> first | exact own | exact hr
    have he : (arcOrder e).val < A := (arcOrder e).isLt
    change ((s ((k.castAdd 1).castAdd 2)).val+((arcOrder e).val % (2^w))) % (2^w) < _
    exact (Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt he) _).trans_le before)
  let oldWidth := fun e ↦ (width s r.rankPost (arcWord arcOrder e)).val
  have ranked : RankedInput X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites s r.rankPost oldWidth :=
    ⟨fun e ↦ (keep 0 e).symm.trans (ai.owners e),fun e ↦ (keep 1 e).symm.trans (ai.ranks e),fun _ ↦ rfl⟩
  have wscan := width_scan s A B r.rankPost r.scatter layout.sourceFits (write_bound layout ranked)
    (regions_of_layout X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites layout ranked) r.widths.scatter
  have aLayout := absolute_layout X (start := start) fit
  let oldKey := fun e ↦ (width acols r.post (arcWord arcOrder e)).val
  have aRanked : RankedInput X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites acols r.post oldKey :=
    ⟨ai.owners,ai.ranks,fun _ ↦ rfl⟩
  have ascan := absolute_scan ap A B r.post abs aLayout.sourceFits (write_bound aLayout aRanked)
    (regions_of_layout X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites aLayout aRanked) last.native
  have color : 2 ≤ Shrink.colors a := State.two_le_packingColors a
  have starts : (s 4).val+2*(B*(s 3).val) ≤ ShrinkWidthArena.prefixBase X q W := by
    rw [show (s 4).val = W from Nat.mod_eq_of_lt fit]; rfl
  obtain ⟨prefixes,abLayout,abSize,_,_⟩ := DemandWidths.allocation s (ShrinkWidthArena.prefixBase X q W)
    color (Nat.two_pow_pos a) layout starts endWidth
  have th := prefix_scan t B prefixes.thick _ r.thickPrefixes r.widths.prefixes.thick.executed
  have cd := prefix_scan u B prefixes.motif _ r.cdPrefixes r.widths.prefixes.motif.executed
  have abCount : (ab 0).val = Q := abSize
  have abScan := ab_scan ab B abLayout (ShrinkWidthArena.prefixedMemory r.rankPost r.scatter r.thickPrefixes r.cdPrefixes)
    r.abPieces (by rw [abCount]; exact r.widths.ab)
  have thCount : (t 0).val = thickCount a := prefixes.thickSize
  have cdCount : (u 0).val = Q := prefixes.motifSize
  rw [thCount] at th; rw [cdCount] at cd; rw [abCount] at abScan
  exact ⟨wscan,th,cd,abScan,ascan⟩

private theorem checked_mono {num : ℕ} {rd wr rd' wr' : ℕ → Prop} {rs : List (Report w)}
    (h : Checked num rd wr rs) (read : ∀ x, rd x → rd' x) (write : ∀ x, wr x → wr' x) :
    Checked num rd' wr' rs := ⟨h.1,fun a v he ↦ read a.val (h.2.1 a v he),fun a v he ↦ write a.val (h.2.2 a v he)⟩

/-- All five write ranges lie inside the fresh shrinking arena. The only
earlier read range is the original arc-width column. -/
theorem width_footprints {abs : List (Report w)} (last : AbsoluteRun r abs)
    (lo : ℕ) (low : lo ≤ T.width.val) (room : ShrinkInput.stop X start < 2^w) :
    let rd := fun x ↦ lo ≤ x ∧ x < ShrinkInput.stop X start
    let wr := fun x ↦ start ≤ x ∧ x < ShrinkInput.stop X start
    Checked A rd wr r.scatter ∧ Checked (B*thickCount a) rd wr r.thickPrefixes ∧
    Checked (B*Q) rd wr r.cdPrefixes ∧ Checked (B*Q) rd wr r.abPieces ∧ Checked A rd wr abs := by
  let endAddr := ShrinkInput.stop X start
  let K := B*Q
  let ok (z len : ℕ) := start ≤ z ∧ z+len ≤ endAddr
  have rr := ShrinkInput.range_bounds X start
  have rankFit : (Z).stop < 2^w := rr.2.2.2.trans_lt room
  have hv := (Z).values T (ShrinkInput.placementBank X T start) Fintype.card_pos rankFit
  have wStart : start ≤ W := rr.1.trans (rr.2.1.trans rr.2.2.1)
  have wHead : (s 4).val = W := Nat.mod_eq_of_lt rankFit
  have wStride : (s 3).val = Q := hv.stride
  have endEq : endAddr = W+6*K+2*B := rfl
  have bound {z n x : ℕ} (hz : ok z n) (hx : InColumn z n x) : start ≤ x ∧ x < endAddr :=
    ⟨hz.1.trans hx.1,hx.2.trans_le hz.2⟩
  have head (z : ℕ) (hz : z ≤ endAddr) : (Fin.ofNat (2^w) z).val = z := Nat.mod_eq_of_lt (hz.trans_lt room)
  have ownerLe : start ≤ (Z).owner := rr.1.trans rr.2.1
  have own : (Z).owner+A ≤ (Z).gathered := by
    unfold ShrinkRankSpace.Shape.owner ShrinkRankSpace.Shape.gathered ShrinkRankSpace.Shape.ids ShrinkRankSpace.Shape.counts
    omega
  have key : (Z).key+A ≤ (Z).gathered := by
    unfold ShrinkRankSpace.Shape.key ShrinkRankSpace.Shape.gathered ShrinkRankSpace.Shape.ids ShrinkRankSpace.Shape.counts
    omega
  have ownKey : (Z).key = (Z).owner+A := rfl
  have rect : (Z).ranks = (Z).gathered+2*K := by
    change (Z).gathered+(2*B)*Q = (Z).gathered+2*(B*Q)
    rw [Nat.mul_assoc]
  have wEq : W = (Z).ranks+A := rfl
  have gHead : (acols 4).val = (Z).gathered := hv.gathered
  have aStride : (acols 3).val = Q := hv.stride
  have absoluteCols (i : Fin 3) : ok (acols (i.castAdd 2)).val A := by
    fin_cases i
    · change ok (Fin.ofNat (2^w) (Z).owner).val A; rw [head _ (by omega)]; change start ≤ _ ∧ (Z).owner+A ≤ endAddr; omega
    · change ok (Fin.ofNat (2^w) (Z).ranks).val A; rw [head _ (by omega)]; change start ≤ _ ∧ (Z).ranks+A ≤ endAddr; omega
    · change ok (Fin.ofNat (2^w) (Z).key).val A; rw [head _ (by omega)]; change start ≤ _ ∧ (Z).key+A ≤ endAddr; omega
  have widthOut : ok (s 4).val ((B+B)*(s 3).val) := by rw [wHead,wStride,Nat.add_mul]; change start ≤ W ∧ W+(K+K) ≤ endAddr; omega
  have absOut : ok (acols 4).val ((B+B)*(acols 3).val) := by rw [gHead,aStride,Nat.add_mul]; change start ≤ (Z).gathered ∧ (Z).gathered+(K+K) ≤ endAddr; omega
  have pb : ShrinkWidthArena.prefixBase X q W = W+2*K := by rw [ShrinkWidthArena.prefixBase,hv.stride]
  have abBase : ShrinkWidthArena.abBase X q W = W+2*K+2*K+2*B := by rw [ShrinkWidthArena.abBase,pb,hv.stride]
  have prefixHead (b : Bool) (i : Fin 3) :
      ((ShrinkWidthArena.prefixBank X T q rankWord W b) (i.natAdd 2)).val =
        (![if b then W+K else W,if b then W+2*K+K else W+2*K,
           if b then W+2*K+2*K+B else W+2*K+2*K] : Fin 3 → ℕ) i := by
    cases b <;> fin_cases i
    · change (Fin.ofNat (2^w) (s 4).val).val = W
      rw [wHead]; exact head _ (by omega)
    · change (Fin.ofNat (2^w) (ShrinkWidthArena.prefixBase X q W)).val = W+2*K
      rw [pb]; exact head _ (by omega)
    · change (Fin.ofNat (2^w) (ShrinkWidthArena.prefixBase X q W+2*(B*(s 3).val))).val = W+2*K+2*K
      rw [pb,wStride]; exact head _ (by change W+2*K+2*K ≤ endAddr; omega)
    · change (Fin.ofNat (2^w) ((s 4).val+B*(s 3).val)).val = W+K
      rw [wHead,wStride]; exact head _ (by change W+K ≤ endAddr; omega)
    · change (Fin.ofNat (2^w) (ShrinkWidthArena.prefixBase X q W+B*(s 3).val)).val = W+2*K+K
      rw [pb,wStride]; exact head _ (by change W+2*K+K ≤ endAddr; omega)
    · change (Fin.ofNat (2^w) (ShrinkWidthArena.prefixBase X q W+2*(B*(s 3).val)+B)).val = W+2*K+2*K+B
      rw [pb,wStride]; exact head _ (by change W+2*K+2*K+B ≤ endAddr; omega)
  have pr (b : Bool) (i : Fin 3) : ok ((ShrinkWidthArena.prefixBank X T q rankWord W b) (i.natAdd 2)).val
      (if i.val=2 then B else K) := by
    rw [prefixHead]; cases b <;> fin_cases i <;> simp [ok,endEq] <;> omega
  have abHd : (ab 3).val = W+2*K+2*K+2*B := by
    change (Fin.ofNat (2^w) (ShrinkWidthArena.abBase X q W)).val = _
    rw [abBase,head _ (by omega)]
  have abOff : (ab 4).val = W+2*K+2*K+2*B+K := by
    change (Fin.ofNat (2^w) (ShrinkWidthArena.abBase X q W+K)).val = _
    rw [abBase,head _ (by omega)]
  have abStride : (ab 1).val = Q := hv.stride
  have abOut (i : Fin 2) : ok (ab (i.natAdd 3)).val (B*(ab 1).val) := by
    rw [abStride]; fin_cases i
    · change ok (ab 3).val K; rw [abHd]; change start ≤ _ ∧ _ ≤ endAddr; omega
    · change ok (ab 4).val K; rw [abOff]; change start ≤ _ ∧ _ ≤ endAddr; omega
  have old := r.greedy.old 5
  change T.width.val+A ≤ start at old
  have read {x : ℕ} (h : start ≤ x ∧ x < endAddr) : lo ≤ x ∧ x < endAddr := ⟨by omega,h.2⟩
  have prefixCoverage (b : Bool) :
      let pp := ShrinkWidthArena.prefixBank X T q rankWord W b
      (∀ x, prefixReads pp B x → lo ≤ x ∧ x < endAddr) ∧
      ∀ x, prefixWrites pp B x → start ≤ x ∧ x < endAddr := by
    intro pp
    have stride : (pp 1).val = Q := hv.stride
    constructor
    · intro x hx; apply read; rcases hx with h | h
      · rw [stride] at h; exact bound (pr b 0) h
      · exact bound (pr b 2) h
    · intro x hx; rcases hx with h | h
      · rw [stride] at h; exact bound (pr b 1) h
      · exact bound (pr b 2) h
  obtain ⟨ws,ts,us,bs,as⟩ := width_sources r last room
  dsimp only
  refine ⟨checked_mono ws ?_ (fun _ h ↦ bound widthOut h),
    checked_mono ts (prefixCoverage false).1 (prefixCoverage false).2,
    checked_mono us (prefixCoverage true).1 (prefixCoverage true).2,
    checked_mono bs (fun _ h ↦ read (bound (pr false 2) h)) ?_,
    checked_mono as ?_ (fun _ h ↦ bound absOut h)⟩
  · rintro x ⟨i,h⟩; fin_cases i
    · exact read (bound (absoluteCols 0) h)
    · exact read (bound (absoluteCols 1) h)
    · change InColumn T.width.val A x at h
      exact ⟨low.trans h.1,h.2.trans_le (old.trans (wStart.trans rr.2.2.2))⟩
  · rintro x ⟨i,h⟩; exact bound (abOut i) h
  · rintro x ⟨i,h⟩; exact read (bound (absoluteCols i) h)

end CompressorRecords.ShrinkBundlePlan.Scheduled

end VPVNP
end Computability
end OAI
