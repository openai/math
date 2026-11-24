import OAI.Computability.VPVNP.CompressionHistory
import OAI.Computability.VPVNP.CompressorBundleRankedInput
import OAI.Computability.VPVNP.CompressorRecordsDemandWidths

/-!
# Widths and field starts in the shrinking arena

Scatter the widths of the ranked old ports, scan the two sorted row families,
and split the thick totals into balanced AB pieces. All four workers run in
sequence on a fresh arena after the rank and incidence directories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkWidthArena

open BurstRAM PrimedStackRAM Compression Compression.PackingData BundleKeys
open scoped Classical

variable {w a g : ℕ} (X : State a (packingLaneBits a g))
local notation "N" => Fintype.card X.Base
local notation "A" => N * 2^(packingLaneBits a g) * 2^a
local notation "D" => (2:ℕ)^a
local notation "C" => Shrink.colors a
local notation "n" => N*(2^(Shrink.J a)*2^g)
local notation "B" => numBundles N a g
local notation "Q" => pieceCount D C
local notation "P" => X.packingData
local notation "arcs" => oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex

variable (T : IncidenceDirectory w) (q : Fin 6 → Word w) (dest : Word w) (start : ℕ)

/-- Public words for scattering old port widths into sorted bundle rows, giving the owner,
rank, and old-width columns, row stride, and output base. -/
def scatterBank : Fin 5 → Word w :=
  BundleWidthScatter.scatterPublic q dest T.width (Fin.ofNat _ start)

/-- First address of the field-start rectangles, immediately after the two families of sorted
width rows. -/
def prefixBase := start + 2*(B*(q 4).val)
/-- First address of the AB piece-width rectangle, following both start rectangles and both
columns of bundle totals. -/
def abBase := prefixBase X q start + 2*(B*(q 4).val) + 2*B
/-- First free address after the dense AB piece-width and field-start rectangles. -/
def stop := abBase X q start + 2*(B*Q)

/-- Parameters for scanning sorted widths into field starts and bundle totals. The motif flag
selects the CD rows when true and the thick-wire rows when false. -/
def prefixBank (motif : Bool) : Fin 5 → Word w :=
  BundlePrefixGraph.prefixPublic (scatterBank T q dest start) B D C (prefixBase X q start) motif

/-- Parameters for splitting each thick-wire bundle total into balanced AB pieces and storing
their widths and starting offsets. -/
def abBank : Fin 5 → Word w :=
  DemandWidths.packedPublic (prefixBank X T q dest start false 4) B Q (abBase X q start)

local notation "s" => scatterBank T q dest start
local notation "t" => prefixBank X T q dest start false
local notation "u" => prefixBank X T q dest start true
local notation "p" => abBank X T q dest start

/-- The owner, rank and old width columns can be anywhere before the fresh arena. -/
theorem scatterLayout (stride : Q ≤ (q 4).val) (ownerBefore : (q 1).val+A ≤ start)
    (rankBefore : dest.val+A ≤ start) (widthBefore : T.width.val+A ≤ start)
    (room : stop X q start < 2^w) : BundleWidthScatter.Layout s A n D C := by
  change start + 2*(B*(q 4).val) + 2*(B*(q 4).val) + 2*B + 2*(B*Q) < 2^w at room
  have base : (s 4).val = start := Nat.mod_eq_of_lt (by omega)
  have before (i : Fin 3) : (s (i.castAdd 2)).val+A ≤ start := by
    fin_cases i
    · exact ownerBefore
    · exact rankBefore
    · exact widthBefore
  refine ⟨stride, ?_, fun i ↦ (before i).trans (by omega), ?_, fun i ↦ .inl ((before i).trans base.ge)⟩
  · change B+B ≤ _; omega
  · change (s 4).val + (B+B)*(q 4).val ≤ _
    rw [base,Nat.add_mul]; omega

/-- Memory after scattering the widths and applying first the thick-wire and then the motif
prefix-scan reports. -/
def prefixedMemory (m : Memory w) (ws ts us : List (Report w)) : Memory w :=
  after (after (after m (eventLog ws)) (eventLog ts)) (eventLog us)

/-- Memory after the AB piece reports have written widths and starts on top of the completed
scatter and prefix scans. -/
def finalMemory (m : Memory w) (ws ts us rs : List (Report w)) : Memory w :=
  after (prefixedMemory m ws ts us) (eventLog rs)

/-- Four native executions, readbacks at their joint endpoint, and their cost. -/
structure Run (m : Memory w) (ws ts us rs : List (Report w)) : Prop where
  scatter : runSegment ((template BundleWidthScatter.visit 0).instantiate w s).program 19 (some 0) m
    (List.replicate A []) = some ws
  prefixes : BundlePrefixGraph.Completed P sites X.packingWidth X.shrinkOrder X.shrinkNumber t u
    (after m (eventLog ws)) ts us
  ab : runSegment ((template ABWidths.visit 0).instantiate w p).program 30 (some (Fin.ofNat _ 0))
    (prefixedMemory m ws ts us) (List.replicate (B*Q) []) = some rs
  stored : DemandWidths.Stored P sites X.packingWidth X.shrinkOrder X.shrinkNumber t u p (finalMemory m ws ts us rs)
  frame : ∀ addr < start, finalMemory m ws ts us rs addr = m addr
  cost : RAMBuckets.cost Report.probes ws + RAMBuckets.cost Report.probes ts +
    RAMBuckets.cost Report.probes us + RAMBuckets.cost Report.probes rs = 10*A + 4*(B*Q)

private theorem scatter_frame {m : Memory w} {ws : List (Report w)}
    (layout : BundleWidthScatter.Layout s A n D C)
    (ranked : BundleWidthScatter.RankedInput P X.shrinkNumber X.shrinkOrder arcs sites s m X.packingWidth)
    (run : runSegment ((template BundleWidthScatter.visit 0).instantiate w s).program 19 (some 0) m
      (List.replicate A []) = some ws) {addr : ℕ} (ha : addr < (s 4).val) :
    after m (eventLog ws) addr = m addr := by
  have regions := BundleWidthScatter.regions_of_layout P X.shrinkNumber X.shrinkOrder arcs sites layout ranked
  obtain ⟨ls,hr,_,filled,_⟩ := BundleWidthScatter.run s m A regions
  obtain rfl := Option.some.inj (hr.symm.trans run)
  apply filled.frame
  intro j hj
  let e := (arcs).symm ⟨j,hj⟩
  have he : (arcs e).val = j := congrArg Fin.val ((arcs).apply_symm_apply _)
  have h := BundleWidthScatter.output_eq P X.shrinkNumber X.shrinkOrder arcs sites layout ranked e
  unfold BundleWidthScatter.arcWord at h
  rw [he] at h
  exact Nat.ne_of_lt (h ▸ ha.trans_le (Nat.le_add_right ..))

private theorem prefix_frame {bank : Fin 5 → Word w} {count : ℕ} {m : Memory w} {ls : List (Report w)}
    (run : BundlePrefixRAM.FullRun bank count m ls) {addr : ℕ} (h₁ : addr < (bank 3).val)
    (h₂ : addr < (bank 4).val) : after m (eventLog ls) addr = m addr :=
  run.frame addr (fun _ _ _ _ ↦ by omega) (fun _ _ ↦ by omega)

private theorem ab_frame {bank : Fin 5 → Word w} {count : ℕ} {m : Memory w} {rs : List (Report w)}
    (layout : ABWidths.Layout bank count) (dense : (bank 1).val = (bank 0).val)
    (run : runSegment ((template ABWidths.visit 0).instantiate w bank).program 30 (some (Fin.ofNat _ 0)) m
      (List.replicate (count*(bank 0).val) []) = some rs)
    {addr : ℕ} (ha : ∀ i : Fin 2, addr < (bank (i.natAdd 3)).val) : after m (eventLog rs) addr = m addr := by
  obtain ⟨ls,hr,filled,_⟩ := ABWidths.run bank count m layout.regions
  obtain rfl := Option.some.inj (hr.symm.trans run)
  apply filled.frame
  intro i j hj
  have hjw := hj.trans_le layout.regions.fits
  have row : (ABWidths.row bank (Fin.ofNat _ j)).val = j/(bank 0).val := by
    change (j % (2^w)/(bank 0).val) % (2^w) = _
    rw [Nat.mod_eq_of_lt hjw,Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt hjw)]
  have rank : (ABWidths.rank bank (Fin.ofNat _ j)).val = j%(bank 0).val := by
    change (j % (2^w)%(bank 0).val) % (2^w) = _
    rw [Nat.mod_eq_of_lt hjw,Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt hjw)]
  have offset : j/(bank 0).val * (bank 0).val + j%(bank 0).val = j := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]
  have fit := layout.outFit i
  rw [dense] at fit
  change addr ≠ (ABWidths.address bank i (Fin.ofNat _ j)).val
  rw [ABWidths.address, Fin.val_add, Fin.val_add, Fin.val_mul, row, rank, dense,
    Nat.mod_add_mod, Nat.add_mod_mod, offset, Nat.mod_eq_of_lt (by omega)]
  exact Nat.ne_of_lt ((ha i).trans_le (Nat.le_add_right ..))

/-- Starting with the native rank directory, materialize all widths and starts.
The original directories and every other address below the allocation survive. -/
theorem build (m : Memory w) (stride : Q ≤ (q 4).val) (ownerBefore : (q 1).val+A ≤ start)
    (rankBefore : dest.val+A ≤ start) (widthBefore : T.width.val+A ≤ start)
    (room : stop X q start < 2^w) (widthFit : Q*X.maxWireWidth < 2^w)
    (ranked : BundleWidthScatter.RankedInput P X.shrinkNumber X.shrinkOrder arcs sites s m X.packingWidth) :
    ∃ ws ts us rs, Run X T q dest start m ws ts us rs := by
  let block := B*(q 4).val
  have hroom : start+2*block+2*block+2*B+2*(B*Q) < 2^w := room
  have hc : 2 ≤ C := by have := Nat.two_pow_pos a; unfold Shrink.colors; omega
  have layout := scatterLayout X T q dest start stride ownerBefore rankBefore widthBefore room
  have sorted : (s 4).val = start := Nat.mod_eq_of_lt (by omega)
  have endWidths : (s 4).val + 2*((n*D)*(s 3).val) ≤ prefixBase X q start := by
    rw [sorted]; exact le_rfl
  obtain ⟨rows,abLayout,cap,tot,apart⟩ := DemandWidths.allocation s (prefixBase X q start)
    hc (Nat.two_pow_pos a) layout endWidths room
  obtain ⟨ws,ts,us,rs,hs,hp,hab,stored,cost⟩ := DemandWidths.from_ranked_input P sites X.packingWidth
    X.shrinkOrder X.shrinkNumber arcs hc s t u p rows m ranked X.maxWireWidth
    (fun _ ↦ X.width_le_maxWireWidth _) widthFit abLayout cap tot apart
  refine ⟨ws,ts,us,rs,hs,hp,hab,stored,?_,cost⟩
  intro addr ha
  have baseT : (t 3).val = start+2*block :=
    Nat.mod_eq_of_lt (show start+2*block < 2^w by omega)
  have totalT : (t 4).val = start+2*block+2*block :=
    Nat.mod_eq_of_lt (show start+2*block+2*block < 2^w by omega)
  have baseU : (u 3).val = start+2*block+block :=
    Nat.mod_eq_of_lt (show start+2*block+block < 2^w by omega)
  have totalU : (u 4).val = start+2*block+2*block+B :=
    Nat.mod_eq_of_lt (show start+2*block+2*block+B < 2^w by omega)
  have baseP : (p 3).val = start+2*block+2*block+2*B :=
    Nat.mod_eq_of_lt (show start+2*block+2*block+2*B < 2^w by omega)
  have endP : (p 4).val = start+2*block+2*block+2*B+B*Q :=
    Nat.mod_eq_of_lt (show start+2*block+2*block+2*B+B*Q < 2^w by omega)
  have hab' : runSegment ((template ABWidths.visit 0).instantiate w p).program 30 (some (Fin.ofNat _ 0))
      (prefixedMemory m ws ts us) (List.replicate (B*(p 0).val) []) = some rs := by
    change (p 0).val = Q at cap
    rw [cap]; exact hab
  have final := ab_frame abLayout rfl hab' (addr := addr) (by
    intro i; fin_cases i
    · change addr < (p 3).val; omega
    · change addr < (p 4).val; omega)
  exact final.trans ((prefix_frame hp.motif (by omega) (by omega)).trans
    ((prefix_frame hp.thick (by omega) (by omega)).trans
    (scatter_frame X T q dest start layout ranked hs (ha.trans_le sorted.ge))))

end CompressorRecords.ShrinkWidthArena

end VPVNP
end Computability
end OAI
