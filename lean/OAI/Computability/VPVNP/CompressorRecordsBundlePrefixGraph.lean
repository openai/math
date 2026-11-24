import OAI.Computability.VPVNP.CompressorRecordsBundlePrefixRAM
import OAI.Computability.VPVNP.CompressorBundleSortedWidths
import OAI.Computability.VPVNP.SlotDemandSlices

/-!
# Field starts and totals in the two sorted rows of a packed bundle

Each prefix scan reads a fixed-size live row within a rectangle. The thick row
uses the old concatenation order, and the motif row uses the CD piece numbers.
Their two full scans run consecutively on the external width arrays produced by
scattering the original ports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundlePrefixGraph

open BurstRAM Compression Compression.PackingData BundleLists BundlePrefixRAM

variable {w : ℕ}

/-- Width, offset and total readbacks for a physical set of rows indexed by
a finite site type, each row indexed by a possibly different fiber type. -/
def Widths {B k : ℕ} {S : Type*} {F : S → Type*} (index : S ≃ Fin B)
    (number : ∀ b, F b ≃ Fin k) (width : ∀ b, F b → ℕ) (p : Fin 5 → Word w) (m : Memory w) :=
  ∀ b (i : Fin k), (m ((p 2).val+(index b).val*(p 1).val+i.val)).val = width b ((number b).symm i)

/-- Every live item in each bundle row stores the sum of widths of the items preceding it in
the given ordering. -/
def Starts {B k : ℕ} {S : Type*} {F : S → Type*} (index : S ≃ Fin B)
    (number : ∀ b, F b ≃ Fin k) (width : ∀ b, F b → ℕ) (p : Fin 5 → Word w) (m : Memory w) :=
  ∀ b (x : F b), (m ((p 3).val+(index b).val*(p 1).val+(number b x).val)).val =
    fieldStart (number b) (width b) x

private theorem prefix_total {B k : ℕ} {S : Type*} {F : S → Type*} [∀ b, Fintype (F b)]
    (index : S ≃ Fin B) (number : ∀ b, F b ≃ Fin k) (width : ∀ b, F b → ℕ)
    (p : Fin 5 → Word w) (m : Memory w) (read : Widths index number width p m) (b : S) :
    prefixSum p m (index b).val k = ∑ x, width b x := by
  rw [prefixSum, ← Fin.sum_univ_eq_sum_range, ← (number b).symm.sum_comp (width b)]
  exact Finset.sum_congr rfl (fun j _ ↦ read b j)

private theorem prefix_start {B k : ℕ} {S : Type*} {F : S → Type*} (index : S ≃ Fin B)
    (number : ∀ b, F b ≃ Fin k) (width : ∀ b, F b → ℕ) (p : Fin 5 → Word w) (m : Memory w)
    (read : Widths index number width p m) (b : S) (x : F b) :
    prefixSum p m (index b).val (number b x).val = fieldStart (number b) (width b) x := by
  rw [prefixSum, ← Fin.sum_univ_eq_sum_range, fieldStart]
  exact Finset.sum_congr rfl (fun j _ ↦ read b (j.castLE (number b x).isLt.le))

/-- Execute the full row scan with a bound on the mathematical sum, recovering
every source-field start and total at its physical address. -/
theorem numbered_run {B k : ℕ} {S : Type*} {F : S → Type*} [∀ b, Fintype (F b)] (index : S ≃ Fin B)
    (number : ∀ b, F b ≃ Fin k) (width : ∀ b, F b → ℕ) (p : Fin 5 → Word w) (m : Memory w)
    (layout : BundlePrefixRAM.Layout p B) (hk : (p 0).val = k) (read : Widths index number width p m)
    (fit : ∀ b, (∑ x, width b x) < 2^w) :
    ∃ rs, FullRun p B m rs ∧ Starts index number width p (after m (eventLog rs)) ∧
      ∀ b, (after m (eventLog rs) ((p 4).val+(index b).val)).val = ∑ x, width b x := by
  have fits (b : ℕ) (hb : b < B) : prefixSum p m b (p 0).val < 2^w := by
    let s := index.symm ⟨b,hb⟩
    have he : (index s).val = b := congrArg Fin.val (index.apply_symm_apply _)
    rw [hk, ← he, prefix_total index number width p m read s]
    exact fit s
  obtain ⟨rs,run⟩ := full_run p B m layout fits
  refine ⟨rs,run,fun b x ↦ ?_,fun b ↦ ?_⟩
  · exact (run.starts _ (index b).isLt _ (hk ▸ (number b x).isLt)).trans
      (prefix_start index number width p m read b x)
  · exact (run.totals _ (index b).isLt).trans (hk ▸ prefix_total index number width p m read b)

/-- Static separation of a region from the two tables a prefix scan writes. -/
structure Outside (p : Fin 5 → Word w) (B base size : ℕ) : Prop where
  starts : BundleGather.separated base size (p 3).val (B*(p 1).val)
  totals : BundleGather.separated base size (p 4).val B

private theorem slot_lt {B k stride b j : ℕ} (hb : b < B) (hj : j < k) (hk : k ≤ stride) :
    b * stride + j < B * stride := by
  have h := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at h
  omega

theorem Outside.preserve {p : Fin 5 → Word w} {B base size : ℕ} {m : Memory w} {rs}
    (h : Outside p B base size) (layout : BundlePrefixRAM.Layout p B) (run : FullRun p B m rs)
    (j : ℕ) (hj : j < size) : after m (eventLog rs) (base+j) = m (base+j) := by
  apply run.frame
  · intro b hb l hl
    have := slot_lt hb hl layout.size_le_stride
    have := h.starts.outside hj
    omega
  · intro b hb
    have := h.totals.outside hj
    omega

variable {V H Tag L : Type} {d c n A : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (site : Site V Tag L ≃ Fin n)
variable (old : Arc V H Tag L d c → ℕ)

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- The AB width producer reads one old thick-wire total per absolute bundle. -/
def ThickTotals (totalBase : Word w) (post : Memory w) : Prop :=
  ∀ b, (post (totalBase.val+(portIndex site b).val)).val = P.bundleWidth old b

/-- Sum of the original CD widths assigned to a bundle. -/
def motifTotal (b : Port V Tag L d) : ℕ := ∑ x : P.MotifFiber b, old x.1.1

variable (dd : P.ThickNumbering) (cd : P.BundleNumbering)

/-- The original arc width carried by a thick wire in the selected bundle. -/
abbrev thickWidth (b : Port V Tag L d) (x : P.ThickFiber b) := old x.1.1
/-- The original arc width carried by a CD motif assigned to the selected bundle. -/
abbrev motifWidth (b : Port V Tag L d) (x : P.MotifFiber b) := old x.1.1

/-- Prefix parameters use the two halves of the sorted-width rectangle in
the same port order. Each scan may place its output tables independently. -/
structure RowLayout (s t u : Fin 5 → Word w) (A n d c : ℕ) : Prop where
  scatter : BundleWidthScatter.Layout s A n d c
  thick : BundlePrefixRAM.Layout t (n*d)
  motif : BundlePrefixRAM.Layout u (n*d)
  thickSize : (t 0).val = 2^c*d/4
  motifSize : (u 0).val = pieceCount d c
  thickStride : t 1 = s 3
  motifStride : u 1 = s 3
  thickBase : t 2 = s 4
  motifBase : (u 2).val = (s 4).val+(n*d)*(s 3).val
  keepMotif : Outside t (n*d) (u 2).val ((n*d)*(u 1).val)
  keepThick : Outside u (n*d) (t 2).val ((n*d)*(t 1).val)
  keepStarts : Outside u (n*d) (t 3).val ((n*d)*(t 1).val)
  keepTotals : Outside u (n*d) (t 4).val (n*d)

/-- Public words for a contiguous pair of start rectangles followed by the
two total columns. The input sorted-width rectangle stays at its original
base. The two modes use the same fixed worker. -/
def prefixPublic (s : Fin 5 → Word w) (B d c base : ℕ) (motif : Bool) : Fin 5 → Word w :=
  let block := B*(s 3).val
  let k := if motif then pieceCount d c else 2^c*d/4
  let widths := if motif then (s 4).val+block else (s 4).val
  let starts := if motif then base+block else base
  let totals := if motif then base+2*block+B else base+2*block
  ![Fin.ofNat _ k,s 3,Fin.ofNat _ widths,Fin.ofNat _ starts,Fin.ofNat _ totals]

/-- A single capacity bound certifies the layout of both prefix scans. -/
theorem RowLayout.packed (s : Fin 5 → Word w) (A n d c base : ℕ) (hc : 2 ≤ c) (hd : 0 < d)
    (space : BundleWidthScatter.Layout s A n d c)
    (afterWidths : (s 4).val+2*((n*d)*(s 3).val) ≤ base)
    (fit : base+2*((n*d)*(s 3).val)+2*(n*d) < 2^w) :
    RowLayout s (prefixPublic s (n*d) d c base false) (prefixPublic s (n*d) d c base true) A n d c := by
  let B := n*d
  let block := B*(s 3).val
  let t := prefixPublic s B d c base false
  let u := prefixPublic s B d c base true
  change (s 4).val+2*block ≤ base at afterWidths
  change base+2*block+2*B < 2^w at fit
  have small : 2^c*d/4 ≤ pieceCount d c := by unfold pieceCount; omega
  have positive : 0 < 2^c*d/4 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hc
    rw [pow_add, show 2^2 = 4 by decide, Nat.mul_assoc]
    have := Nat.mul_pos (Nat.two_pow_pos k) hd
    omega
  have live := space.slots
  have modulus := (s 3).isLt
  have ht₀ : (t 0).val = 2^c*d/4 := Nat.mod_eq_of_lt (show 2^c*d/4 < 2^w by omega)
  have hu₀ : (u 0).val = pieceCount d c := Nat.mod_eq_of_lt (show pieceCount d c < 2^w by omega)
  have ht₁ : t 1 = s 3 := rfl
  have hu₁ : u 1 = s 3 := rfl
  have ht₂ : t 2 = s 4 := Fin.ext (Nat.mod_eq_of_lt (s 4).isLt)
  have hu₂ : (u 2).val = (s 4).val+block := Nat.mod_eq_of_lt (show (s 4).val+block < 2^w by omega)
  have ht₃ : (t 3).val = base := Nat.mod_eq_of_lt (show base < 2^w by omega)
  have hu₃ : (u 3).val = base+block := Nat.mod_eq_of_lt (show base+block < 2^w by omega)
  have ht₄ : (t 4).val = base+2*block := Nat.mod_eq_of_lt (show base+2*block < 2^w by omega)
  have hu₄ : (u 4).val = base+2*block+B := Nat.mod_eq_of_lt (show base+2*block+B < 2^w by omega)
  change RowLayout s t u A n d c
  refine ⟨space, ?_, ?_, ht₀, hu₀, ht₁, hu₁, ht₂, hu₂, ?_, ?_, ?_, ?_⟩
  all_goals constructor
  all_goals simp only [BundleGather.separated, ht₀, hu₀, ht₁, hu₁, ht₂, hu₂, ht₃, hu₃, ht₄, hu₄]
  all_goals dsimp only [block,B] at *
  all_goals omega

/-- The two prefix workers, and the typed contents of all six tables after the
second worker finishes. Each worker's full frame is available in its report. -/
structure Completed (t u : Fin 5 → Word w) (initial : Memory w) (ts us : List (Report w)) : Prop where
  thick : FullRun t (n*d) initial ts
  motif : FullRun u (n*d) (after initial (eventLog ts)) us
  thickWidths : Widths (portIndex site) dd (thickWidth P old) t (after (after initial (eventLog ts)) (eventLog us))
  motifWidths : Widths (portIndex site) cd (motifWidth P old) u (after (after initial (eventLog ts)) (eventLog us))
  thickStarts : Starts (portIndex site) dd (thickWidth P old) t (after (after initial (eventLog ts)) (eventLog us))
  motifStarts : Starts (portIndex site) cd (motifWidth P old) u (after (after initial (eventLog ts)) (eventLog us))
  thickTotals : ThickTotals P site old (t 4) (after (after initial (eventLog ts)) (eventLog us))
  motifTotals : ∀ b, ((after (after initial (eventLog ts)) (eventLog us)) ((u 4).val+(portIndex site b).val)).val =
    motifTotal P old b

/-- Given the actual output rows of the width scatter, execute the thick and
CD prefix scans in sequence. The final tables retain every live sorted width,
its offset in the corresponding concatenation, and the row's total. -/
theorem prefix_runs (s t u : Fin 5 → Word w) (layout : RowLayout s t u A n d c)
    (m : Memory w)
    (th : ∀ b i, (m ((BundleWidthScatter.rowBase s site (.inl b)).val+i.val)).val = old ((dd b).symm i).1.1)
    (mo : ∀ b i, (m ((BundleWidthScatter.rowBase s site (.inr b)).val+i.val)).val = old ((cd b).symm i).1.1)
    (thFit : ∀ b, P.bundleWidth old b < 2^w) (moFit : ∀ b, motifTotal P old b < 2^w) :
    ∃ ts us, Completed P site old dd cd t u m ts us := by
  let idx := portIndex site (d := d)
  have thWidth : Widths idx dd (thickWidth P old) t m := by
    intro b i
    have h := th b i
    rw [BundleWidthScatter.rowBase_val site layout.scatter, show (bucketIndex site (.inl b)).val = (idx b).val from rfl] at h
    simpa only [layout.thickBase,layout.thickStride] using h
  have cdWidth : Widths idx cd (motifWidth P old) u m := by
    intro b i
    have h := mo b i
    rw [BundleWidthScatter.rowBase_val site layout.scatter, show (bucketIndex site (.inr b)).val = n*d+(idx b).val from rfl,
      Nat.add_mul, ← Nat.add_assoc] at h
    simpa only [layout.motifBase,layout.motifStride] using h
  obtain ⟨ts,ht,st,tt⟩ := numbered_run idx dd (thickWidth P old) t m layout.thick layout.thickSize thWidth thFit
  let mid := after m (eventLog ts)
  have cdMid : Widths idx cd (motifWidth P old) u mid := by
    intro b i
    have hs := slot_lt (idx b).isLt i.isLt (layout.motifSize ▸ layout.motif.size_le_stride)
    dsimp only [mid]
    rw [Nat.add_assoc, layout.keepMotif.preserve layout.thick ht _ hs, ← Nat.add_assoc]
    exact cdWidth b i
  obtain ⟨us,hu,su,tu⟩ := numbered_run idx cd (motifWidth P old) u mid layout.motif layout.motifSize cdMid moFit
  refine ⟨ts,us,ht,hu,?_,?_,?_,su,?_,tu⟩
  · intro b i
    have hlt : i.val < (t 0).val := by rw [layout.thickSize]; exact i.isLt
    have hs := slot_lt (idx b).isLt hlt layout.thick.size_le_stride
    rw [Nat.add_assoc, layout.keepThick.preserve layout.motif hu _ hs, ← Nat.add_assoc]
    dsimp only [mid]
    rw [ht.saved.widths layout.thick _ _ (idx b).isLt hlt]
    exact thWidth b i
  · intro b i
    rw [hu.saved.widths layout.motif _ _ (idx b).isLt (by rw [layout.motifSize]; exact i.isLt)]
    exact cdMid b i
  · intro b x
    have hs := slot_lt (idx b).isLt (dd b x).isLt (layout.thickSize ▸ layout.thick.size_le_stride)
    rw [Nat.add_assoc, layout.keepStarts.preserve layout.motif hu _ hs, ← Nat.add_assoc]
    exact st b x
  · intro b
    rw [layout.keepTotals.preserve layout.motif hu _ (idx b).isLt]
    exact tt b

theorem motifTotal_le (hc : 2 ≤ c) (W : ℕ) (hW : ∀ a, old a ≤ W) (b : Port V Tag L d) :
    motifTotal P old b ≤ pieceCount d c * W := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x : P.MotifFiber b ↦ fun _ ↦ hW x.1.1)
  simpa [motifTotal, P.card_motifs_bundle hc] using h

/-- Scatter each old port once, then visit each occupied width cell exactly
once across the two prefix scans. Their combined call-plus-probe count is ten
times the number of old ports. A uniform bound on the old widths suffices. -/
theorem scatter_prefix_runs (arcs : Arc V H Tag L d c ≃ Fin A) (hc : 2 ≤ c)
    (s t u : Fin 5 → Word w) (layout : RowLayout s t u A n d c)
    (m : Memory w) (stored : BundleWidthScatter.RankedInput P cd dd arcs site s m old)
    (W : ℕ) (bound : ∀ a, old a ≤ W) (fit : pieceCount d c * W < 2^w) :
    let M := (PrimedStackRAM.template BundleWidthScatter.visit 0).instantiate w s
    ∃ ws ts us, let scattered := after m (eventLog ws)
      runSegment M.program 19 (some 0) m (List.replicate A []) = some ws ∧
      endState (some 0) ws = some (Fin.ofNat _ A) ∧ BundleWidthScatter.Filled s m scattered A ∧
      ws.length = A ∧ (∀ r ∈ ws, r.events.length = 18 ∧ r.probes = 4) ∧
      Completed P site old dd cd t u scattered ts us ∧
      RAMBuckets.cost Report.probes ws + RAMBuckets.cost Report.probes ts + RAMBuckets.cost Report.probes us = 10*A := by
  obtain ⟨ws,wr,we,wd,wl,ww,wcost,wth,wmo⟩ :=
    BundleWidthScatter.graph_run P cd dd arcs site s m old layout.scatter stored
  have hsmall : 2^c*d/4 ≤ pieceCount d c := by unfold pieceCount; omega
  have hth (b : Port V Tag L d) : P.bundleWidth old b < 2^w :=
    ((P.bundleWidth_le hc old bound b).trans (Nat.mul_le_mul_right W hsmall)).trans_lt fit
  obtain ⟨ts,us,done⟩ := prefix_runs P site old dd cd s t u layout _ wth wmo hth
    (fun b ↦ (motifTotal_le P old hc W bound b).trans_lt fit)
  refine ⟨ws,ts,us,wr,we,wd,wl,ww,done,?_⟩
  let e : Arc V H Tag L d c ≃ Fin ((n*d)*(2^c*d)) :=
    ((portIndex site).prodCongr (((bitWordFinEquiv c).prodCongr P.slotLabel).trans finProdFinEquiv)).trans finProdFinEquiv
  have card : (n*d)*(2^c*d) = A := by simpa using Fintype.card_congr (e.symm.trans arcs)
  rw [wcost,done.thick.cost,done.motif.cost,layout.thickSize,layout.motifSize]
  have size := BundleKeys.bundle_row_lengths_add (d := d) hc
  calc
    5*A + 5*(n*d*(2^c*d/4)) + 5*(n*d*pieceCount d c) =
      5*A + 5*(n*d*(2^c*d/4+pieceCount d c)) := by ring
    _ = 10*A := by rw [size,card]; omega

end CompressorRecords.BundlePrefixGraph

end VPVNP
end Computability
end OAI
