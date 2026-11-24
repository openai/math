import OAI.Computability.VPVNP.CompressorRecordsABGraph
import OAI.Computability.VPVNP.CompressorRecordsBundlePrefixGraph

/-!
# Simultaneous demand and thick-wire width columns

After the sorted-width scatter and the two old-field prefix scans, one native
balanced-piece scan materializes all AB widths. It preserves the sorted CD
widths, the original thick-wire widths, and the starts of both old field
families. Thus the AB and CD words for a single term share a bundle and rank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandWidths

open Compression Compression.PackingData BurstRAM PrimedStackRAM BundleLists
open BundlePrefixGraph (Widths Starts thickWidth motifWidth)

variable {w B : ℕ}

private theorem out_bounds {p : Fin 5 → Word w} (L : ABWidths.Layout p B)
    (t : Fin 2) (i : ℕ) (hi : i<B*(p 0).val) :
    (p (t.natAdd 3)).val ≤ (ABWidths.address p t (Fin.ofNat _ i)).val ∧
    (ABWidths.address p t (Fin.ofNat _ i)).val < (p (t.natAdd 3)).val + B*(p 1).val := by
  have hf := L.regions.fits
  have hiw := hi.trans_le hf
  have hr : i/(p 0).val < B := (Nat.div_lt_iff_lt_mul L.positive).mpr hi
  have hs : i%(p 0).val < (p 1).val := (Nat.mod_lt _ L.positive).trans_le L.stride
  have hprod := Nat.mul_le_mul_right (p 1).val hr
  rw [Nat.succ_mul] at hprod
  have ho : (i/(p 0).val)*(p 1).val + i%(p 0).val < B*(p 1).val := by omega
  have htotal := L.outFit t
  have hrv : (ABWidths.row p (Fin.ofNat _ i)).val = i/(p 0).val := by
    change (i%(2^w)/(p 0).val)%(2^w) = _
    rw [Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt hiw)]
  have hsv : (ABWidths.rank p (Fin.ofNat _ i)).val = i%(p 0).val := by
    change (i%(2^w)%(p 0).val)%(2^w) = _
    rw [Nat.mod_eq_of_lt hiw,Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt hiw)]
  rw [ABWidths.address, Fin.val_add,Fin.val_add,Fin.val_mul,hrv,hsv,Nat.mod_add_mod,
    Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega)]
  omega

/-- An old rectangle lies outside each of the new AB output rectangles. -/
def Outside (p : Fin 5 → Word w) (B base length : ℕ) : Prop :=
  ∀ t : Fin 2, base+length ≤ (p (t.natAdd 3)).val ∨ (p (t.natAdd 3)).val + B*(p 1).val ≤ base

private theorem frame {p : Fin 5 → Word w} {m m' : Memory w} (layout : ABWidths.Layout p B)
    (h : ABWidths.Filled p m m' (B*(p 0).val)) {base length : ℕ} (apart : Outside p B base length)
    {addr : ℕ} (lo : base ≤ addr) (hi : addr < base+length) : m' addr = m addr := by
  apply h.frame
  intro t j hj e
  change addr = (ABWidths.address p t (Fin.ofNat (2^w) j)).val at e
  obtain ⟨hl,hu⟩ := out_bounds layout t j hj
  rcases apart t with a|a <;> omega

private theorem slot_bound {b j B s k : ℕ} (hb : b<B) (hj : j<k) (h : k≤s) :
    b*s+j < B*s := by
  have hm := Nat.mul_le_mul_right s hb
  rw [Nat.succ_mul] at hm
  omega

/-- Allocate two dense AB rectangles of equal extent, with the total column
already reserved at its supplied address. -/
def packedPublic (total : Word w) (B k start : ℕ) : Fin 5 → Word w :=
  ![Fin.ofNat _ k, Fin.ofNat _ k, total, Fin.ofNat _ start, Fin.ofNat _ (start+B*k)]

theorem packedLayout (total : Word w) (B k start : ℕ) (hk : 0<k) (kw : k<2^w)
    (afterTotals : total.val+B ≤ start) (fit : start+2*(B*k) < 2^w) :
    ABWidths.Layout (packedPublic total B k start) B := by
  let p := packedPublic total B k start
  have h₀ : (p 0).val = k := Nat.mod_eq_of_lt kw
  have h₁ : (p 1).val = k := Nat.mod_eq_of_lt kw
  have h₂ : p 2 = total := rfl
  have h₃ : (p 3).val = start := Nat.mod_eq_of_lt (by omega)
  have h₄ : (p 4).val = start+B*k := Nat.mod_eq_of_lt (by omega)
  change ABWidths.Layout p B
  refine ⟨h₀ ▸ hk,by rw [h₀,h₁],by rw [h₂]; omega,?_,?_,?_⟩
  · intro t; fin_cases t <;> first
      | change (p 3).val+B*(p 1).val ≤ _; rw [h₃,h₁]; omega
      | change (p 4).val+B*(p 1).val ≤ _; rw [h₄,h₁]; omega
  · intro t; left
    fin_cases t <;> first
      | change total.val+B ≤ (p 3).val; rw [h₃]; exact afterTotals
      | change total.val+B ≤ (p 4).val; rw [h₄]; omega
  · left; rw [h₁,h₃,h₄]

theorem packedOutside (total : Word w) {B k start base length : ℕ}
    (before : base+length ≤ start) (fit : start+2*(B*k) < 2^w) :
    Outside (packedPublic total B k start) B base length := by
  let p := packedPublic total B k start
  have h₃ : (p 3).val = start := Nat.mod_eq_of_lt (by omega)
  have h₄ : (p 4).val = start+B*k := Nat.mod_eq_of_lt (by omega)
  intro t; left
  fin_cases t <;> first
    | change base+length ≤ (p 3).val; rw [h₃]; exact before
    | change base+length ≤ (p 4).val; rw [h₄]; omega

variable {V H T L : Type} {d c n : ℕ} [AddCommGroup H] [AddCommGroup T] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype T] [Fintype L]
variable [DecidableEq V] [DecidableEq T] [DecidableEq L]
variable (P : PackingData V H T L d c) (site : Site V T L ≃ Fin n) (old : Arc V H T L d c → ℕ)
variable (dd : P.ThickNumbering) (cd : P.BundleNumbering)

/-- All demand widths and all old and AB field offsets in one memory snapshot. -/
structure Stored (thick cdRows ab : Fin 5 → Word w) (mem : Memory w) : Prop where
  thickWidths : Widths (portIndex site) dd (thickWidth P old) thick mem
  cdWidths : Widths (portIndex site) cd (motifWidth P old) cdRows mem
  thickStarts : Starts (portIndex site) dd (thickWidth P old) thick mem
  cdStarts : Starts (portIndex site) cd (motifWidth P old) cdRows mem
  ab : ABWidths.ABColumns P cd site old ab mem

/-- A fixed scan gives both sides of the input to every demand motif and the
two orderings needed by the AB-copy kernel at its endpoints. -/
theorem complete (t u p : Fin 5 → Word w) (initial : Memory w) {ts us : List (Report w)}
    (h : BundlePrefixGraph.Completed P site old dd cd t u initial ts us)
    (layout : ABWidths.Layout p (n*d)) (count : (p 0).val = pieceCount d c)
    (total : p 2 = t 4)
    (thickStride : 2^c*d/4 ≤ (t 1).val) (cdStride : pieceCount d c ≤ (u 1).val)
    (apart : ∀ z ∈ [t,u], ∀ i ∈ ([2,3] : List (Fin 5)), Outside p (n*d) (z i).val ((n*d)*(z 1).val)) :
    let mem := after (after initial (eventLog ts)) (eventLog us)
    let N := n*d*pieceCount d c
    let M := (template ABWidths.visit 0).instantiate w p
    ∃ rs, runSegment M.program 30 (some (Fin.ofNat _ 0)) mem (List.replicate N []) = some rs ∧
      Stored P site old dd cd t u p (after mem (eventLog rs)) ∧ rs.length = N ∧
      RAMBuckets.cost Report.probes rs = 4*N := by
  intro mem N M
  have totals : ∀ b, (mem ((p 2).val+(portIndex site b).val)).val = P.bundleWidth old b := total ▸ h.thickTotals
  obtain ⟨rs,hr,hab,hf,hl,cost⟩ := ABWidths.graph_run P cd site old p mem layout count totals
  have hf' : ABWidths.Filled p mem (after mem (eventLog rs)) (n*d*(p 0).val) := count ▸ hf
  have keep (z : Fin 5 → Word w) (hz : z ∈ [t,u]) (i : Fin 5) (hi : i ∈ ([2,3] : List (Fin 5)))
      (b : Site V T L × Fin d) (j : ℕ) (hj : j < (z 1).val) :
      after mem (eventLog rs) ((z i).val+(portIndex site b).val*(z 1).val+j) =
        mem ((z i).val+(portIndex site b).val*(z 1).val+j) := by
    apply frame layout hf' (apart z hz i hi)
    · omega
    · have hb := slot_bound (portIndex site b).isLt hj le_rfl
      omega
  refine ⟨rs,hr,⟨?_,?_,?_,?_,hab⟩,hl,cost⟩
  · intro b j; rw [keep t (by simp) 2 (by simp) b j.val (j.isLt.trans_le thickStride)]; exact h.thickWidths b j
  · intro b j; rw [keep u (by simp) 2 (by simp) b j.val (j.isLt.trans_le cdStride)]; exact h.motifWidths b j
  · intro b x
    rw [keep t (by simp) 3 (by simp) b (dd b x).val ((dd b x).isLt.trans_le thickStride)]
    exact h.thickStarts b x
  · intro b x
    rw [keep u (by simp) 3 (by simp) b (cd b x).val ((cd b x).isLt.trans_le cdStride)]
    exact h.motifStarts b x

/-- Scatter the ranked actual widths, compute both old-field prefix rectangles, and
then materialize the AB widths. These four segments use one post-memory after
another. Their combined cost is ten units per old port plus four per motif. -/
theorem from_ranked_input {A : ℕ} (arcs : Arc V H T L d c ≃ Fin A) (hc : 2 ≤ c)
    (s t u p : Fin 5 → Word w) (oldLayout : BundlePrefixGraph.RowLayout s t u A n d c)
    (m : Memory w) (ranked : BundleWidthScatter.RankedInput P cd dd arcs site s m old)
    (W : ℕ) (bound : ∀ e, old e ≤ W) (fit : pieceCount d c*W < 2^w)
    (layout : ABWidths.Layout p (n*d)) (count : (p 0).val = pieceCount d c) (total : p 2=t 4)
    (apart : ∀ z ∈ [t,u], ∀ i ∈ ([2,3] : List (Fin 5)), Outside p (n*d) (z i).val ((n*d)*(z 1).val)) :
    let S := (template BundleWidthScatter.visit 0).instantiate w s
    let M := (template ABWidths.visit 0).instantiate w p
    ∃ ws ts us rs, let scattered := after m (eventLog ws)
      let prefixed := after (after scattered (eventLog ts)) (eventLog us)
      runSegment S.program 19 (some 0) m (List.replicate A []) = some ws ∧
      BundlePrefixGraph.Completed P site old dd cd t u scattered ts us ∧
      runSegment M.program 30 (some (Fin.ofNat _ 0)) prefixed (List.replicate (n*d*pieceCount d c) []) = some rs ∧
      Stored P site old dd cd t u p (after prefixed (eventLog rs)) ∧
      RAMBuckets.cost Report.probes ws + RAMBuckets.cost Report.probes ts +
        RAMBuckets.cost Report.probes us + RAMBuckets.cost Report.probes rs =
          10*A + 4*(n*d*pieceCount d c) := by
  intro S M
  obtain ⟨ws,ts,us,hr,_,_,_,_,done,hcost⟩ :=
    BundlePrefixGraph.scatter_prefix_runs P site old dd cd arcs hc s t u oldLayout m ranked W bound fit
  have ht : 2^c*d/4 ≤ (t 1).val := oldLayout.thickSize ▸ oldLayout.thick.size_le_stride
  have hu : pieceCount d c ≤ (u 1).val := oldLayout.motifSize ▸ oldLayout.motif.size_le_stride
  obtain ⟨rs,hab,stored,_,habcost⟩ :=
    complete P site old dd cd t u p _ done layout count total ht hu apart
  exact ⟨ws,ts,us,rs,hr,done,hab,stored,congrArg₂ (·+·) hcost habcost⟩

/-- Following the old sorted-width rectangle, reserve the two old-start
rectangles, the two old-total columns, and finally the AB width and start
rectangles. One last-address bound suffices for all three subsequent scans. -/
theorem allocation {A n d c : ℕ} (s : Fin 5 → Word w) (start : ℕ) (hc : 2 ≤ c) (hd : 0 < d)
    (scatter : BundleWidthScatter.Layout s A n d c)
    (afterWidths : (s 4).val + 2*((n*d)*(s 3).val) ≤ start)
    (room : start+2*((n*d)*(s 3).val)+2*(n*d)+2*((n*d)*pieceCount d c) < 2^w) :
    let B := n*d
    let Q := pieceCount d c
    let t := BundlePrefixGraph.prefixPublic s B d c start false
    let u := BundlePrefixGraph.prefixPublic s B d c start true
    let base := start+2*(B*(s 3).val)+2*B
    let p := packedPublic (t 4) B Q base
    BundlePrefixGraph.RowLayout s t u A n d c ∧ ABWidths.Layout p B ∧ (p 0).val = Q ∧ p 2 = t 4 ∧
      ∀ z ∈ [t,u], ∀ i ∈ ([2,3] : List (Fin 5)), Outside p B (z i).val (B*(z 1).val) := by
  intro B Q t u base p
  let size := B*(s 3).val
  change start+2*size+2*B+2*(B*Q) < 2^w at room
  change (s 4).val+2*size ≤ start at afterWidths
  have fit : start+2*size+2*B < 2^w := by omega
  have tables := BundlePrefixGraph.RowLayout.packed s A n d c start hc hd scatter afterWidths fit
  have hw : Q < 2^w := scatter.slots.trans_lt (s 3).isLt
  have hpos : 0 < Q := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hc
    change 0 < 3*(2^(2+j)*d)/4
    rw [pow_add, show 2^2 = 4 by decide]
    have := Nat.mul_pos (Nat.two_pow_pos j) hd
    rw [Nat.mul_assoc 4]
    omega
  have tStart : (t 3).val = start := by
    change start % (2^w) = start; exact Nat.mod_eq_of_lt (by omega)
  have uStart : (u 3).val = start+size := by
    change (start+size) % (2^w) = _; exact Nat.mod_eq_of_lt (by omega)
  have tTotal : (t 4).val = start+2*size := by
    change (start+2*size) % (2^w) = _; exact Nat.mod_eq_of_lt (by omega)
  have tWidth : (t 2).val = (s 4).val := congrArg Fin.val tables.thickBase
  have uWidth : (u 2).val = (s 4).val+size := tables.motifBase
  have tStride : (t 1).val = (s 3).val := rfl
  have uStride : (u 1).val = (s 3).val := rfl
  have htotal : (t 4).val+B ≤ base := by change _ ≤ start+2*size+2*B; omega
  refine ⟨tables, packedLayout _ _ _ _ hpos hw htotal room,Nat.mod_eq_of_lt hw,rfl,?_⟩
  intro z hz i hi
  apply packedOutside _ _ room
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hi
  rcases hz with rfl|rfl <;> rcases hi with rfl|rfl
  all_goals
    first | rw [tStride] | rw [uStride]
    first | rw [tWidth] | rw [uWidth] | rw [tStart] | rw [uStart]
    change _ + size ≤ start+2*size+2*B
    omega

end CompressorRecords.DemandWidths

end VPVNP
end Computability
end OAI
