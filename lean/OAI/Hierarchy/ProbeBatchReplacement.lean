import OAI.Hierarchy.ProbeLocalReplacement
import OAI.Hierarchy.ProbeHistogram
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking
import OAI.ThreeFlat.Diagonal.TraceCircuitArray

namespace OAI
/-! # Replacing a batch on a failed price ball -/

noncomputable section
namespace Hierarchy.Probe

open scoped BigOperators Classical
open LinearAlgebra.SpectralBooks
open LinearAlgebra.SpectralBooks.SiteTensor
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms

variable {k : ℕ} {F E A : Type*} [Field F] [Nonempty (Fin k)] [Fintype E] [Fintype A]

omit [Fintype E] [Fintype A] in
/-- Zero-priced demands already attain equality under their upper bound.
They can be omitted when forming the tensor of demands in a replacement. -/
theorem failed_positive_demands (edge : E → Chord k) (req : A → E) (cost : E → ℝ)
    (nonneg : ∀ e, 0 ≤ cost e) :
    Failed F edge req cost ↔ Failed F edge
      (fun a : {a : A // 0 < cost (req a)} => req a.val) cost := by
  constructor
  · rintro full ⟨φ,t,ht,upper,tight⟩
    refine full ⟨φ,t,ht,upper,fun a => ?_⟩
    by_cases pos : 0 < cost (req a)
    · exact tight ⟨a,pos⟩
    · have hz : cost (req a) = 0 := le_antisymm (le_of_not_gt pos) (nonneg _)
      apply le_antisymm (upper _)
      rw [hz]
      exact mul_nonneg ht (rawLogPrice_nonneg φ zero_le_one _)
  · rintro pos ⟨φ,t,ht,upper,tight⟩
    exact pos ⟨φ,t,ht,upper,fun a => tight a.val⟩

/-- A local identity, including its exact number of options, bit demand,
option widths, and coefficients on the original demand ports. -/
structure Packet (F : Type*) [Field F] (edge : E → Chord k) (req : A → E) where
  width : ℕ
  selectorBits : ℕ
  terms : ℕ
  encoding : terms ≤ 2^selectorBits
  count : Fin terms → E → ℕ
  coeff : Fin terms → (∀ i, State (width • demandWidths edge req) i) → F
  identity : (raw F (width • demandWidths edge req)).coeff = ∑ j, coeff j
  images : ∀ j, ({raw F (width • demandWidths edge req) with coeff := coeff j} :
    Raw (Fin k) F).Restricts (raw F (optionWidths edge (count j)))

/-- The same packet applies to every batch size. The cost counts the chosen
number of bits of every option and broadcasts each full selector word over
a fixed tree of total length `tree`. The saving per demand bit is positive
and uniform over all histograms. -/
theorem exists_paid_packet [Nonempty E] (edge : E → Chord k) (req : A → E)
    (cost : E → ℝ) (nonneg : ∀ e, 0 ≤ cost e) (conn : Connected edge)
    (failed : Failed F edge req cost) (tree : ℝ) (htree : 0 ≤ tree) (N : ℕ) :
    ∃ (P : Packet F edge req) (price : ℝ), N < P.width ∧ price < ∑ a, cost (req a) ∧
      ∀ t (hist : Histogram (Fin P.terms) t),
        (∑ e, (histWidth P.count hist e : ℝ)*cost e) + t*(tree*P.selectorBits) ≤
          t*(P.width*price) := by
  obtain ⟨B,hB,tiles⟩ := exists_local_replacement edge req cost nonneg conn failed
  obtain ⟨η,hη,rate⟩ := selector_rate hB htree
  obtain ⟨b,s,hb,hs,l,hl,z,hz,hterm⟩ := tiles η hη N
  choose count hcost hmaps using hterm
  refine ⟨⟨b,s,l,hl,count,z,hz,hmaps⟩,((∑ a, cost (req a))+B)/2,hb,?_,?_⟩
  · linarith only [hB]
  · intro t hist
    change (∑ e, (histWidth count hist e : ℝ)*cost e) + t*(tree*s) ≤ _
    calc
      _ ≤ t*(b*B) + t*(tree*s) :=
        add_le_add (histogram_cost count cost hcost hist) le_rfl
      _ = t*(b*B + tree*s) := (mul_add ..).symm
      _ ≤ t*(b*(((∑ a, cost (req a))+B)/2)) :=
        mul_le_mul_of_nonneg_left (rate b s hs) (Nat.cast_nonneg t)

/-- A compact family of failed tests of one fixed option format admits a
finite catalogue of actual packets, even when the list of positively priced
demands changes with the proposed price vector. Every use preserves uniform
positive slack in both its saving and the unit prices of its selected demands. -/
theorem exists_packet_catalogue {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {D : X → Type*} [∀ x, Fintype (D x)] [Nonempty E] (edge : E → Chord k)
    (req : (x : X) → D x → E) (cost : X → E → ℝ)
    (nonneg : ∀ x e, 0 ≤ cost x e) (cont : ∀ e, Continuous (fun x => cost x e))
    (positive : ∀ x a, 0 < cost x (req x a))
    (conn : Connected edge) (failed : ∀ x, Failed F edge (req x) (cost x))
    (tree : ℝ) (htree : 0 ≤ tree) (N : ℕ) :
    ∃ (S : Finset X) (P : (j : S) → Packet F edge (req j.val)) (γ : ℝ), 0 < γ ∧
      (∀ j, N < (P j).width) ∧ ∀ x : X, ∃ j : S, (∀ a, γ ≤ cost x (req j.val a)) ∧
        ∀ t (hist : Histogram (Fin (P j).terms) t),
          (∑ e, (histWidth (P j).count hist e : ℝ)*cost x e) + t*(tree*(P j).selectorBits) ≤
            t*((P j).width*((∑ a : D j.val, cost x (req j.val a))-γ)) := by
  classical
  choose pkt price wide saving paid using fun x =>
    exists_paid_packet edge (req x) (cost x) (nonneg x) conn (failed x) tree htree N
  let total (c x : X) := ∑ a, cost x (req c a)
  have stock (x : X) : ∃ δ : ℝ, 0 < δ ∧ ∀ a, δ < cost x (req x a) := by
    let p : Option (D x) → ℝ := Option.elim' 1 (fun a => cost x (req x a))
    obtain ⟨i,_,least⟩ := Finset.univ.exists_min_image p Finset.univ_nonempty
    have hp : 0 < p i := by cases i with
                              | none => exact zero_lt_one
                              | some a => exact positive x a
    exact ⟨p i/2,half_pos hp,fun a => (half_lt_self hp).trans_le (least (some a) (Finset.mem_univ _))⟩
  choose δ dpos dsmall using stock
  let margin (x : X) := min ((total x x - price x)/2) (δ x)
  have mpos (x : X) : 0 < margin x := lt_min (half_pos (sub_pos.mpr (saving x))) (dpos x)
  let U (c : X) : Set X := (⋂ j : Fin (pkt c).terms,
    {y | (∑ e, ((pkt c).count j e : ℝ)*cost y e) + tree*(pkt c).selectorBits <
      (pkt c).width*(total c y - margin c)}) ∩ (⋂ a : D c, {y | margin c < cost y (req c a)})
  have op (c : X) : IsOpen (U c) := by
    apply IsOpen.inter
    · apply isOpen_iInter_of_finite
      intro j
      exact isOpen_lt ((continuous_finsetSum _ fun e _ => continuous_const.mul (cont e)).add
        continuous_const) (continuous_const.mul ((continuous_finsetSum _ fun a _ => cont (req c a)).sub
        continuous_const))
    · exact isOpen_iInter_of_finite (fun a => isOpen_lt continuous_const (cont (req c a)))
  have mem (c : X) : c ∈ U c := by
    refine ⟨Set.mem_iInter.mpr (fun j => ?_), Set.mem_iInter.mpr
      (fun a => (min_le_right _ _).trans_lt (dsmall c a))⟩
    have h := paid c 1 (histogram (fun _ : Fin 1 => j))
    simp only [histogram_width,totalWidth,Fin.sum_univ_one,Nat.cast_one,one_mul] at h
    change _ < (pkt c).width*(total c c - margin c)
    apply lt_of_le_of_lt h
    apply mul_lt_mul_of_pos_left _ (by exact_mod_cast (Nat.zero_le N).trans_lt (wide c))
    have gap : price c < total c c := saving c
    have half : margin c ≤ (total c c - price c)/2 := min_le_left _ _
    linarith only [gap,half]
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover U op
    (fun x _ => Set.mem_iUnion.mpr ⟨x,mem x⟩)
  have chooseIndex (x : X) : ∃ j ∈ S, x ∈ U j := by
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ x))
    obtain ⟨hj,hx⟩ := Set.mem_iUnion.mp hj
    exact ⟨j,hj,hx⟩
  obtain ⟨j₀,hj₀,_⟩ := chooseIndex (Classical.arbitrary X)
  obtain ⟨jmin,_,least⟩ := S.exists_min_image margin ⟨j₀,hj₀⟩
  refine ⟨S,fun j => pkt j.val,margin jmin,mpos _,fun j => wide j.val,?_⟩
  intro x
  obtain ⟨j,hj,hx⟩ := chooseIndex x
  have positive_at (a : D j) : margin j < cost x (req j a) := Set.mem_iInter.mp hx.2 a
  refine ⟨⟨j,hj⟩,fun a => (least j hj).trans (positive_at a).le,?_⟩
  intro t hist
  let cap := (pkt j).width*(total j x - margin jmin)
  let fee := tree*(pkt j).selectorBits
  have bound (i : Fin (pkt j).terms) : (∑ e, ((pkt j).count i e : ℝ)*cost x e) ≤ cap-fee := by
    have hi := Set.mem_iInter.mp hx.1 i
    change (∑ e, ((pkt j).count i e : ℝ)*cost x e) + fee < (pkt j).width*(total j x-margin j) at hi
    apply (le_sub_iff_add_le).mpr
    exact hi.le.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left (least j hj) _) (Nat.cast_nonneg _))
  have h := histogram_cost (pkt j).count (cost x) bound hist
  change _ + t*fee ≤ t*cap
  exact (add_le_add h (le_refl ((t : ℝ)*fee))).trans_eq (by ring)

omit [Nonempty (Fin k)] in
/-- Exact coefficient expansion of a paid packet after the public histogram is
chosen. The local matrices are fixed once, independently of the batch size. -/
theorem Packet.batch {edge : E → Chord k} {req : A → E} (P : Packet F edge req) :
    let a := P.width • demandWidths edge req
    let U (h : Fin P.terms) := optionWidths edge (P.count h)
    ∃ M : ∀ h i, State a i → State (U h) i → F,
      ∀ (t : ℕ) (x : ∀ i, State (∑ _ : Fin t, a) i),
      (raw F (∑ _ : Fin t, a)).coeff x =
        ∑ hist : Histogram (Fin P.terms) t, ∑ w : {w : Fin t → Fin P.terms // histogram w = hist},
          ∑ y : ∀ i, State (∑ j, U (w.1 j)) i,
            (raw F (∑ j, U (w.1 j))).coeff y *
              ∏ i, tiledTable (g := fun _ : Fin t => a) (fun j => M (w.1 j)) i (x i) (y i) :=
  histogram_batch _ _ P.coeff P.identity P.images

omit [Nonempty (Fin k)] in
/-- The fixed public branch uses one installed state space. The selected
complete word affects only the local table addresses in its contraction. -/
theorem Packet.batch_fixed {edge : E → Chord k} {req : A → E} (P : Packet F edge req) :
    let a := P.width • demandWidths edge req
    let U (w : Fin P.terms) := optionWidths edge (P.count w)
    ∃ M : ∀ h i, State a i → State (U h) i → F, ∀ (t : ℕ) (x : ∀ i, State (∑ _ : Fin t, a) i),
      (raw F (∑ _ : Fin t, a)).coeff x =
        ∑ h : Histogram (Fin P.terms) t, ∑ y : ∀ i, State (installed U h) i,
          (raw F (installed U h)).coeff y *
            (∑ w : {w : Fin t → Fin P.terms // histogram w = h},
              ∏ i, tiledTable (g := fun _ : Fin t => a) (fun j => M (w.1 j)) i
                (x i) (cast (congrArg (fun B => State B i) (word_installed U h w).symm) (y i))) :=
  histogram_batch_fixed _ _ P.coeff P.identity P.images

/-- These particular one-copy entries are shared by the ordinary signed
identity, the broadcast restriction and every site hardware instantiation. -/
def Packet.siteMatrices {edge : E → Chord k} {req : A → E} (P : Packet F edge req)
    (j : Fin P.terms) (i : Fin k) :
    State (P.width • demandWidths edge req) i → State (optionWidths edge (P.count j)) i → F :=
  P.batch_fixed.choose j i

/-- The ordinary choices have a fixed injective binary encoding. Padding
patterns above the actual alphabet are rejected. -/
def Packet.encode {edge : E → Chord k} {req : A → E} (P : Packet F edge req) :
    Fin P.terms ↪ Fin (2^P.selectorBits) := Fin.castLEEmb P.encoding

def Packet.decode {edge : E → Chord k} {req : A → E} (P : Packet F edge req)
    (i : Fin (2^P.selectorBits)) : Option (Fin P.terms) :=
  if h : i.val < P.terms then some ⟨i.val,h⟩ else none

omit [Nonempty (Fin k)] in
@[simp] theorem Packet.decode_encode {edge : E → Chord k} {req : A → E} (P : Packet F edge req)
    (i : Fin P.terms) : P.decode (P.encode i) = some i := by
  simp [Packet.decode,Packet.encode,i.isLt]

open ThreeFlat.Diagonal in
/-- The word placed on each broadcast edge consists of the actual binary
selector fields, in copy order, exactly as read by the header network. -/
def Packet.selectorWord {edge : E → Chord k} {req : A → E} (P : Packet F edge req) (t : ℕ) :
    (Fin t → Fin P.terms) ↪ Fin (2^(t*P.selectorBits)) where
  toFun w := MotifBinaryPacking.word _ (TraceCircuit.blocks t P.selectorBits
    (fun i => (MotifBinaryPacking.word P.selectorBits).symm (P.encode (w i))))
  inj' := by
    intro x y eq
    have blocks := (MotifBinaryPacking.word _).injective eq
    have fields := (TraceCircuit.blocks t P.selectorBits).injective blocks
    exact funext fun i => P.encode.injective
      ((MotifBinaryPacking.word P.selectorBits).symm.injective (congrFun fields i))

open ThreeFlat.Diagonal in
omit [Nonempty (Fin k)] in
theorem Packet.selectorWord_bits {edge : E → Chord k} {req : A → E} (P : Packet F edge req)
    (t : ℕ) (w : Fin t → Fin P.terms) :
    (MotifBinaryPacking.word (t*P.selectorBits)).symm (P.selectorWord t w) =
      TraceCircuit.blocks t P.selectorBits
        (fun i => (MotifBinaryPacking.word P.selectorBits).symm (P.encode (w i))) :=
  Equiv.symm_apply_apply _ _


end Hierarchy.Probe
end

end OAI
