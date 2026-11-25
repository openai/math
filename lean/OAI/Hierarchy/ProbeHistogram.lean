import OAI.LinearAlgebra.SpectralBooks.RawTiledTables
import OAI.ThreeFlat.Diagonal.MotifHistogram

namespace OAI
/-! # Histogram batching of the finite local replacements

The public branch records the histogram. The complete selector word is
summed internally; it determines the bit offsets within the installed
widths. This keeps the coefficient of each original word over the ground
field, including in positive characteristic. -/

noncomputable section

namespace Hierarchy.Probe

open scoped BigOperators Classical
open LinearAlgebra.SpectralBooks
open LinearAlgebra.SpectralBooks.ChordGraph
open LinearAlgebra.SpectralBooks.SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms

variable {k t : ℕ} {F H E : Type*} [Field F] [Fintype H] [DecidableEq H]

/-- The installed width of each chord is fixed by the outer histogram. -/
theorem histogram_wire_widths (U : H → Widths k) (word : Fin t → H) :
    ∑ j, U (word j) = ∑ h, ((histogram word).1 h).val • U h := by
  ext e
  simpa only [Finsupp.finsetSum_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_id,histWidth,totalWidth] using
    (histogram_width (fun h e => U h e) word e).symm

/-- Contracting equality wires along a connected network of sites broadcasts
one word. Each constant assignment occurs exactly once, with coefficient
one, so checking its histogram at the root preserves all multiplicities. -/
theorem broadcast_contraction {V P W : Type*} [Fintype V] [Fintype P] [Fintype W]
    [DecidableEq W] (src dst : P → V) (root : V)
    (connected : ∀ v, Relation.EqvGen (fun a b => ∃ p, src p=a ∧ dst p=b) root v)
    (f : (V → W) → F) :
    (∑ x : V → W, (∏ p, if x (src p)=x (dst p) then (1:F) else 0) * f x) =
      ∑ w : W, f (fun _ => w) := by
  classical
  let ok (x : V → W) := ∀ p, x (src p)=x (dst p)
  have constant (x : V → W) (hx : ok x) (v : V) : x root = x v := by
    suffices ∀ {a b}, Relation.EqvGen (fun a b => ∃ p, src p=a ∧ dst p=b) a b → x a=x b by
      exact this (connected v)
    intro a b h
    induction h with
    | rel a b hp => obtain ⟨p,rfl,rfl⟩ := hp; exact hx p
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
  let eqv : {x : V → W // ok x} ≃ W :=
    { toFun := fun x => x.val root
      invFun := fun w => ⟨fun _ => w, fun _ => rfl⟩
      left_inv := fun x => Subtype.ext (funext (constant x x.property))
      right_inv := fun _ => rfl }
  simp only [Fintype.prod_boole,ite_mul,one_mul,zero_mul]
  change (∑ x : V → W, if ok x then f x else 0) = _
  rw [← Finset.sum_filter,← Finset.sum_subtype_eq_sum_filter,Finset.subtype_univ]
  apply Fintype.sum_equiv eqv
  intro x
  exact congrArg f (funext (fun v => (constant x x.property v).symm))

private theorem sum_change_enumeration {X K : Type*} [AddCommMonoid K] (A B : Fintype X) (f : X→K) :
    (@Finset.univ X A).sum f=(@Finset.univ X B).sum f :=
  congrArg (fun d : Fintype X=>(@Finset.univ X d).sum f) (Subsingleton.elim A B)

private theorem raw_tables_enumerated (X Y : Raw.{0} (Fin k) F)
    (enum : Fintype (∀i,Y.Leg i)) (h : X.Restricts Y) :
    ∃M : ∀i,X.Leg i→Y.Leg i→F,∀x,X.coeff x=(@Finset.univ _ enum).sum
      (fun y=>Y.coeff y * ∏i,M i (x i) (y i)) := by
  obtain ⟨M,entries⟩:=h
  refine ⟨M,fun x=>(entries x).trans ?_⟩
  exact sum_change_enumeration _ enum _

private theorem one_copy_tables (a b : Widths k) (z : (∀ i, State a i)→F)
    (restricts : ({raw F a with coeff:=z} : Raw (Fin k) F).Restricts (raw F b)) :
    ∃ M : ∀ i,State a i→State b i→F, ∀ x,z x=∑y : ∀i,State b i,
      (raw F b).coeff y * ∏i,M i (x i) (y i) :=
  raw_tables_enumerated {raw F a with coeff:=z} (raw F b)
    (inferInstanceAs (Fintype (∀i,State b i))) restricts

set_option maxHeartbeats 1000000 in
/-- Each full word contributes the contraction of the original local matrices,
with their actual coefficients. Mixed-radix splitting at the two ends of a
wire uses the same offset. -/
theorem histogram_batch (a : Widths k) (U : H → Widths k)
    (z : H → (∀ i, State a i) → F)
    (hz : (raw F a).coeff = ∑ h, z h)
    (restricts : ∀ h, ({raw F a with coeff := z h} : Raw (Fin k) F).Restricts (raw F (U h))) :
    ∃ M : ∀ h i, State a i → State (U h) i → F,
      ∀ (t : ℕ) (x : ∀ i, State (∑ _ : Fin t, a) i),
      (raw F (∑ _ : Fin t, a)).coeff x =
        ∑ hist : Histogram H t, ∑ w : {w : Fin t → H // histogram w = hist},
          ∑ y : ∀ i, State (∑ j, U (w.1 j)) i,
            (raw F (∑ j, U (w.1 j))).coeff y *
              ∏ i, tiledTable (g := fun _ : Fin t => a) (fun j => M (w.1 j)) i (x i) (y i) := by
  choose M hM using (fun h=>one_copy_tables a (U h) (z h) (restricts h))
  refine ⟨M,fun t x => ?_⟩
  let value (w : Fin t → H) := ∑ y : ∀ i, State (∑ j, U (w j)) i,
    (raw F (∑ j, U (w j))).coeff y * ∏ i,
      tiledTable (g := fun _ : Fin t => a) (fun j => M (w j)) i (x i) (y i)
  have terms : (raw F (∑ _ : Fin t, a)).coeff x = ∑ w, value w :=
    raw_tiled_sum (J := fun _ : Fin t => H) (fun _ => a) (fun _ => U)
      (fun _ => z) (fun _ => M) (fun _ => hz) (fun _ => hM) x
  exact terms.trans (Fintype.sum_fiberwise (fun w : Fin t → H => histogram w) value).symm

/-- All words in one public branch use this same installed wire tensor. -/
def installed (U : H → Widths k) (h : Histogram H t) : Widths k :=
  ∑ a, ((h.1 a).val) • U a

theorem word_installed (U : H → Widths k) (h : Histogram H t)
    (w : {w : Fin t → H // histogram w = h}) :
    ∑ j, U (w.1 j) = installed U h :=
  (histogram_wire_widths U w.1).trans (congrArg (installed U) w.2)

/-- Split the fixed histogram wire using the prefix widths of the chosen
hidden word. Casting the index preserves its integer value. -/
def readBlock (U : H → Widths k) (h : Histogram H t)
    (w : {w : Fin t → H // histogram w = h}) (e : Chord k) (a : Index (installed U h) e)
    (j : Fin t) : Index (U (w.1 j)) e :=
  blockWireIndex (fun m => U (w.1 m)) e
    (Fin.cast (congrArg (fun B : Widths k => 2^(B e)) (word_installed U h w).symm) a) j

/-- Each bit for the selected local table is a read of the installed wire at
the indicated integer prefix offset. There is no scan over basis states. -/
theorem readBlock_bit (U : H → Widths k) (h : Histogram H t)
    (w : {w : Fin t → H // histogram w = h}) (e : Chord k) (a : Index (installed U h) e)
    (j : Fin t) (b : Fin ((U (w.1 j)) e)) :
    (readBlock U h w e a j).val.testBit b =
      a.val.testBit (b.val + ∑ m : Fin j, (U (w.1 (Fin.castLE j.is_lt.le m))) e) :=
  blockWireIndex_testBit (fun m => U (w.1 m)) e
    (Fin.cast (congrArg (fun B : Widths k => 2^(B e)) (word_installed U h w).symm) a) j b

private theorem sum_reindex_width {B C : Widths k} (h : B = C)
    (g : (∀ i, State B i) → F) :
    (∑ y, (raw F B).coeff y * g y) =
      ∑ y : ∀ i, State C i, (raw F C).coeff y *
        g (fun i => cast (congrArg (fun a => State a i) h.symm) (y i)) := by
  subst C
  rfl

set_option maxHeartbeats 600000 in
/-- The hidden selector sum is contracted against one actual wire tensor of
fixed dimensions per histogram, even when two histograms have equal widths. -/
theorem histogram_batch_fixed (a : Widths k) (U : H → Widths k)
    (z : H → (∀ i, State a i) → F)
    (hz : (raw F a).coeff = ∑ h, z h)
    (restricts : ∀ h, ({raw F a with coeff := z h} : Raw (Fin k) F).Restricts (raw F (U h))) :
    ∃ M : ∀ h i, State a i → State (U h) i → F,
      ∀ (t : ℕ) (x : ∀ i, State (∑ _ : Fin t, a) i),
      (raw F (∑ _ : Fin t, a)).coeff x =
        ∑ h : Histogram H t, ∑ y : ∀ i, State (installed U h) i,
          (raw F (installed U h)).coeff y *
            (∑ w : {w : Fin t → H // histogram w = h},
              ∏ i, tiledTable (g := fun _ : Fin t => a) (fun j => M (w.1 j)) i
                (x i) (cast (congrArg (fun B => State B i) (word_installed U h w).symm) (y i))) := by
  obtain ⟨M,batch⟩ := histogram_batch a U z hz restricts
  refine ⟨M,fun t x => ?_⟩
  refine (batch t x).trans ?_
  apply Finset.sum_congr rfl
  intro h _
  conv_rhs =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact sum_reindex_width (word_installed U h w) _

/-- For a fixed alphabet the public selector takes at most one integer between
zero and the batch size per letter. -/
theorem histogram_card (t : ℕ) :
    Fintype.card (Histogram H t) ≤ 2^(Nat.clog 2 (t+1) * Fintype.card H) := by
  calc
    _ ≤ Fintype.card (H → Fin (t+1)) := Fintype.card_subtype_le _
    _ = (t+1)^Fintype.card H := by simp
    _ ≤ (2^Nat.clog 2 (t+1))^Fintype.card H :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) _) _
    _ = _ := (pow_mul _ _ _).symm

/-- The public selector has one fixed-width counter field per letter. -/
def histogramFields (h : Histogram H t) (i : H) : Fin (2^Nat.clog 2 (t+1)) :=
  (h.1 i).castLE (Nat.le_pow_clog (by decide) _)

/-- An admissible vector of counter words has an exact total and no field
outside the range of the batch. -/
def readHistogram (t : ℕ) (x : H → Fin (2^Nat.clog 2 (t+1))) : Option (Histogram H t) :=
  if small : ∀ i, (x i).val<t+1 then
    if total : ∑ i, (x i).val=t then some ⟨fun i => ⟨(x i).val,small i⟩,total⟩ else none
  else none

omit [DecidableEq H] in
@[simp] theorem readHistogram_fields (h : Histogram H t) :
    readHistogram t (histogramFields h) = some h := by
  have small (i : H) : (histogramFields h i).val<t+1 := (h.1 i).isLt
  have total : ∑ i, (histogramFields h i).val=t := h.2
  simp only [readHistogram,dite_eq_left small,dite_eq_left total]
  rfl

omit [DecidableEq H] in
theorem fields_of_readHistogram {x : H → Fin (2^Nat.clog 2 (t+1))} {h : Histogram H t}
    (ok : readHistogram t x = some h) : histogramFields h = x := by
  unfold readHistogram at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  obtain rfl := Option.some.inj ok
  rfl

omit [DecidableEq H] in
/-- Every admitted histogram obeys the same batch cost. The estimate charges
all indexed options at their original prices, including zero prices. -/
theorem histogram_cost [Fintype E] (count : H → E → ℕ) (cost : E → ℝ)
    {B : ℝ} (budget : ∀ h, (∑ e, (count h e : ℝ)*cost e) ≤ B) (hist : Histogram H t) :
    (∑ e, (histWidth count hist e : ℝ)*cost e) ≤ t*B := by
  calc
    _ = ∑ h, (hist.1 h).val * (∑ e, (count h e : ℝ)*cost e) := by
      simp only [histWidth,Nat.cast_sum,Nat.cast_mul,Finset.sum_mul,Finset.mul_sum,mul_assoc]
      exact Finset.sum_comm
    _ ≤ ∑ h, ((hist.1 h).val : ℝ)*B := Finset.sum_le_sum fun h _ =>
      mul_le_mul_of_nonneg_left (budget h) (Nat.cast_nonneg _)
    _ = t*B := by rw [← Finset.sum_mul,← Nat.cast_sum,hist.2]

/-- Choose the local selector rate before the packet width. It leaves at
least half the per-bit saving after broadcasting the complete choice word
on a fixed tree of total length `tree`. -/
theorem selector_rate {B L tree : ℝ} (saving : B < L) (htree : 0 ≤ tree) :
    ∃ η : ℝ, 0 < η ∧ ∀ b s : ℕ, (s : ℝ) ≤ η*b →
      (b : ℝ)*B + tree*s ≤ b*((L+B)/2) := by
  let η := (L-B)/(2*(tree+1))
  have hgap : 0 < L-B := sub_pos.mpr saving
  have den : 0 < 2*(tree+1) := by positivity
  have hη : 0 < η := div_pos hgap den
  have hbase : tree*η ≤ (L-B)/2 := by
    have mul : η*(2*(tree+1)) = L-B := div_mul_cancel₀ _ den.ne'
    nlinarith only [mul,hη.le]
  refine ⟨η,hη,?_⟩
  intro b s hs
  have hb := Nat.cast_nonneg (α := ℝ) b
  have sb := mul_le_mul_of_nonneg_left hs htree
  have scale := mul_le_mul_of_nonneg_right hbase hb
  linarith only [sb,scale]

omit [DecidableEq H] in
/-- Broadcasting one fixed-length selector of cost `fee` per copy preserves
the strict saving if the local replacement already covers that charge. -/
theorem histogram_charged_cost [Fintype E] (count : H → E → ℕ) (cost : E → ℝ)
    {B fee L : ℝ} (budget : ∀ h, (∑ e, (count h e : ℝ)*cost e) ≤ B)
    (saving : B+fee<L) (ht : 0<t) (hist : Histogram H t) :
    (∑ e, (histWidth count hist e : ℝ)*cost e) + t*fee < t*L := by
  calc
    _ ≤ t*B+t*fee := add_le_add (histogram_cost count cost budget hist) le_rfl
    _ = t*(B+fee) := (mul_add ..).symm
    _ < t*L := mul_lt_mul_of_pos_left saving (by exact_mod_cast ht)


end Hierarchy.Probe
end

end OAI
