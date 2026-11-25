import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.NearSquareRoot.BoxScale
import OAI.Computability.NearSquareRoot.CRTTree

/-! # Size of a CRT table query on one complete control setting

Each axis descriptor contains its width and its modulus in unary. The varying
control setting contains one bit per selected address wire. All bounds below
use the size of the actual prefix-tree encoding consumed by a P192 task.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

private theorem controlBits_size (bits : List Bool) : size bits = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b l ih => simp only [size_cons, size_bit, ih, List.length_cons]; omega

/-- Exact encoded size, separating widths, moduli and list delimiters. -/
theorem descriptorList_size (ds : List (Tally × Tally)) :
    size ds = 2 * (ds.map (fun p => p.1.length)).sum +
      2 * (ds.map (fun p => p.2.length)).sum + 4 * ds.length + 1 := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    simp only [size_cons, size_prod, size_tally, List.map_cons, List.sum_cons,
      List.length_cons, ih]
    omega

private theorem moduli_sum_le (ds : List (Tally × Tally)) (b : ℕ)
    (hb : ∀ p ∈ ds, p.2.length ≤ b) :
    (ds.map (fun p => p.2.length)).sum ≤ ds.length * b := by
  induction ds with
  | nil => simp
  | cons p ds ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    exact (Nat.add_le_add (hb p List.mem_cons_self)
      (ih fun q hq => hb q (List.mem_cons_of_mem _ hq))).trans_eq (Nat.add_comm ..)

/-- One query, with the complete selected control setting attached. -/
theorem controlQuery_size_le (k b : ℕ) (ds : List (Tally × Tally)) (bits : List Bool)
    (hc : ds.length ≤ k) (hw : (ds.map (fun p => p.1.length)).sum ≤ k)
    (hb : ∀ p ∈ ds, p.2.length ≤ b) (ht : bits.length ≤ k) :
    size (ds, bits) ≤ 2 * (k * b) + 8 * k + 3 := by
  simp only [size_prod, descriptorList_size, controlBits_size]
  have hm := (moduli_sum_le ds b hb).trans (Nat.mul_le_mul_right b hc)
  omega

/-- A uniform polynomial covers all control settings, including the unary
expansions of all axis moduli. -/
theorem controlQuery_dom {ι : Type*} (k : ι → ℕ) (d : ι → List (Tally × Tally))
    (bits : ι → List Bool) (hc : ∀ i, (d i).length ≤ k i)
    (hw : ∀ i, ((d i).map (fun p => p.1.length)).sum ≤ k i)
    (hb : ∀ i p, p ∈ d i → p.2.length ≤ (2 * k i)^20)
    (ht : ∀ i, (bits i).length ≤ k i) :
    Dom k (fun i => size (d i, bits i)) := by
  have hk := Dom.base k
  have hpow := ((Dom.const k 2).mul hk).pow 20
  exact (((Dom.const k 2).mul (hk.mul hpow)).add ((Dom.const k 8).mul hk) |>.add
    (Dom.const k 3)).mono fun i => controlQuery_size_le _ _ _ _ (hc i) (hw i) (hb i) (ht i)

private theorem sublist_size_le {α : Type*} [Codec α] {s t : List α} (h : s.Sublist t) :
    size s ≤ size t := by
  induction h with
  | slnil => rfl
  | cons a _ ih => simp only [size_cons]; omega
  | cons_cons a _ ih => simp only [size_cons]; omega

/-- Restricting a full descriptor stream to the left children of a CRT level
preserves its polynomial size bound. -/
theorem controlSubquery_dom {ι : Type*} (k : ι → ℕ) (all control : ι → List (Tally × Tally))
    (bits : ι → List Bool) (hd : Dom k (fun i => size (all i)))
    (hs : ∀ i, (control i).Sublist (all i)) (ht : ∀ i, (bits i).length ≤ k i) :
    Dom k (fun i => size (control i, bits i)) := by
  apply ((hd.add ((Dom.const k 2).mul (Dom.base k))).add (Dom.const k 2)).mono
  intro i
  simp only [size_prod, controlBits_size]
  have := sublist_size_le (hs i)
  specialize ht i
  omega

/-- Encoded size of the complete box and a control word. -/
theorem validBoxQuery_dom {ι : Type*} (k : ι → ℕ) (box : ι → List (ℕ × ℕ))
    (bits : ι → List Bool) (hk : ∀ i, 1 < k i)
    (hb : ∀ i, BoxShape.Valid (k i) (BoxScale.width (k i)) (box i))
    (ht : ∀ i, (bits i).length ≤ k i) :
    Dom k (fun i => size ((box i).map (fun p => (tally p.1,tally p.2)), bits i)) := by
  let pack := fun p : ℕ × ℕ => (tally p.1, tally p.2)
  apply controlQuery_dom k (fun i => (box i).map pack) bits
  · intro i
    have hw : (box i).length ≤ ((box i).map Prod.fst).sum := by
      have hh := List.length_le_sum_of_one_le ((box i).map Prod.fst) (by
        intro w hm
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
        exact ((hb i).axisBounds _ hp).1)
      simpa using hh
    simpa only [List.length_map, (hb i).widthSum] using hw
  · intro i
    simpa only [List.map_map, Function.comp_def, pack, tally_length] using (hb i).widthSum.le
  · intro i d hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    simp only [pack, tally_length]
    obtain ⟨_, hwidth, _, hmod⟩ := (hb i).axisBounds _ hp
    exact (hmod.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hwidth)).trans
      (BoxScale.span_le (hk i))
  · exact ht

/-- At every depth of every valid coprime box, all complete control queries
obey the polynomial bound with the same constants. Depth and address bits may
both depend on the query. -/
theorem validLevelQueries_dom {ι : Type*} (k depth : ι → ℕ) (box : ι → List (ℕ × ℕ))
    (bits : ι → List Bool) (hk : ∀ i, 1 < k i)
    (hb : ∀ i, BoxShape.Valid (k i) (BoxScale.width (k i)) (box i))
    (ht : ∀ i, (bits i).length ≤ k i) :
    Dom k (fun i => size (((CRTTree.controls (depth i) (box i)).map
        (fun p => (tally p.1, tally p.2))), bits i)) := by
  let pack := fun p : ℕ × ℕ => (tally p.1, tally p.2)
  have H := validBoxQuery_dom k box bits hk hb ht
  exact H.mono fun i => by
    simp only [size_prod]
    have hs := (CRTTree.controls_sublist (depth i) (box i)).map pack
    exact Nat.add_le_add_right (Nat.add_le_add_right (sublist_size_le hs) _) _

/-- Compute the auxiliary rows and retain the exact control query under the
same polynomial clock. The cost includes copying the retained copy. -/
theorem attachGeneratedData {ι A B : Type*} [Codec A] [Codec B]
    {k : ι → ℕ} {query : ι → A} {generate : A → B}
    (hsize : Dom k (fun i => size (query i))) (hgen : Poly generate) :
    Task.BT k (fun i => send (query i)) (fun i => send (query i, generate (query i))) :=
  (Poly.identity.pair hgen).on hsize

end CRTTable

end NearSquareRoot
end Computability
end OAI
