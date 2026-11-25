import OAI.Hierarchy.DescentPackedMatchedInput
import OAI.Hierarchy.DescentPackedMatchingTable
import Mathlib.Data.Nat.Log

namespace OAI
/-! # A polynomial-size local shape for every packed matching panel -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {r D p d : ℕ}

def binCount (r D : ℕ) := 1+D*r
def entryCount (r D p : ℕ) := r*(binCount r D)*p
def digitWidth (r D p profile : ℕ) :=
  max profile (Nat.clog 2 (2+entryCount r D p+binCount r D+(D+1)*r+r*p))

def shape (r D p profile : ℕ) : Shape :=
  ⟨r,binCount r D,entryCount r D p,entryCount r D p,digitWidth r D p profile⟩

theorem shape_width (r D p profile : ℕ) :
    entryCount r D p < 2^(digitWidth r D p profile) ∧
    binCount r D ≤ 2^(digitWidth r D p profile) ∧
    (D+1)*r+r*p < 2^(digitWidth r D p profile) ∧ profile≤digitWidth r D p profile := by
  let n:=2+entryCount r D p+binCount r D+(D+1)*r+r*p
  have bound : n≤2^(digitWidth r D p profile) := (Nat.le_pow_clog (by decide : 1<2) n).trans
    (Nat.pow_le_pow_right (by decide) (le_max_right ..))
  refine ⟨?_,?_,?_,le_max_left ..⟩ <;> dsimp only [n] at bound <;> omega

private theorem flat_length {I J : Type*} (xs : List I) (f : I→List J) (n : ℕ) (h : ∀i,(f i).length≤n) :
    (xs.flatMap f).length≤xs.length*n := by
  induction xs with
  | nil=>simp
  | cons a xs ih=>
    simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*n) n] using
      Nat.add_le_add (h a) ih

theorem site_length (u : Panel r D p d) (key : ℕ) (shade : Bool) : (sites u key shade).length≤r := by
  simpa only [sites,List.length_finRange] using List.length_filter_le _ (List.finRange r)

theorem bin_length (u : Panel r D p d) (x : Fin r) (b : ℕ) : (atBin u x b).length≤p := by
  unfold atBin
  simpa only [List.length_map,List.length_finRange] using List.length_filter_le _ (List.finRange p)

theorem thin_length (u : Panel r D p d) (bins key : ℕ) : (thinStream u bins key).length≤r*bins*p := by
  have cols (x : Fin r) : (inBlock u bins x).length≤bins*p := by
    simpa only [inBlock,List.length_finRange] using flat_length (List.finRange bins) (fun b=>atBin u x b.val) p (fun b=>bin_length u x b.val)
  have sites_:=site_length u key false
  exact (flat_length (sites u key false) _ _ cols).trans ((Nat.mul_le_mul_right _ sites_).trans_eq (Nat.mul_assoc ..).symm)

theorem thick_bin_length (u : Panel r D p d) (key b : ℕ) : (thickBins u key b).length≤r*p :=
  (flat_length (sites u key true) (fun x=>atBin u x b) p (fun x=>bin_length u x b)).trans
    (Nat.mul_le_mul_right p (site_length u key true))

private theorem partial_sum {I : Type*} (f : I→ℕ) (xs : List I) (n : ℕ) :
    (∑i : Fin n,((xs[i.val]?).map f).getD 0)≤DescentPacking.amount f xs := by
  induction xs generalizing n with
  | nil=>simp [DescentPacking.amount]
  | cons x xs ih=>
    cases n with
    | zero=>simp
    | succ n=>
      rw [Fin.sum_univ_succ]
      simpa only [Fin.val_zero,Fin.val_succ,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.map_some,
        Option.getD_some,DescentPacking.amount,List.map_cons,List.sum_cons] using Nat.add_le_add_left (ih n) (f x)

private theorem amount_flat {I : Type*} (load : I→ℕ) (ps : List (List I)) :
    DescentPacking.amount (DescentPacking.amount load) ps=DescentPacking.amount load ps.flatten := by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    simpa only [DescentPacking.amount,List.map_cons,List.sum_cons,List.flatten_cons,List.map_append,List.sum_append] using
      congrArg (DescentPacking.amount load p+·) ih

theorem raw_need_sum (s : Shape) (B key : ℕ) (u : Panel r D p d) :
    (∑i : Fin s.packs,(((packs u s.bins B key)[i.val]?).map (DescentPacking.amount (countAt u s.bins))).getD 0)≤r*s.bins*p := by
  let load:=countAt u s.bins
  let ps:=packs u s.bins B key
  calc
    _ ≤ DescentPacking.amount (DescentPacking.amount load) ps := partial_sum _ _ _
    _ = DescentPacking.amount load ps.flatten := amount_flat load ps
    _ = (thinStream u s.bins key).length := by
      rw [show ps.flatten=sites u key false from thinPacks_flatten ..,local_amount]
      rfl
    _ ≤ _ := thin_length u _ _

theorem need_sum (s : Shape) (B key : ℕ) (u : Panel r D p d) (pf : Fin s.pairs→Cell s.digit) :
    (∑i,need (inputs s B key u pf) i)≤r*s.bins*p :=
  (Finset.sum_le_sum (fun (i : Fin s.packs) _=>Nat.mod_le
    ((((packs u s.bins B key)[i.val]?).map (DescentPacking.amount (countAt u s.bins))).getD 0) (2^s.digit))).trans
    (raw_need_sum s B key u)

theorem need_read (profile B key : ℕ) (u : Panel r D p d) (pf : Fin (shape r D p profile).pairs→Cell (shape r D p profile).digit)
    (j : Fin (shape r D p profile).packs) :
    let s:=shape r D p profile
    need (inputs s B key u pf) j=(((packs u s.bins B key)[j.val]?).map (DescentPacking.amount (countAt u s.bins))).getD 0 := by
  let s:=shape r D p profile
  let weight (i : Fin s.packs):=(((packs u s.bins B key)[i.val]?).map (DescentPacking.amount (countAt u s.bins))).getD 0
  have weight_le := Finset.single_le_sum (f:=weight) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  exact Nat.mod_eq_of_lt ((weight_le.trans (raw_need_sum s B key u)).trans_lt (shape_width r D p profile).1)

theorem cap_read (profile B key : ℕ) (u : Panel r D p d) (pf : Fin (shape r D p profile).pairs→Cell (shape r D p profile).digit)
    (b : Fin (shape r D p profile).bins) :
    cap (inputs (shape r D p profile) B key u pf) b=(thickBins u key b.val).length := by
  have low : r≤r*binCount r D := by
    have extra:=Nat.mul_le_mul_left r (show 1≤binCount r D by unfold binCount;omega)
    simpa only [Nat.mul_one] using extra
  exact Nat.mod_eq_of_lt (((thick_bin_length u key b.val).trans (Nat.mul_le_mul_right p low)).trans_lt (shape_width r D p profile).1)

theorem packs_fit (u : Panel r D p d) (bins B key : ℕ) : (packs u bins B key).length≤r := by
  have bound (xs : List (Fin r)) : (thinPacks (countAt u bins) B xs).length≤xs.length := by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>
      cases h : thinPacks (countAt u bins) B xs with
      | nil => simp [thinPacks,h]
      | cons z zs =>
        rw [h,List.length_cons] at ih
        by_cases full : B ≤ DescentPacking.amount (countAt u bins) z
        · simpa only [thinPacks,h,ite_eq_left full,List.length_cons] using Nat.succ_le_succ ih
        · simpa only [thinPacks,h,ite_eq_right full,List.length_cons] using ih.trans (Nat.le_succ xs.length)
  exact (bound _).trans (site_length u key false)

theorem cap_sum (s : Shape) (B key : ℕ) (u : Panel r D p d) (pf : Fin s.pairs→Cell s.digit) :
    (∑b,cap (inputs s B key u pf) b)≤r*s.bins*p := by
  have h (b : Fin s.bins) : cap (inputs s B key u pf) b≤r*p :=
    (Nat.mod_le ..).trans (thick_bin_length u key b.val)
  calc
    _ ≤ ∑_ : Fin s.bins,r*p := Finset.sum_le_sum (fun b _=>h b)
    _ = _ := by simp; ring

theorem shape_bounded (profile B key : ℕ) (u : Panel r D p d)
    (pf : Fin (shape r D p profile).pairs→Cell (shape r D p profile).digit) :
    Bounded (inputs (shape r D p profile) B key u pf) := by
  let s:=shape r D p profile
  let x:=inputs s B key u pf
  have needBound : (∑i,need x i)≤ s.entries := need_sum s B key u pf
  have sizes:=shape_width r D p profile
  refine ⟨fun i=>?_,needBound,cap_sum s B key u pf,sizes.1,sizes.2.1⟩
  exact (Finset.single_le_sum (f:=need x) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans needBound

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
