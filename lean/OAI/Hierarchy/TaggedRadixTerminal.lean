import OAI.Hierarchy.TaggedFinalScan
import OAI.Hierarchy.TaggedRadixRecords
import OAI.Hierarchy.TaggedRadixOrder
import OAI.Hierarchy.TaggedRadixPins
import OAI.Hierarchy.TaggedFinalCorrect

namespace OAI
/-! # Reading the original tagged tensor from a physically sorted record array -/
noncomputable section
namespace Hierarchy.Tagged.RadixRecord
open ThreeFlat Routing
open scoped Classical
variable {h n : ℕ}

def entry (w : Bits (width h)) : FinalScan.Entry (2^h) (Bits h) :=
  (w (kind h),dataTag w)

private def packed (e : FinalScan.Entry (2^h) (Bits h)) : Bool × Bits (h+h) :=
  (e.1,packValue e.2)

private theorem paired_packed (xs : List (FinalScan.Entry (2^h) (Bits h))) :
    FinalScan.paired (xs.map packed) ↔ FinalScan.paired xs := by
  match xs with
  | [] => simp [FinalScan.paired]
  | [_] => simp [FinalScan.paired]
  | a::b::xs =>
    simp only [List.map_cons,FinalScan.paired,packed,(packValue_injective h).eq_iff,
      paired_packed xs]

private theorem initial_entries (x : Fin (pins h h)→Bool) :
    (realWords h (Sum.elim x id ∘ feed h)).map entry =
      FinalScan.input (source x) (tag x) (target x) := by
  rw [realWords_feed,List.map_ofFn]
  let left (i : Row h) : FinalScan.Entry (2^h) (Bits h) := (false,i,source x i)
  let right (i : Row h) : FinalScan.Entry (2^h) (Bits h) := (true,tag x i,target x i)
  have l (i : Row h) : entry (readFeed x (rowIndex h (.inl i))) = left i := by
    simp [entry,left,tag_data_feed]
  have r (i : Row h) : entry (readFeed x (rowIndex h (.inr i))) = right i := by
    simp [entry,right,tag_data_feed]
  have e : 2^h+2^h=2^(h+1) := by rw [pow_succ]; omega
  rw [List.ofFn_congr e.symm]
  change List.ofFn (fun i : Fin (2^h+2^h) => entry (readFeed x (Fin.cast _ i))) = _
  have fuse : (fun i : Fin (2^h+2^h) => entry (readFeed x (Fin.cast e i))) = Fin.append left right := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact l i
    · rw [Fin.append_right]
      exact r i
  rw [fuse,List.ofFn_fin_append]
  simp only [FinalScan.input,FinalScan.sources,FinalScan.targets,List.map_ofFn,left,right,
    Function.comp_def]

def scanField (h : ℕ) : FinalScan.Fields (h+h) → Fin (width h)
  | none => real h
  | some none => kind h
  | some (some j) => Fin.addCases (keyField h) (dataField h) j

def scan (F : Type*) [Zero F] [One F] (n h : ℕ) :
    BitNetwork F (Fintype.card (Fin n × Fin (width h))) :=
  RadixStage.pullPins (FinalScan.network F n (h+h)) (fun p => .inl (p.1,scanField h p.2))

private theorem word_fields (w : Bits (width h)) :
    (fun j : Fin (h+h) => w (scanField h (some (some j)))) = packValue (dataTag w) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [scanField,packValue,dataTag,Function.comp_def]
  rw [show i.addNat h=Fin.natAdd h i from Fin.ext (Nat.add_comm _ _)]
  simp only [Fin.addCases_right,Fin.append_right]

private theorem rows_project (x : Fin n × Fin (width h)→Bool) :
    FinalScan.rows (fun j : FinalScan.Ports n (h+h) => x (j.1,scanField h j.2)) =
      ((realWords h x).map entry).map packed := by
  let w (i : Fin n) : Bits (width h) := fun j => x (i,j)
  let list := List.ofFn (id : Fin n→Fin n)
  have s : List.ofFn w = list.map w := by simp [list,List.map_ofFn]
  change list.filterMap (fun i => if w i (real h) then
    some (w i (kind h),fun j => w i (scanField h (some (some j)))) else none) = _
  simp_rw [word_fields]
  change list.filterMap (fun i => if w i (real h) then some (packed (entry (w i))) else none) =
    (((List.ofFn w).filter (fun q => q (real h))).map entry).map packed
  rw [s]
  induction list with
  | nil => rfl
  | cons i l ih => cases yes : w i (real h) <;> simp [yes,ih]

private theorem order_entry {l : List (Bits (width h))}
    (a : (l.map keyValue).Pairwise (·≤·)) :
    ((l.map entry).map FinalScan.sortKey).Pairwise (·≤·) := by
  rw [List.map_map,List.pairwise_map]
  apply (List.pairwise_map.mp a).imp
  intro x y le
  have k := (Radix.flagged_key_order (dataTag x).1.val (dataTag y).1.val (x (kind h)) (y (kind h))).mp le
  change toLex ((dataTag x).1,x (kind h)) ≤ toLex ((dataTag y).1,y (kind h))
  rw [Prod.Lex.toLex_le_toLex] at k ⊢
  rcases k with lt | ⟨eq,right⟩
  · exact Or.inl lt
  · exact Or.inr ⟨Fin.ext eq,right⟩

theorem scan_finish (F : Type*) [_root_.Field F] (hh : 0<h) (x : Fin (pins h h)→Bool)
    (y : Fin n × Fin (width h)→Bool)
    (perm : (realWords h y).Perm (realWords h (Sum.elim x id ∘ feed h)))
    (order : ((realWords h y).map keyValue).Pairwise (·≤·)) :
    TypedWiring.value (scan F n h) y = coeff F h h x := by
  let l := (realWords h y).map entry
  have all : l.Perm (FinalScan.input (source x) (tag x) (target x)) := by
    rw [← initial_entries x]
    exact perm.map entry
  have sound := FinalScan.valid_iff_terminal (source x) (tag x) (target x) l all (order_entry order)
  rw [scan,RadixStage.pullPins_value,FinalScan.eval F (by omega : 0<h+h)]
  change (if FinalScan.paired (FinalScan.rows (fun j : FinalScan.Ports n (h+h) =>
      y (j.1,scanField h j.2))) then (1:F) else 0) = _
  rw [rows_project,paired_packed,← sound]
  rfl

theorem scan_size (F : Type*) [Zero F] [One F] (n h : ℕ) :
    (scan F n h).cells+(scan F n h).internal ≤ 11000*(h+h)*(n+2) := by
  simpa [scan,RadixStage.pullPins] using (FinalScan.size F n (h+h))

theorem scan_room (F : Type*) [Zero F] [One F] {n h : ℕ} (volume : n≤2*2^(h+1)) :
    (scan F n h).cells+(scan F n h).internal+pins h h ≤ 132003*(2^h*h) := by
  rw [pow_succ] at volume
  have one : 1 ≤ 2^h := Nat.two_pow_pos h
  have span : n+2 ≤ 6*(2^h) := by omega
  have bound := (scan_size F n h).trans (Nat.mul_le_mul_left _ span)
  have total : pins h h = 3*(2^h*h) := by unfold pins; ring
  rw [total]
  nlinarith only [bound]

end Hierarchy.Tagged.RadixRecord

end
end OAI
