import OAI.Hierarchy.ProtocolRAMPrices
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Native marking of sampler tiles from their live signed stock readings

For each possible integer stock the public table contains one threshold bit.
A scan checks signed directions in numerical order, and gives each tile to the
first direction that qualifies. The last extra row is permanently unavailable.
-/

namespace Hierarchy.ProtocolRAM.PurchaseMarks
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

variable {w n k : ℕ}

/-- The threshold is evaluated at the exact offer corresponding to the physical stock word. -/
def signedDirection (k : ℕ) : Fin (2*k) ≃ Fin k × Bool :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

def eligible (p : PhasePrice) (T : ℝ) (k kind bits : ℕ) : Bool :=
  decide (1/(4*(k:ℝ)) ≤ p.time*(AdaptiveProbe.rise p.M (p.quote kind bits)/T)^2)

def tableWords (p : PhasePrice) (T : ℝ) (k kind : ℕ) (table : Bank) : List ℕ :=
  List.ofFn (fun t : Fin table.size => (eligible p T k kind t.val).toNat)

def mount (p : PhasePrice) (T : ℝ) (k kind : ℕ) (table : Bank) (mem : Memory w) : Memory w :=
  fillSegment table.base table.size (fun a => ((eligible p T k kind (a-table.base)).toNat : Word w)) mem

def Table (p : PhasePrice) (T : ℝ) (k kind : ℕ) (table : Bank) (mem : Memory w) : Prop :=
  ∀ bits : Word w, table.read mem bits = ((eligible p T k kind (bits.val%table.size)).toNat : Word w)

theorem mount_table (p : PhasePrice) (T : ℝ) (k kind : ℕ) (table : Bank) (mem : Memory w) :
    Table p T k kind table (mount p T k kind table mem) := by
  intro bits
  have bound := Nat.mod_lt bits.val (Nat.two_pow_pos table.bits)
  change bits.val%table.size < table.size at bound
  have inside : table.base ≤ table.base+bits.val%table.size ∧ table.base+bits.val%table.size<table.base+table.size := by omega
  simp [Bank.read,mount,fillSegment,inside]

/-- Positive codes are signed-direction ordinals plus one. -/
def tag {d : ℕ} (hit : Fin d → Bool) : List (Fin d) → ℕ
  | [] => 0
  | j::js => if hit j then j.val+1 else tag hit js

def tagExpr {d : ℕ} (table : Bank) (stock : Fin d→Bank) : List (Fin d)→Expr
  | [] => .lit 0
  | j::js => .branch .eq (.lookup table (.lookup (stock j) .row)) (.lit 1)
      (.lit (j.val+1)) (tagExpr table stock js)

theorem tag_positive_iff {d : ℕ} (hit : Fin d→Bool) (js : List (Fin d)) :
    0 < tag hit js ↔ ∃ j∈js, hit j=true := by
  induction js with
  | nil => simp [tag]
  | cons j js ih => cases hj : hit j <;> simp [tag,hj,ih]

theorem hit_of_tag {d : ℕ} (hit : Fin d→Bool) (js : List (Fin d)) (j : Fin d)
    (eq : tag hit js=j.val+1) : hit j=true := by
  induction js with
  | nil => simp [tag] at eq
  | cons i is ih =>
    cases hi : hit i with
    | false => exact ih (by simpa [tag,hi] using eq)
    | true =>
      have same : i=j := Fin.ext (Nat.succ.inj (by simpa [tag,hi] using eq))
      simpa [same] using hi

private theorem tag_le {d : ℕ} (hit : Fin d→Bool) (js : List (Fin d)) : tag hit js≤d := by
  induction js with
  | nil => exact Nat.zero_le _
  | cons i is ih => cases hi : hit i <;> simp [tag,hi,ih,i.isLt]

/-- The stock column indexed by `j` belongs to exactly that signed altimeter. -/
def tested (p : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) (r : Word w) (j : Fin (2*k)) :=
  eligible p T k kind ((stock j |>.read mem r).val%table.size)

theorem tagExpr_eval (p : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) (r : Word w) (present : Table p T k kind table mem) (wide : 0<w)
    (js : List (Fin (2*k))) :
    (tagExpr table stock js).eval mem r = (tag (tested p T kind table stock mem r) js : Word w) := by
  have ne : (0:Word w)≠1 := by
    intro h
    have a := congrArg Fin.val h
    rw [Fin.val_zero,show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at a
    omega
  induction js with
  | nil => rfl
  | cons j js ih =>
    have word : table.read mem ((stock j).read mem r)=
        ((tested p T kind table stock mem r j).toNat:Word w) := present _
    simp only [tagExpr,Expr.eval,word,Comparison.test,beq_iff_eq,tag]
    cases hit : tested p T kind table stock mem r j <;> simp [ih,ne,Bool.toNat]

def markExpr (n : ℕ) (table : Bank) (stock : Fin (2*k)→Bank) (s : Fin (2*k)) : Expr :=
  .branch .lt .row (.lit n)
    (.branch .eq (tagExpr table stock (List.finRange (2*k))) (.lit (s.val+1)) (.lit 1) (.lit 0))
    (.lit 0)

def stratum (p : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) (s : Fin (2*k)) : Finset (Fin n) :=
  Finset.univ.filter fun i => tag (tested p T kind table stock mem (i.val:Word w)) (List.finRange (2*k))=s.val+1

theorem strata_disjoint (p : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) {s t : Fin (2*k)} (different : s≠t) :
    Disjoint (stratum (n:=n) p T kind table stock mem s) (stratum p T kind table stock mem t) := by
  apply Finset.disjoint_left.mpr
  intro r hs ht
  exact different (Fin.ext (Nat.succ.inj ((Finset.mem_filter.mp hs).2.symm.trans (Finset.mem_filter.mp ht).2)))

theorem read_mark (p : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) (s : Fin (2*k)) (wide : 0<w) (room : n<2^w) (dirs : 2*k<2^w)
    (present : Table p T k kind table mem) (i : Fin (n+1)) :
    (markExpr n table stock s).eval mem (i.val:Word w) =
      ((decide (i ∈ (stratum (n:=n) p T kind table stock mem s).map Fin.castSuccEmb)).toNat : Word w) := by
  induction i using Fin.lastCases with
  | last => simp [markExpr,Expr.eval,Comparison.test,Finset.mem_map,Fin.castSuccEmb_apply,Fin.castSucc_ne_last]
  | cast i =>
    have left := tagExpr_eval p T kind table stock mem (i.val:Word w) present wide (List.finRange (2*k))
    let v := tag (tested p T kind table stock mem (i.val:Word w)) (List.finRange (2*k))
    have small : v<2^w := (tag_le ..).trans_lt dirs
    have key : s.val+1<2^w := show s.val+1<2^w from Nat.lt_of_le_of_lt s.isLt dirs
    have eq : ((v:Word w)=((s.val+1:ℕ):Word w)) ↔ v=s.val+1 := by
      constructor
      · intro q
        have equal:=congrArg Fin.val q
        rw [Fin.val_cast_of_lt small,Fin.val_cast_of_lt key] at equal
        exact equal
      · intro q; rw [q]
    simp only [markExpr,Expr.eval,Comparison.test,Fin.val_castSucc,Fin.lt_def,Fin.val_cast_of_lt room,
      Fin.val_cast_of_lt (i.isLt.trans room),i.isLt,decide_true,ite_true,beq_iff_eq,left]
    change (if (v:Word w)=((s.val+1:ℕ):Word w) then _ else _) = _
    have membership : i.castSucc ∈ (stratum (n:=n) p T kind table stock mem s).map Fin.castSuccEmb ↔ v=s.val+1 := by
      simp [stratum,v,Finset.mem_map,Fin.castSuccEmb_apply]
    by_cases selected : v=s.val+1
    · have yes:=eq.mpr selected
      have memYes:=membership.mpr selected
      simp [yes,memYes]
    · have no:=fun e=>selected (eq.mp e)
      have memNo:=fun e=>selected (membership.mp e)
      rw [ite_eq_right no,decide_eq_false memNo]
      rfl

/-- One scan fills the binary mark column of a signed stratum, including its dummy row. -/
theorem emit (p : PhasePrice) (T : ℝ) (kind out : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) (s : Fin (2*k)) (wide : 0<w) (dirs : 2*k<2^w) (present : Table p T k kind table mem)
    (fit : (markExpr n table stock s).Fits w out) (space : out+(n+1)<2^w) :
    (scan w out (n+1) (markExpr n table stock s)).Exec mem (image out (n+1) (markExpr n table stock s) mem)
      (4+(n+1)*(2*(markExpr n table stock s).work+4)) ∧
    ∀i : Fin (n+1),image out (n+1) (markExpr n table stock s) mem (out+i.val) =
      ((decide (i∈(stratum (n:=n) p T kind table stock mem s).map Fin.castSuccEmb)).toNat : Word w) := by
  refine ⟨scan_exec out (n+1) (markExpr n table stock s) mem fit space,fun i => ?_⟩
  have interval : out ≤ out+i.val ∧ out+i.val < out+(n+1) := by have := i.isLt; omega
  simp only [image,fillSegment,ite_eq_left interval,Nat.cast_add,add_sub_cancel_left]
  exact read_mark p T kind table stock mem s wide (by omega) dirs present i

theorem tagExpr_work {d : ℕ} (table : Bank) (stock : Fin d→Bank) (js : List (Fin d)) :
    (tagExpr table stock js).work=1+15*js.length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [tagExpr,Expr.work,ih,List.length_cons,Nat.mul_succ]; omega

theorem markExpr_work (table : Bank) (stock : Fin (2*k)→Bank) (s : Fin (2*k)) :
    (markExpr n table stock s).work=10+15*(2*k) := by
  simp only [markExpr,Expr.work,tagExpr_work,List.length_finRange]
  omega

theorem exists_stratum_iff (p : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) (i : Fin n) :
    (∃ s, i∈stratum p T kind table stock mem s) ↔ ∃ s, tested p T kind table stock mem (i.val:Word w) s=true := by
  let hit := tested p T kind table stock mem (i.val:Word w)
  let v := tag hit (List.finRange (2*k))
  constructor
  · rintro ⟨s,hs⟩; exact ⟨s,hit_of_tag _ _ _ (Finset.mem_filter.mp hs).2⟩
  · rintro ⟨s,hs⟩
    have pos : 0<v := (tag_positive_iff ..).2 ⟨s,by simp,hs⟩
    have bounded : v≤2*k := tag_le ..
    refine ⟨⟨v-1,by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    change v = v-1+1
    omega

theorem markCheap (w n out : ℕ) (table : Bank) (stock : Fin (2*k)→Bank) (s : Fin (2*k)) :
    CheapCode (scan w out (n+1) (markExpr n table stock s)) :=
  scan_cheap w out (n+1) (markExpr n table stock s)

theorem qualifies_of_mem (p : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (mem : Memory w) (s : Fin (2*k)) (i : Fin n) (selected : i∈stratum p T kind table stock mem s)
    (fits : ((stock s).read mem (i.val:Word w)).val < table.size) :
    1/(4*(k:ℝ)) ≤ p.time*(AdaptiveProbe.rise p.M
      (p.quote kind ((stock s).read mem (i.val:Word w)).val)/T)^2 := by
  have hit := hit_of_tag _ _ s (Finset.mem_filter.mp selected).2
  simpa [tested,eligible,Nat.mod_eq_of_lt fits] using hit

end
end Hierarchy.ProtocolRAM.PurchaseMarks

end OAI
