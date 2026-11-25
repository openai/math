import OAI.Hierarchy.DescentGoodPortCoherence
import OAI.Hierarchy.DescentPairedKeyComparison

namespace OAI
/-! # Computing actual rotor peer-column prefixes from host-shared comparisons and short interval names -/
namespace Hierarchy.DescentShortReservationPeer
open DescentPairedKeyComparison DescentChosenRouter DescentBaseProfile DescentCanonicalPorts
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical BigOperators
noncomputable section

/-- Short metadata cached once for two old host names. The large absolute names are read only
on the old host roster. Their ordering and small-name cases suffice in every block. -/
structure Compare where
  first : ℕ
  second : ℕ
  less : Bool
  same : Bool

def compare (bound a b : ℕ) : Compare := ⟨min a bound,min b bound,decide (a<b),decide (a=b)⟩

def before (bound : ℕ) (c : Compare) (i j : ℕ) : Prop :=
  if c.first<bound ∧ c.second<bound then ordered c.first i c.second j
  else c.less=true ∨ c.same=true ∧ i<j

theorem before_read (bound a b i j : ℕ) (lo : i<bound) (hi : j<bound) :
    before bound (compare bound a b) i j ↔ Nat.pair a i<Nat.pair b j := by
  rw [pair_iff]
  unfold before compare
  by_cases x : a<bound <;> by_cases y : b<bound
  · simp [min_eq_left x.le,min_eq_left y.le,x,y]
  all_goals simp [min_def,ordered,tailLT,max_def]; split_ifs <;> simp_all <;> omega

/-- These four expressions are constant work on the original host-pair directory. -/
def «fields» (bound : ℕ) (a b : Expr) : Fin 4→Expr :=
  ![.branch .lt a (.lit bound) a (.lit bound),.branch .lt b (.lit bound) b (.lit bound),
    .branch .lt a b (.lit 1) (.lit 0),.branch .eq a b (.lit 1) (.lit 0)]

theorem fields_read {w : ℕ} (bound : ℕ) (a b : Expr) (m : Memory w) (r : Computability.VPVNP.BurstRAM.Word w)
    (small : bound<2^w) (one : 1<2^w) (j : Fin 4) :
    ((«fields» bound a b j).eval m r).val=
      let c:=compare bound (a.eval m r).val (b.eval m r).val
      ![c.first,c.second,c.less.toNat,c.same.toNat] j := by
  have clip (e : Expr) :
      ((Expr.branch .lt e (.lit bound) e (.lit bound)).eval m r).val = min (e.eval m r).val bound := by
    by_cases below : (e.eval m r).val<bound
    · simp [Expr.eval,DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt small,
        below,min_eq_left below.le]
    · simp [Expr.eval,DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt small,
        below,min_eq_right (le_of_not_gt below)]
  fin_cases j
  · exact clip a
  · exact clip b
  · change ((Expr.branch .lt a b (.lit 1) (.lit 0)).eval m r).val =
        (decide ((a.eval m r).val<(b.eval m r).val)).toNat
    by_cases h : (a.eval m r).val<(b.eval m r).val <;>
      simp [Expr.eval,DescriptorExpr.Comparison.test,Fin.lt_def,h,Nat.mod_eq_of_lt one]
  · change ((Expr.branch .eq a b (.lit 1) (.lit 0)).eval m r).val =
        (decide ((a.eval m r).val=(b.eval m r).val)).toNat
    by_cases h : (a.eval m r).val=(b.eval m r).val <;>
      simp [Expr.eval,DescriptorExpr.Comparison.test,Fin.ext_iff,h,Nat.mod_eq_of_lt one]

theorem touching_lt {d e x j : ℕ} (xx : x<2^d) (member : j∈touching d e x) : j<2^e := by
  by_cases deep : d≤e
  · rw [touching,ite_eq_left deep,Finset.mem_image] at member
    obtain ⟨t,ht,rfl⟩:=member
    have tlt:=Finset.mem_range.mp ht
    have upto:=Nat.mul_le_mul_right (2^(e-d)) xx
    rw [Nat.succ_mul,←pow_add,Nat.add_sub_of_le deep] at upto
    omega
  · simp [touching,deep] at member
    subst j
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    have ed:e≤d:=by omega
    simpa [←pow_add,Nat.add_sub_of_le ed] using xx

def amount (bound d e x y scale : ℕ) (c : Compare) :=
  ∑t : ↥(touching d e x),if before bound c t.val y then scale else 0

variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k n : ℕ}
variable (P : Placement V I H A k (2^n)) (m : ℕ) (roster : P.ColumnRoster m)
variable (s : Bool) (t : Reserve P.span)
local notation "x" => short (m:=m) P.b (Subtype.val (P.ends s (Sigma.fst t)))
local notation "y" => short (m:=m) P.b (Subtype.val (P.ends (!s) (Sigma.fst t)))
local notation "B" => (2^(k-m):ℕ)
local notation "d" w:arg => relative (m:=m) P.b w

/-- No absolute host name occurs under the short sum except in the shared comparison metadata. -/
theorem reserved_column :
    P.reservedColumn m roster.host roster.near roster.size s t=
      (∑w : roster.near x.1, amount B (d x.1) (d w.val) x.2 y.2 (roster.size x.1 w.val)
        (compare B (roster.host w.val) (roster.host y.1)))+t.2.val := by
  unfold Placement.reservedColumn
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro w _
  unfold amount
  apply Finset.sum_congr rfl
  intro z _
  have dx : x.2<2^(d x.1):=Nat.mod_lt _ (Nat.two_pow_pos _)
  have dy : y.2<2^(d y.1):=Nat.mod_lt _ (Nat.two_pow_pos _)
  have dep (v : V) : d v≤k-m := Nat.sub_le_sub_right (P.depth v) m
  have left := (touching_lt dx z.property).trans_le (Nat.pow_le_pow_right (by decide : 0<2) (dep w.val))
  have right := dy.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (dep y.1))
  change (if Nat.pair (roster.host w.val) z.val < Nat.pair (roster.host y.1) y.2
      then roster.size x.1 w.val else 0) = _
  exact if_congr (before_read B (roster.host w.val) (roster.host y.1) z.val y.2 left right).symm rfl rfl

end
end Hierarchy.DescentShortReservationPeer

end OAI
