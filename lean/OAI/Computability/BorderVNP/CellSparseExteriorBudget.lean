import OAI.Computability.BorderVNP.CellSparseExteriorDriver

/-! # Valid sparse exterior bursts obey the original native square-root and tape budgets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open Filter TeamScales CellMacro CellMacro.Generator CellSparse
open private compact_digits small_width from OAI.Computability.BorderVNP.RoutingISATypedPrivateClock

/-- Word count and true transition cutoff for each physical compressed external burst. -/
def PrivateCallsAt (A T B j H R k n r : ℕ) : Prop :=
  ∀ M E w p U : ℕ, M ≤ width n (1/5) → E ≤ width n (1/4) → 0<w → w≤n →
    ∀ (D : Directory) (f : Field), f.width+f.tail.length ≤ E → Ordered f.width 0 f.spans →
    (∀ z ∈ f.spans, 0<z.bits.length) →
    D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
    D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
    Packet.storedMass D ≤ A*(M+1)^2 → Packet.RawFields D p U → U.size+1 ≤ B*(logWidth r n+1)^j →
    (∀ row ∈ D.records, (Packet.record row).length ≤ H) → (∀ fs ∈ D.boxes, ∀ z ∈ fs, z.TableBound T) →
    (∀ bs ∈ D.reportedCounts, bs.length ≤ R*(logWidth r n+1)^k) →
    (CompactFrame.pack w (Packet.input D p f.bytes)).length ≤ width n (1/2) ∧ clock w D p f ≤ n^25

private theorem spans_size (ss : List Span) (width pos : ℕ) (ordered : Ordered width pos ss) :
    pos+(ss.map (fun s => s.bits.length)).sum ≤ width := by
  induction ss generalizing pos with
  | nil => simpa [Ordered] using ordered
  | cons s ss ih =>
    have h := ih s.stop ordered.2
    have start := ordered.1
    simp only [List.map_cons,List.sum_cons,Span.stop] at h ⊢
    omega

private theorem span_count (ss : List Span) (positive : ∀ s ∈ ss, 0<s.bits.length) :
    ss.length ≤ (ss.map fun s => s.bits.length).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have a := positive s List.mem_cons_self
    have b := ih (fun x hx => positive _ (List.mem_cons_of_mem _ hx))
    simp; omega

/-- Per-cell compact payload, using the binary width of actual gaps and avoiding
an extra factor of the external RAM word width on the square-root probe bound. -/
theorem Field.bytes_le (e : Field) {E L : ℕ} (bound : e.width+e.tail.length ≤ E) (digits : e.width.size ≤ L)
    (ordered : Ordered e.width 0 e.spans) (positive : ∀ s ∈ e.spans, 0<s.bits.length) :
    e.bytes.length ≤ 8*(E+1)*(L+1) := by
  have length := encode_length e.tail e.spans ordered (Nat.lt_size_self e.width)
  have total := spans_size e.spans e.width 0 ordered
  have count := (span_count e.spans positive).trans (by simpa only [Nat.zero_add] using total)
  have product := Nat.mul_le_mul (show 2*e.width.size+4 ≤ 4*(L+1) by omega)
    (show e.spans.length+1 ≤ E+1 by omega)
  have paid : E ≤ (E+1)*(L+1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (by omega))
  change (encode e.width e.tail 0 e.spans).length ≤ _
  rw [show 4*(L+1)*(E+1)=4*((E+1)*(L+1)) by ring] at product
  rw [Nat.mul_assoc]
  omega

/-- With the genuine typed-directory compiler and RLE restorer installed,
the same uniform `n^(1/2)` word and `n^25` transition bounds follow from the
local expanded dimensions. This covers arbitrary gap positions and report bits. -/
theorem eventually_private_cell (A T B j H R k : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w p U : ℕ, 1 ≤ r → (r:ℝ) ≤ 2^((n:ℝ)^ω) →
      M ≤ width n (1/5) → E ≤ width n (1/4) → 0<w → w≤n →
      ∀ (D : Directory) (f : Field), f.width+f.tail.length ≤ E → Ordered f.width 0 f.spans →
      (∀ s ∈ f.spans, 0<s.bits.length) →
      D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
      D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
      Packet.storedMass D ≤ A*(M+1)^2 → Packet.RawFields D p U → U.size+1 ≤ B*(logWidth r n+1)^j →
      (∀ row ∈ D.records, (Packet.record row).length ≤ H) → (∀ fs ∈ D.boxes, ∀ z ∈ fs, z.TableBound T) →
      (∀ bs ∈ D.reportedCounts, bs.length ≤ R*(logWidth r n+1)^k) →
      (CompactFrame.pack w (Packet.input D p f.bytes)).length ≤ width n (1/2) ∧ clock w D p f ≤ n^25 := by
  obtain ⟨K,g,_,_,compile⟩ := CellPrivate.translateClock_physical A T B j 10 1 H R k
  let e := max 1 (max j g)
  let W := B+2
  let P := (8*A+4)*(4*W+4)+9
  let C := K+42*P+140
  obtain ⟨ω,hω,physical⟩ := eventually_compiled_load_log A C e
  refine ⟨ω,hω,?_⟩
  filter_upwards [physical,eventually_ge_atTop 1] with n budget hn
  intro r M E w p U hr batch hM hE hw hwn D f he order positive static compact rec report mass raw rawDigits fmt tabs widths
  let X := M+E+1
  let Y := (M+1)^2+E+1
  let L := logWidth r n+1
  have x1 : 1≤X := by dsimp [X]; omega
  have l1 : 1≤L := by dsimp [L]; omega
  have y1 : 1≤Y := by dsimp [Y]; omega
  have pow1 : 1 ≤ L^e := Nat.one_le_pow _ _ l1
  have powL : L ≤ L^e := by simpa using Nat.pow_le_pow_right l1 (le_max_left 1 (max j g))
  have hJ := Nat.pow_le_pow_right l1 ((le_max_left j g).trans (le_max_right 1 _))
  have hG : L^g ≤ L^e := Nat.pow_le_pow_right l1 ((le_max_right j g).trans (le_max_right 1 _))
  have mn := hM.trans (small_width hn _ (by norm_num))
  have en := hE.trans (small_width hn _ (by norm_num))
  have cubic := compact_digits hr mn en
  have work := compile D p M E U (4*X^3) L l1 static mass raw rawDigits compact (by simpa only [pow_one,X,L] using cubic) fmt tabs widths
  have tr := work.trans (Nat.mul_le_mul (Nat.mul_le_mul_left K (Nat.pow_le_pow_right x1 (show 63≤96 by decide))) hG)
  have scalar (v : ℕ) (hv : v ∈ Packet.words D p) : v.size ≤ W*L^e := by
    have lim := Packet.words_bounded _ _ raw v hv
    rcases max_choice 3 U with h|h
    · rw [h] at lim
      have b : (3:ℕ).size ≤ W := by change 2≤B+2; omega
      exact (Nat.size_le_size lim).trans (b.trans (Nat.le_mul_of_pos_right _ pow1))
    · rw [h] at lim
      exact (Nat.size_le_size lim).trans ((Nat.le_succ _).trans (rawDigits.trans (Nat.mul_le_mul (Nat.le_add_right ..) hJ)))
  have pay := Packet.input_length_from_static D p f.bytes static mass scalar
  have digits : f.width.size ≤ logWidth r n := (Nat.size_le_size ((Nat.le_add_right ..).trans (he.trans en))).trans (size_le_logWidth n r hr)
  have ext := f.bytes_le he digits order positive
  change f.bytes.length ≤ 8*(E+1)*L at ext
  have large : E+1 ≤ Y := by dsimp [Y]; omega
  have pp : (M+1)^2 ≤ Y := by dsimp [Y]; omega
  have p1 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 large) powL
  have pf : 4*(W*L^e)+4 ≤ (4*W+4)*L^e := by rw [Nat.add_mul (4*W) 4, Nat.mul_assoc 4 W]; omega
  have mp := Nat.mul_le_mul (Nat.mul_le_mul_left (8*A+4) pp) pf
  have yz : 1 ≤ Y*L^e := y1.trans (Nat.le_mul_of_pos_right _ pow1)
  have hpay : (Packet.input D p f.bytes).length ≤ P*(Y*L^e) := by
    change _ ≤ (8*A+4)*(M+1)^2*(4*(W*L^e)+4)+1+f.bytes.length at pay
    rw [show (8*A+4)*Y*((4*W+4)*L^e)=(8*A+4)*(4*W+4)*(Y*L^e) by ring] at mp
    have exBound := ext.trans p1
    rw [Nat.mul_assoc 8] at exBound
    dsimp only [P]; rw [Nat.add_mul]; omega
  have sc := Private.restore_cost_le f.width 0 f.tail f.spans order positive
  change f.restoreCost ≤ _ at sc
  have xp := Nat.pow_le_pow_right x1 (show 3≤96 by decide)
  have root : f.width+f.tail.length+1 ≤ X := by dsimp [X]; omega
  have re := sc.trans (Nat.mul_le_mul_left 100 ((Nat.pow_le_pow_left root 3).trans xp))
  have scale := Nat.le_mul_of_pos_right (X^96) pow1
  have yx := (Nat.pow_le_pow_left (show M+1≤X by dsimp [X]; omega) 2).trans (Nat.pow_le_pow_right x1 (by decide : 2≤96))
  have lin : X ≤ X^96 := by simpa using Nat.pow_le_pow_right x1 (by decide : 1≤96)
  have ex : E ≤ X := by dsimp [X]; omega
  have scale1 := x1.trans (lin.trans scale)
  have yg : Y ≤ 3*X^96 := by dsimp [Y]; omega
  have metaBound : (Packet.bits D p).length ≤ (Packet.input D p f.bytes).length := by simp [Packet.input,RationalHitting.StackLanguage.codeWord_length]; omega
  have mt := metaBound.trans (hpay.trans (Nat.mul_le_mul_left P (Nat.mul_le_mul_right (L^e) yg)))
  have length := expand_length f.tail f.spans order
  have dense : f.values.length ≤ E := by change (expand _ _ _ _).length ≤ _; omega
  have paid : f.restoreCost+CellPrivate.translateClock D p+14*(Packet.bits D p).length+12*f.values.length+22 ≤ C*X^96*L^e := by
    have regroup (p x l : ℕ) : p*(3*x*l)=3*(p*(x*l)) := by ring
    rw [regroup] at mt
    rw [Nat.mul_assoc K] at tr
    have combine (k p x l : ℕ) : (k+42*p+140)*x*l=k*(x*l)+42*(p*(x*l))+140*(x*l) := by ring
    rw [show C=K+42*P+140 from rfl,combine]
    omega
  obtain ⟨q,h⟩ := budget r M E w p hr batch hM hE hw hwn D static compact rec report _ _
    (by simpa only [Nat.mul_assoc,L,Y] using hpay.trans (Nat.mul_le_mul_right _ (show P≤C by dsimp [C]; omega))) paid
  refine ⟨q,?_⟩
  dsimp only [clock]
  have eq := CompactPacket.packet_work D p (f.restoreCost+CellPrivate.translateClock D p) f.values
  dsimp only at eq
  omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
