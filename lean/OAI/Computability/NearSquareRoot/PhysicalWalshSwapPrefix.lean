import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouteIO
import OAI.Computability.NearSquareRoot.PhysicalWalshPadding

/-! # Extending a Walsh lane to a dyadic prefix

Only the trailing prefix groups are padded. A binary computation on the
original compact node descriptor determines how many zero records to append
and the exact truncation length. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SwapPrefix

open IntegerMultiplication Code Strip Carry PhysicalWalsh Space

def length (A W : ℕ) (s : Shape) := groups W s * inner A s
def paddedSize (A W : ℕ) (s : Shape) := 2^(Nat.clog 2 (groups W s)) * inner A s

def extend (A W : ℕ) (s : Shape) (x : Data s) : Data s := fun n =>
  if n < length A W s then x n else 0

/-- A source-address map preserving the prefix boundary commutes with
extending a stream by zero records. -/
theorem extend_comp (A W : ℕ) (s : Shape) (x : Data s) (f : ℕ → ℕ)
    (inside : ∀ n, f n < length A W s ↔ n < length A W s) :
    extend A W s x ∘ f = extend A W s (x ∘ f) := by
  funext n
  simp only [Function.comp_apply,extend,inside]

def stream {s : Shape} (N : ℕ) (x : Data s) := (List.range N).map (Dusk.mark ∘ x)

theorem length_pos (A W : ℕ) (s : Shape) : 0 < length A W s :=
  Nat.mul_pos (Nat.zero_lt_one.trans_le (le_max_left ..)) (Nat.mul_pos (Nat.two_pow_pos _) s.suff_pos)

theorem length_le (A W : ℕ) (s : Shape) : length A W s ≤ paddedSize A W s :=
  Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)

theorem paddedSize_le (A W : ℕ) (s : Shape) : paddedSize A W s ≤ 2 * length A W s := by
  have pos : 0 < groups W s := Nat.zero_lt_one.trans_le (le_max_left ..)
  have bound : 2^(Nat.clog 2 (groups W s)) ≤ 2 * groups W s := by
    by_cases one : groups W s = 1
    · simp [one]
    · have gt : 1 < groups W s := by omega
      have hp := Nat.clog_pos (by decide : 1 < 2) gt
      have prev := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) gt
      rw [show Nat.clog 2 (groups W s) = Nat.clog 2 (groups W s) - 1 + 1 by omega, pow_succ']
      exact Nat.mul_le_mul_left _ prev.le
  simpa only [length,paddedSize,Nat.mul_assoc] using Nat.mul_le_mul_right (inner A s) bound

theorem length_le_count (A W : ℕ) (s : Shape) : length A W s ≤ count A s :=
  Nat.mul_le_mul_right _ (max_le s.pref_pos (Nat.div_le_self _ _))

def cuts (A W : ℕ) (s : Shape) :=
  (tally (paddedSize A W s - length A W s),tally (length A W s))

private theorem cuts_mint (A W : ℕ) : Mint (Header.regime A) (cuts A W) := by
  have desc : (Header.regime A).Has (Header.wire A) := (Header.regime A).self
  have active : Staff.Realizes (Header.regime A) (fun s => grow A s.level) :=
    desc.ez (Easy.fst.compose (Easy.snd.compose Easy.fst))
  have rows := ((Figure.natural 2).repeated active).multiplied (Header.suff A)
  have gr := Header.groupCount A W
  have raw := gr.multiplied rows
  have pad := ((Figure.natural 2).repeated gr.short_log).multiplied rows
  exact (Mint.tally (pad.subtracted raw)).pair (Mint.tally raw)

theorem capacity (A W : ℕ) (s : Shape) (d : ℕ) :
    (length A W s+1)*(s.w+1) ≤ allowance A d s := by
  calc
    _ ≤ (count A s+1)*(grow A s.level+s.w+1) := by
      exact Nat.mul_le_mul (by have := length_le_count A W s; omega) (by omega)
    _ ≤ _ := Nat.le_add_right ..

private theorem cuts_cost (A W : ℕ) : ∃ d,
    BoundedTask (allowance A d) (allowance A d) (send ∘ Header.wire A) (send ∘ cuts A W) := by
  obtain ⟨d,C,h⟩ := (cuts_mint A W).bounded
  refine ⟨d,?_⟩
  apply h.bound (C+8) (C+8) <;> intro s
  all_goals
    have hc := capacity A W s d
    have hN : length A W s ≤ allowance A d s :=
      (Nat.le_add_right _ 1).trans ((Nat.le_mul_of_pos_right _ (by omega)).trans hc)
    have hp := paddedSize_le A W s
    have hd : C*(Header.scale A s+1)^d ≤ C*allowance A d s := Nat.mul_le_mul_left _ (Nat.le_add_left ..)
    change C*(Header.scale A s+1)^d + size (cuts A W s) + 1 ≤ (C+8) * (allowance A d s+1)
    simp only [cuts,size_prod,size_tally,tally_length,Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega

theorem pad_eq (A W : ℕ) (s : Shape) (x : Data s) :
    Padding.padded (paddedSize A W s-length A W s) ((List.range (length A W s)).map x) =
      stream (paddedSize A W s) (extend A W s x) := by
  have enough := length_le A W s
  unfold Padding.padded stream
  apply List.ext_getElem
  · simp only [List.length_append,List.length_map,List.length_range,List.length_replicate]
    omega
  · intro i hi hj
    by_cases left : i<length A W s
    · have lt : i < (((List.range (length A W s)).map x).map Dusk.mark).length := by simpa using left
      simp only [List.getElem_append_left lt,List.getElem_map,List.getElem_range,Function.comp_apply,extend,ite_eq_left left]
    · have le : (((List.range (length A W s)).map x).map Dusk.mark).length ≤ i := by simpa using Nat.le_of_not_gt left
      simp only [List.getElem_append_right le,List.getElem_replicate,List.getElem_map,List.getElem_range,Function.comp_apply,extend,ite_eq_right left]

private theorem stream_size {s : Shape} (N : ℕ) (x : Data s) :
    size (stream N x) = N*(4*(s.w+1)+4)+1 := by
  unfold stream
  rw [← List.map_map,Padding.marks_size,List.length_map,List.length_range]

theorem stream_cost (A W d : ℕ) (s : Shape) (N : ℕ) (x : Data s) (hN : N ≤ paddedSize A W s) :
    size (stream N x) ≤ 16*allowance A d s + 1 := by
  have h := hN.trans (paddedSize_le A W s)
  have hm := Nat.mul_le_mul_right (s.w+1) h
  have hc := capacity A W s d
  rw [stream_size]
  ring_nf at h hm hc ⊢
  omega

private theorem mint_for_stream {I : Type} (A W d : ℕ)
    (h : BoundedTask (allowance A d) (allowance A d) (send ∘ Header.wire A) (send ∘ cuts A W))
    (s : I → Shape) (N : I → ℕ) (x : (i : I) → Data (s i))
    (fit : ∀ i, N i ≤ paddedSize A W (s i)) :
    let b i := allowance A d (s i)
    BoundedTask b b (fun i => send (Header.wire A (s i), stream (N i) (x i)))
      (fun i => send (cuts A W (s i),stream (N i) (x i))) := by
  intro b
  apply ((h.on s).left (fun i => send (stream (N i) (x i)))).bound 1 20
  · intro i; simp [b]
  · intro i
    have := stream_cost A W d (s i) (N i) (x i) (fit i)
    change allowance A d (s i) + size (stream (N i) (x i)) + 1 ≤ 20*(allowance A d (s i)+1)
    omega

/-- Pad the real stream to a power-of-two number of prefix groups. The
destination words in every added record are both zero. -/
theorem pad {I : Type} (A W : ℕ) (s : I → Shape) (x : (i : I) → Data (s i)) : ∃ d,
    let b i := allowance A d (s i)
    BoundedTask b b (fun i => send (Header.wire A (s i),laneFlat A W (s i) (x i)))
      (fun i => send (stream (paddedSize A W (s i)) (extend A W (s i) (x i)))) := by
  obtain ⟨d,mint⟩ := cuts_cost A W
  refine ⟨d,?_⟩
  let N i := length A W (s i)
  let M i := paddedSize A W (s i)
  let b i := allowance A d (s i)
  let xs i := (List.range (N i)).map (x i)
  have head := mint_for_stream A W d mint s N x (fun i => length_le A W (s i))
  have nonempty (i : I) : xs i ≠ [] := by
    intro z
    have eq := congrArg List.length z
    simp only [xs,List.length_map,List.length_range,List.length_nil] at eq
    exact (length_pos A W (s i)).ne' eq
  have append := Padding.appendZeros (Shape.w ∘ s) (fun i => M i-N i) xs nonempty
  have body : BoundedTask b b (fun i => send (cuts A W (s i),stream (N i) (x i)))
      (fun i => send (tally (N i),stream (M i) (extend A W (s i) (x i)))) := by
    simp only [xs,List.length_map,List.length_range,List.map_map] at append
    have he (i : I) : Padding.padded (M i-N i) ((List.range (N i)).map (x i)) =
        stream (M i) (extend A W (s i) (x i)) := pad_eq A W (s i) (x i)
    simp only [he] at append
    apply append.bound 3 3 <;> intro i
    all_goals
      have hc := capacity A W (s i) d
      have hNM : N i ≤ M i := length_le A W (s i)
      have hM : M i ≤ 2 * N i := paddedSize_le A W (s i)
      have hm := Nat.mul_le_mul_right ((s i).w+1) hM
      change (N i + (M i-N i)+1)*((s i).w+1)+1 ≤ 3*(b i+1)
      change (N i+1)*((s i).w+1) ≤ b i at hc
      rw [show N i+(M i-N i) = M i by omega]
      ring_nf at hc hm ⊢
      omega
  let out i := stream (M i) (extend A W (s i) (x i))
  have final := PhysicalWalshGrid.easyWithin b (Easy.snd (X:=Tally) (Y:=List Dusk.Pair))
    (fun i => (tally (N i),out i)) 22 (fun i => by
      have ho := stream_cost A W d (s i) (M i) (extend A W (s i) (x i)) le_rfl
      have hc := capacity A W (s i) d
      have small : N i ≤ b i := (Nat.le_add_right _ 1).trans ((Nat.le_mul_of_pos_right _ (by omega)).trans hc)
      change size (tally (N i),out i) ≤ 22*(b i+1)
      change size (out i) ≤ 16*b i+1 at ho
      simp only [size_prod,size_tally,tally_length]; omega)
  exact ((head.compose body).compose final).bound 3 1 (fun _ => by simp [b]; omega) (fun _ => by simp [b])

/-- Truncate any transformed padded row at the original prefix boundary. -/
theorem crop {I : Type} (A W : ℕ) (s : I → Shape) (y : (i : I) → Data (s i)) : ∃ d,
    let b i := allowance A d (s i)
    BoundedTask b b (fun i => send (Header.wire A (s i),stream (paddedSize A W (s i)) (y i)))
      (fun i => send (laneFlat A W (s i) (y i))) := by
  obtain ⟨d,mint⟩ := cuts_cost A W
  refine ⟨d,?_⟩
  let N i := length A W (s i)
  let M i := paddedSize A W (s i)
  let b i := allowance A d (s i)
  have head := mint_for_stream A W d mint s M y (fun _ => le_rfl)
  let cut (p : (Tally × Tally) × List Dusk.Pair) := p.2.take p.1.2.length
  have run : Easy cut := (easy_cut ((Easy.fst.compose Easy.snd).pair Easy.snd)).compose Easy.fst
  have taken := PhysicalWalshGrid.easyWithin b run (fun i => (cuts A W (s i),stream (M i) (y i))) 28 (fun i => by
    have ho := stream_cost A W d (s i) (M i) (y i) le_rfl
    have hc := capacity A W (s i) d
    have small : N i ≤ b i := (Nat.le_add_right _ 1).trans ((Nat.le_mul_of_pos_right _ (by omega)).trans hc)
    have hm : M i ≤ 2*N i := paddedSize_le A W (s i)
    change size (stream (M i) (y i)) ≤ 16*b i+1 at ho
    change size ((tally (M i - N i),tally (N i)), stream (M i) (y i)) ≤ 28*(b i+1)
    simp only [size_prod,size_tally,tally_length]; omega)
  have eq (i : I) : cut (cuts A W (s i),stream (M i) (y i)) = laneFlat A W (s i) (y i) := by
    change ((List.range (M i)).map (Dusk.mark ∘ y i)).take (tally (N i)).length = _
    rw [tally_length,← List.map_take,List.take_range,Nat.min_eq_left (length_le A W (s i))]
    rfl
  simp only [eq] at taken
  exact (head.compose taken).bound 2 1 (fun _ => by simp [b]; omega) (fun _ => by simp [b])

/-- Keep a second copy of the compact descriptor for the wide interchange
that consumes the extended bundle. -/
theorem padWithHeader {I : Type} (A W : ℕ) (s : I → Shape) (x : (i : I) → Data (s i)) : ∃ d,
    let b i := allowance A d (s i)
    BoundedTask b b (fun i => send (Header.wire A (s i),laneFlat A W (s i) (x i)))
      (fun i => send (Header.wire A (s i),stream (paddedSize A W (s i)) (extend A W (s i) (x i)))) := by
  obtain ⟨d,padder⟩ := pad A W s x
  let b i := allowance A (d+1) (s i)
  let hd i := Header.wire A (s i)
  let p i := (hd i,laneFlat A W (s i) (x i))
  let out i := stream (paddedSize A W (s i)) (extend A W (s i) (x i))
  have small (i : I) : size (hd i) ≤ b i := by
    have pow := Nat.pow_le_pow_right (n:=Header.scale A (s i)+1) (by omega) (show 1 ≤ d+1 by omega)
    change Header.scale A (s i) ≤ _; rw [pow_one] at pow
    exact (Nat.le_add_right _ 1).trans (pow.trans (Nat.le_add_left ..))
  have first := PhysicalWalshGrid.easyWithin b (Easy.identity.pair Easy.fst) p 22 (fun i => by
    have h := stream_cost A W (d+1) (s i) _ (x i) (length_le A W (s i))
    change size (laneFlat A W (s i) (x i)) ≤ 16*b i+1 at h
    have h' := small i
    change size (hd i)+size (laneFlat A W (s i) (x i))+1 ≤ 22*(b i+1)
    omega)
  have kept := padder.left (send ∘ hd)
  have keep := kept.bound (time':=b) (space':=b) 1 2 (fun i => by
      simp only [Nat.one_mul]; exact Nat.succ_le_succ (allowance_mono (Nat.le_succ d) (s i))) (fun i => by
      have h := small i
      have h' : allowance A d (s i) ≤ allowance A (d+1) (s i) := allowance_mono (Nat.le_succ d) (s i)
      change allowance A d (s i)+size (hd i)+1 ≤ 2*(allowance A (d+1) (s i)+1)
      change size (hd i) ≤ allowance A (d+1) (s i) at h; omega)
  have flip := PhysicalWalshGrid.easyWithin b (Easy.exchange (X:=List Dusk.Pair) (Y:=Header.Wire))
    (fun i => (out i,hd i)) 22 (fun i => by
      have ho := stream_cost A W (d+1) (s i) _ (extend A W (s i) (x i)) le_rfl
      change size (out i) ≤ 16*b i+1 at ho
      change size (out i)+size (hd i)+1 ≤ 22*(b i+1)
      have := small i; omega)
  exact ⟨d+1, ((first.compose keep).compose flip).bound 3 1 (fun _ => by simp [b]; omega)
    (fun _ => by simp [b])⟩

end PhysicalWalshNode.SwapPrefix

end NearSquareRoot
end Computability
end OAI
