import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomSyntax
import OAI.Computability.NearSquareRoot.InterchangeBatchIndices

/-! # Effective numeric row selections on occupied center blocks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.LoomRegisters NearSquareRoot.CommonRegisters NearSquareRoot.Space
  NearSquareRoot.GeneratorSyntax

def amount (x y : Tree) := x.count + y.count + 1

/-- A command on one pair of actual tree buffers, with separate clock and
space coefficients. Neither coefficient depends on any buffer length. -/
def Run (c : Cmd) (time space : ℕ) (x y : Tree) : Prop :=
  ∀ env r base, DeckCap base r → BoundedFits env c (pile 0 x r) (pile 0 y r)
    (time * amount x y) (base + space * amount x y) (space * amount x y)

private theorem at_most {X : Type} (s : Series X) (v : X → Tree) (x : X) :
    (v x).count ≤ (stripe s v).count := by
  rw [stripe_simple]
  exact count_le_forest v (s.complete x)

private theorem costSum_const {X : Type} (l : List X) (c : ℕ) :
    costSum (fun _ => c) l = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [costSum_cons, ih, List.length_cons, Nat.succ_mul]; omega

private theorem sum_amount {X : Type} (v w : X → Tree) (l : List X) :
    costSum (fun x => amount (v x) (w x)) l ≤ amount (Task.forest v l) (Task.forest w l) := by
  induction l with
  | nil => simp [amount,Tree.count]
  | cons a l ih =>
    simp only [costSum_cons, Task.forest_cons, Tree.count, amount] at *
    omega

theorem map_run {A : Type} (s : Series A) (x y : A → Tree) {t k : ℕ} {op : Cmd}
    (h : ∀ a, Run op t k (x a) (y a)) :
    Run (mapCommand op) (t+110) (k+50) (stripe s x) (stripe s y) := by
  let V := amount (stripe s x) (stripe s y)
  have hs (a : A) : amount (x a) (y a) ≤ V := by
    dsimp [V,amount]
    exact Nat.add_le_add_right (Nat.add_le_add (at_most s x a) (at_most s y a)) _
  intro env r base hr
  have cmd := map_bounded s.explore x y op (fun a => t * amount (x a) (y a)) (k*V)
    (fun a E d b hb => (h a E d b hb).mono le_rfl
      (Nat.add_le_add_left (Nat.mul_le_mul_left k (hs a)) _)
      (Nat.mul_le_mul_left k (hs a))) env r base hr
  simp only [← stripe_simple, costSum_mul] at cmd
  have ht := Nat.mul_le_mul_left t (sum_amount x y s.explore)
  simp only [← stripe_simple] at ht
  apply cmd.mono
  · change _ ≤ (t+110)*V
    dsimp only [V,amount] at *
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at ht ⊢
    omega
  · dsimp only [mapSpace,V,amount]
    rw [Nat.add_mul]
    omega
  · dsimp only [mapSpace,V,amount]
    rw [Nat.add_mul]
    omega

theorem series_run {A : Type} (s : Series A) (op : A → Cmd) (x : Tree) (y : A → Tree)
    {t k : ℕ} (h : ∀ a, Run (op a) t k x (y a)) :
    Run (seriesCommand op s.explore) ((s.count+1)*(t+100)) (k+70) x (stripe s y) := by
  let V := amount x (stripe s y)
  have hs (a : A) : amount x (y a) ≤ V :=
    Nat.add_le_add_right (Nat.add_le_add_left (at_most s y a) _) _
  intro env r base hr
  have cmd := series_bounded_at op x y (fun _ => t*V) (k*V) (k*V) env
    (fun a d b hb => (h a env d b hb).mono (Nat.mul_le_mul_left t (hs a))
      (Nat.add_le_add_left (Nat.mul_le_mul_left k (hs a)) _) (Nat.mul_le_mul_left k (hs a)))
    s.explore r base hr
  simp only [← stripe_simple, seriesClock, costSum_const] at cmd
  apply cmd.mono
  · change s.count*(45*x.count + t*V + 7) + 60*x.count + 10 ≤ (s.count+1)*(t+100)*V
    rw [Nat.mul_assoc, Nat.add_mul]
    rw [Nat.one_mul]
    have hl : 45*x.count + t*V + 7 ≤ (t+100)*V := by
      rw [Nat.add_mul]
      dsimp only [V,amount]
      omega
    have hr' : 60*x.count + 10 ≤ (t+100)*V := by
      rw [Nat.add_mul]
      dsimp only [V,amount]
      omega
    simpa only [Nat.add_assoc] using Nat.add_le_add (Nat.mul_le_mul_left s.count hl) hr'
  · dsimp only [V,amount]
    rw [Nat.add_mul]
    omega
  · dsimp only [V,amount]
    rw [Nat.add_mul]
    omega

private theorem fin_lanes (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp

theorem numeric_series {n : ℕ} (op : ℕ → Cmd) (x : Tree) (y : Fin n → Tree)
    {t k : ℕ} (h : ∀ a : Fin n, Run (op a.val) t k x (y a)) :
    Run (seriesCommand op (List.range n)) ((n+1)*(t+100)) (k+70) x (stripe (Series.natural n) y) := by
  rw [← fin_lanes n, InterchangeROM.series_map]
  have c := series_run (Series.natural n) (fun a : Fin n => op a.val) x y h
  simpa only [Series.count_natural, show (Series.natural n).explore = List.finRange n from rfl,
    Function.comp_def] using c

theorem numeric_cell {n : ℕ} (a : Fin n) (v : Fin n → Tree) :
    Run (cellCommand a.val) 90 91 (stripe (Series.natural n) v) (v a) := by
  intro env r base hr
  have h := finite_cell_bounded (Series.natural n) v a env r base hr
  change BoundedFits _ (cellCommand ((List.finRange n).idxOf a)) _ _ _ _ _ at h
  rw [List.idxOf_finRange] at h
  apply h.mono <;> dsimp [amount] <;> omega

def padOne (b W u : ℕ) : Cmd :=
  seriesCommand (fun j => cellCommand ((j*W+u)%b)) (List.range (BatchRows.groups b W))

def pad (b W : ℕ) : Cmd := seriesCommand (fun u => mapCommand (padOne b W u)) (List.range W)

theorem effective_pad : Effective ltr (fun x : ℕ × ℕ => pad x.1 x.2) := by
  apply InterchangeROM.effective_series
  · apply effective_map
    apply InterchangeROM.effective_series
    · apply InterchangeROM.effective_cell
      exact (Primrec.nat_mod.comp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp .snd ((Primrec.snd.comp .fst).comp .fst)) (Primrec.snd.comp .fst))
        ((Primrec.fst.comp .fst).comp .fst)).to_comp
    · have hg : Primrec (fun x : (ℕ × ℕ) × ℕ => BatchRows.groups x.1.1 x.1.2) := by
        simpa only [BatchRows.groups,Nat.ceilDiv_eq_add_pred_div] using
          Primrec.nat_div.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp
            (Primrec.fst.comp (.fst (α := ℕ × ℕ) (β := ℕ))) (Primrec.snd.comp .fst))
            (.const 1)) (Primrec.snd.comp .fst)
      exact (Primrec.list_range.comp hg).to_comp
  · exact (Primrec.list_range.comp Primrec.snd).to_comp

theorem pad_within (b W : ℕ) : Within 3 (pad b W) :=
  series_within (le_refl 3) _ _ fun _ => map_within (le_refl 3)
    (series_within (le_refl 3) _ _ fun _ => cell_within _)

abbrev packed {P : Type} {b W : ℕ} (p : Series P) (hb : 0 < b) (v : P → Fin b → Tree) (u : Fin W) :=
  stripe p (fun x => stripe (Series.natural (BatchRows.groups b W))
    (fun h => v x (BatchRows.select hb u h)))

theorem pad_run {P : Type} (p : Series P) {b W : ℕ} (hb : 0 < b) (v : P → Fin b → Tree) :
    Run (pad b W) ((W+1)*((BatchRows.groups b W+1)*190+210)) 281
      (stripe p (fun x => stripe (Series.natural b) (v x)))
      (stripe (Series.natural W) (packed p hb v)) := by
  apply numeric_series
  intro u
  apply map_run
  intro x
  apply numeric_series
  intro j
  exact numeric_cell (BatchRows.select hb u j) (v x)

end InterchangeROMBank

end NearSquareRoot
end Computability
end OAI
