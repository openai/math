import OAI.Computability.NearSquareRoot.InterchangeROMBankReindex
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomBlend

/-! # Extracting the genuine digits from a padded bank

The supplied blank row scaffold transposes the bank to prefix-major order.
At each prefix the quotient and remainder select one cell for each genuine
digit, omitting all padding in the final group. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.LoomRegisters NearSquareRoot.CommonRegisters NearSquareRoot.Space NearSquareRoot.GeneratorSyntax

/-- Both selections address literal natural-order stripes. -/
def unpadCell (W d : ℕ) : Cmd :=
  (cellCommand (d % W)).join (cellCommand (d / W))

def unpadRow (b W : ℕ) : Cmd := seriesCommand (unpadCell W) (List.range b)

def unpad (b W : ℕ) : Cmd := blendCommand.join (mapCommand (unpadRow b W))

theorem unpadRow_within (b W : ℕ) : Within 3 (unpadRow b W) :=
  series_within (le_refl 3) _ _ (fun _ => ⟨cell_within _, cell_within _⟩)

theorem unpad_within (b W : ℕ) : Within 4 (unpad b W) :=
  ⟨blend_within, map_within (by decide)
    (RegisterSelect.within_mono (by decide : 3 ≤ 4) _ (unpadRow_within b W))⟩

private theorem join_small {p q : Cmd} {t k u l : ℕ} {x y z : Tree}
    (hp : Run p t k x y) (hq : Run q u l y z) (hy : y.count ≤ x.count) :
    Run (p.join q) (2*t+u+2) (2*k+l+1) x z := by
  intro env r base hr
  let V := amount x z
  have vpos : 1 ≤ V := by dsimp [V,amount]; omega
  have A : amount x y ≤ 2 * V := by dsimp [V,amount]; omega
  have B : amount y z ≤ V := by dsimp [V,amount]; omega
  have first := hp env r base hr
  have second := hq env r base hr
  have ts := Nat.mul_le_mul_left t A
  have ks := Nat.mul_le_mul_left k A
  have us := Nat.mul_le_mul_left u B
  have ls := Nat.mul_le_mul_left l B
  have dt : k * amount x y ≤ 2*k*V := by simpa only [Nat.mul_left_comm,Nat.mul_assoc] using ks
  have tt : t * amount x y ≤ 2*t*V := by simpa only [Nat.mul_left_comm,Nat.mul_assoc] using ts
  let cap := base + (2*k+l+1)*V
  let depth := (2*k+l+1)*V
  have h₁ := first.mono le_rfl
    (show _ ≤ cap by dsimp only [cap]; simp only [Nat.add_mul,Nat.one_mul]; omega) dt
  have h₂ := second.mono le_rfl
    (show _ ≤ cap by dsimp only [cap]; simp only [Nat.add_mul,Nat.one_mul]; omega)
    (show _ ≤ depth by dsimp only [depth]; simp only [Nat.add_mul,Nat.one_mul]; omega)
  apply (h₁.join h₂ (by dsimp only [depth]; simp only [Nat.add_mul,Nat.one_mul]; omega)).mono _
    le_rfl le_rfl
  change _ ≤ (2*t+u+2)*V
  simp only [Nat.add_mul]
  omega

private theorem entry_le {A : Type} (s : Series A) (v : A → Tree) (i : A) :
    (v i).count ≤ (stripe s v).count := by
  rw [stripe_simple]
  exact count_le_forest v (s.complete i)

theorem unpadCell_run {b W : ℕ} (hW : 0 < W) (d : Fin b)
    (v : Fin W → Fin (BatchRows.groups b W) → Tree) :
    Run (unpadCell W d.val) 272 274
      (stripe (Series.natural W) (fun u => stripe (Series.natural (BatchRows.groups b W)) (v u)))
      (v (BatchRows.row hW d) (BatchRows.group hW d)) :=
  join_small (numeric_cell (BatchRows.row hW d) (fun u => stripe (Series.natural _) (v u)))
    (numeric_cell (BatchRows.group hW d) (v (BatchRows.row hW d)))
    (entry_le (Series.natural W) (fun u => stripe (Series.natural _) (v u)) (BatchRows.row hW d))

private theorem blanks_count {A : Type} (p : Series A) :
    (stripe p (fun _ => Tree.atom false)).count = 2 * p.count + 1 := by
  rw [stripe_simple]
  change (Task.forest _ p.explore).count = 2 * p.explore.length + 1
  induction p.explore with
  | nil => rfl
  | cons a l ih =>
    simp only [Task.forest_cons, Tree.count, List.length_cons, Nat.mul_add, Nat.mul_one] at *
    omega

/-- Both dimensions and the prefix order are arbitrary. The space coefficient
is absolute. Only the time coefficient depends on the radix and bank width. -/
theorem unpad_run {P : Type} (p : Series P) {b W : ℕ} (hW : 0 < W)
    (v : Fin W → P → Fin (BatchRows.groups b W) → Tree) :
    Run (unpad b W) (2*(401*(W+1))+((b+1)*372+110)+2) 995
      (.fork (stripe (Series.natural W) (fun u =>
        stripe p (fun x => stripe (Series.natural (BatchRows.groups b W)) (v u x))))
        (stripe p (fun _ => .atom false)))
      (stripe p (fun x => stripe (Series.natural b) (fun d =>
        v (BatchRows.row hW d) x (BatchRows.group hW d)))) := by
  let cols := Series.natural W
  let f (x : P) (u : Fin W) := stripe (Series.natural (BatchRows.groups b W)) (v u x)
  let x := Tree.fork (stripe cols (fun u => stripe p (fun a => f a u)))
    (stripe p (fun _ => Tree.atom false))
  let y := stripe p (stripe cols ∘ f)
  have bl : Run blendCommand (401*(W+1)) 300 x y := by
    intro env r base hr
    have h := blend_bounded cols p f env r base hr
    change BoundedFits _ _ _ _ (401*(cols.count+1)*(x.count+1)) (base+300*x.count) (300*x.count) at h
    simp only [cols,Series.count_natural] at h
    apply h.mono (Nat.mul_le_mul_left _ (show x.count+1 ≤ amount x y by simp [amount])) _ _
    all_goals dsimp only [amount]; omega
  have small : y.count ≤ x.count := by
    have e := transpose_volume cols p f
    change _ + _ = y.count + _ at e
    dsimp only [x,Tree.count]
    rw [blanks_count]
    omega
  apply join_small (u := (b+1)*372+110) (l := 394) bl _ small
  apply map_run (t := (b+1)*372) (k := 344)
  intro a
  apply numeric_series (t := 272) (k := 274)
  intro d
  exact unpadCell_run hW d (fun u => v u a)

theorem effective_unpad : Effective ltr (fun x : ℕ × ℕ => unpad x.1 x.2) := by
  apply (effective_const ltr blendCommand).join
  apply effective_map
  apply InterchangeROM.effective_series
  · exact (InterchangeROM.effective_cell (Primrec.nat_mod.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp).join
      (InterchangeROM.effective_cell (Primrec.nat_div.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp)
  · exact (Primrec.list_range.comp Primrec.fst).to_comp

end InterchangeROMBank

end NearSquareRoot
end Computability
end OAI
