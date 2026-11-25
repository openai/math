import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineLanes
import OAI.Computability.NearSquareRoot.InterchangeROMAddressDescriptor

/-! # Pricing an affine mask bank on a native interchange stream -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace AffineAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic InterchangeROMAddress InterchangeAffineMask InterchangeROMColors

theorem forest_member_count {T : Type} (f : T → Tree) (s : List T) (a : T) (h : a ∈ s) :
    (f a).count ≤ (Task.forest f s).count := by
  induction s with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons x s ih =>
    rw [Task.forest_cons,Tree.count]
    rcases List.mem_cons.mp h with rfl | hx
    · omega
    · have := ih hx
      omega

private theorem sum_price {T : Type} (s : List T) (p : T → ℕ) (m : ℕ) (h : ∀ t ∈ s, p t ≤ m) :
    costSum p s ≤ s.length*m := by
  induction s with
  | nil => simp
  | cons x s ih =>
    have a := h x List.mem_cons_self
    have b := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [costSum_cons,List.length_cons,Nat.succ_mul]
    omega

abbrev headerCount {D : Type} {mask : D → Tree} (desc : D → Tree) (bank : BankInput D mask) :=
  (Task.forest (pairDesc desc) bank.configs).count

/-- Each comparison can use the total serialized descriptor length as its
polynomial argument. The stream itself is traversed linearly per class. -/
theorem bank_price_bound {D : Type} {mask : D → Tree} (desc : D → Tree) (cost : D → ℕ)
    (bank : BankInput D mask) (comparisonCost : ℕ)
    (pair : ∀ k ∈ bank.rows.colors, cost (bank.faces k).1 ≤ comparisonCost ∧
      cost (bank.faces k).2 ≤ comparisonCost) :
    BankInput.total desc cost bank ≤
      (bank.rows.colors.length+1) * (headerCount desc bank + 2*comparisonCost +
        size (bank.rows.source.map Prod.snd) + size (bank.rows.target.map Prod.snd) + 1) := by
  let H := headerCount desc bank
  have entries : ∀ v ∈ bank.configs, pairPrice desc cost v ≤ H + 2*comparisonCost := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp (show v ∈ bank.rows.colors.map bank.faces from hv)
    have ⟨l,r⟩ := pair k hk
    have tag := forest_member_count (pairDesc desc) bank.configs (bank.faces k) hv
    change (desc (bank.faces k).1).count + (desc (bank.faces k).2).count + 1 ≤ H at tag
    unfold pairPrice
    omega
  have total := sum_price _ _ _ entries
  have length : bank.configs.length = bank.rows.colors.length := List.length_map _
  rw [length] at total
  change costSum _ _ + H + ((bank.rows.colors.length+1) * (_+_+1)) ≤ _
  let V := size (bank.rows.source.map Prod.snd) + size (bank.rows.target.map Prod.snd) + 1
  change costSum _ _ + H + (bank.rows.colors.length+1)*V ≤
    (bank.rows.colors.length+1) *
      (H+2*comparisonCost+size (bank.rows.source.map Prod.snd)+size (bank.rows.target.map Prod.snd)+1)
  rw [show H+2*comparisonCost+size (bank.rows.source.map Prod.snd)+
    size (bank.rows.target.map Prod.snd)+1 = H+2*comparisonCost+V by dsimp only [V]; omega]
  rw [Nat.mul_add (bank.rows.colors.length+1) (H+2*comparisonCost) V,Nat.succ_mul bank.rows.colors.length (H+2*comparisonCost)]
  omega

private theorem monotone_price (d : ℕ) : Monotone (localPrice d) := by
  intro a b h
  unfold localPrice
  gcongr

variable {J : Type} [DecidableEq J] {n b f : ℕ}
    (ord : J ≃ Fin n) (P G S : Tape) (hp : solid P) (hg : solid G) (hs : solid S) (hb : 2 ≤ b)

/-- Uniform native bound for the complete comparison and payload-routing
command, expressed in the descriptor forest physically supplied to the bank. -/
theorem native_price (x y : Spot J) (A B : Row ℕ) (d : ℕ)
    (bank : BankInput Comparison Comparison.result)
    (describes : ∀ k ∈ bank.rows.colors,
      bank.faces k = nativeFaces (f:=f) ord P G S hp hg hs hb x y A B k) :
    let N := (arrays ord (line b f) P G S).count
    let H := headerCount Affine.tag bank
    BankInput.total Affine.tag (Comparison.budget d) bank ≤
      (bank.rows.colors.length+1) * (H + 2*((N+1)*localPrice d H) +
        size (bank.rows.source.map Prod.snd) + size (bank.rows.target.map Prod.snd) + 1) := by
  apply bank_price_bound
  intro k hk
  have mem : bank.faces k ∈ bank.configs := List.mem_map_of_mem (f:=bank.faces) hk
  have bound := forest_member_count (pairDesc Affine.tag) bank.configs (bank.faces k) mem
  let N := (arrays ord (line b f) P G S).count
  let H := headerCount Affine.tag bank
  change size (bank.faces k).1.desc + size (bank.faces k).2.desc + 1 ≤ H at bound
  have face {z : Comparison} (sizeCap : size z.desc ≤ H)
      (price : z.budget d ≤ (N+1)*localPrice d (size z.desc)) :
      z.budget d ≤ (N+1)*localPrice d H :=
    price.trans (Nat.mul_le_mul_left _ (monotone_price d sizeCap))
  obtain before := comparison_budget (f:=f) ord P G S hp hg hs hb x y (literal (b^f) A B k) d
  obtain after_ := comparison_budget (f:=f) ord P G S hp hg hs hb x y (literal (b^f) B A k.swap) d
  rw [describes k hk] at bound ⊢
  exact ⟨face (by omega) before,face (by omega) after_⟩

/-- A field permutation leaves the serialized volume of the entire row
stream unchanged, even when the payload sizes differ at every address. -/
theorem tab_volume_eq {X Y : Type} [Codec Y] (s : Series X) (q : X ≃ X) (v : X → Y) :
    size (s.tab (v ∘ q)) = size (s.tab v) := by
  have perm : (s.explore.map q).Perm s.explore :=
    (List.perm_ext_iff_of_nodup (s.nodup.map q.injective) s.nodup).mpr (fun x =>
      ⟨fun _ => s.complete x,fun _ => List.mem_map.mpr ⟨q.symm x,s.complete _,q.apply_symm_apply x⟩⟩)
  have data := perm.map v
  rw [List.map_map] at data
  change (s.tab (v ∘ q)).Perm (s.tab v) at data
  rw [← costSum_le_length_size,← costSum_le_length_size, data.length_eq]
  exact congrArg (fun n => _+n+1) (data.map size).sum_eq

variable [NeZero b]

/-- The width program can be priced from the single input stream. -/
theorem width_price (x : Spot J) (a : Span b) (d : ℕ) (v : Keys P G S J (Block b f) → Tree) :
    let w := widthRows a.neg a.top.count a.down.count
    let bank := widthBank ord P G S hp hg hs hb x a v
    let s := arrays ord (line b f) P G S
    let H := headerCount Affine.tag bank
    BankInput.total Affine.tag (Comparison.budget d) bank ≤
      ((colors w.1 w.2).length+1)*(H+2*((s.count+1)*localPrice d H)+
        2*size (s.tab v)+1) := by
  let w := widthRows a.neg a.top.count a.down.count
  let bank := widthBank ord P G S hp hg hs hb x a v
  have price := native_price ord P G S hp hg hs hb x x w.1 w.2 d bank (fun _ _ => rfl)
  change BankInput.total _ _ _ ≤ _ at price ⊢
  simpa only [bank,widthBank,slotRows_colors,slotRows_source,slotRows_target,tab_volume_eq,two_mul,
    Nat.add_assoc,w] using price

/-- A translate controlled by an earlier field has the same bound. -/
theorem gather_price (x y : Spot J) (early : Lag.early (ranking ord) x y) (a : Pinpoint b)
    (d : ℕ) (v : Keys P G S J (Block b f) → Tree) :
    let bank := gatherBank ord P G S hp hg hs hb x y early a v
    let s := arrays ord (line b f) P G S
    let H := headerCount Affine.tag bank
    BankInput.total Affine.tag (Comparison.budget d) bank ≤
      ((colors (pinRows a).1 (pinRows a).2).length+1)*(H+2*((s.count+1)*localPrice d H)+
        2*size (s.tab v)+1) := by
  let bank := gatherBank ord P G S hp hg hs hb x y early a v
  have price := native_price ord P G S hp hg hs hb x y (pinRows a).1 (pinRows a).2 d bank (fun _ _ => rfl)
  change BankInput.total _ _ _ ≤ _ at price ⊢
  simpa only [bank,gatherBank,axisRows_colors,axisRows_source,axisRows_target,tab_volume_eq,two_mul,
    Nat.add_assoc] using price

end AffineAddress

end NearSquareRoot
end Computability
end OAI
