import OAI.Hierarchy.DescentResetActorTable
import OAI.Hierarchy.DescentResetPackedStencil
import OAI.Hierarchy.DescentResetLocalRows

namespace OAI
/-! # Searching the original terminal roster from one remixed low-coordinate window -/
namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentColonies DescentGL DescentFineTerminals DescentIssuedFallbackPanel
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {m c : ℕ}
abbrev Coordinates := (ℕ×ℕ)×Option ℕ

def expand (c hi : ℕ) (z : Coordinates) : Coordinates :=
  ((c+z.1.1,hi*2^z.1.1+z.1.2),z.2)

theorem expand_relative {z : Coordinates} (lower : c≤z.1.1) :
    expand c (z.1.2/2^(z.1.1-c)) (fieldsRelative c z)=z := by
  rcases z with ⟨⟨d,j⟩,tag⟩
  change c ≤ d at lower
  simp only [expand,fieldsRelative,Prod.mk.injEq,and_true]
  exact ⟨Nat.add_sub_of_le lower,Nat.div_add_mod' ..⟩

theorem relative_expand (hi : ℕ) (z : Coordinates) (ok : z.1.2<2^z.1.1) :
    fieldsRelative c (expand c hi z)=z ∧ (expand c hi z).1.2/2^((expand c hi z).1.1-c)=hi := by
  rcases z with ⟨⟨d,j⟩,tag⟩
  change j < 2^d at ok
  constructor
  · simp [expand,fieldsRelative,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt ok]
  · change (hi*2^d+j) / 2^(c+d-c) = hi
    rw [Nat.add_sub_cancel_left, Nat.mul_comm hi, Nat.mul_add_div (Nat.two_pow_pos d),
      Nat.div_eq_of_lt ok,Nat.add_zero]

variable (near : V→Finset V) (b : V→ℕ) (L : Layout m) (wt : V→Block m→ℕ)
  (f D B g Y : ℕ) (safe : ∀v x,wt v x≤B) (bad : V→ℕ→Prop) (hub : V→Bool)
local notation "ep" => endpoint near b L wt f D B g Y safe bad hub
variable (small : c≤ m) (hubLow : c≤ m-g) (lo : ∀v,c≤b v) (hi : ∀v,b v≤ m)

include hubLow lo hi in
omit [Fintype V] [DecidableEq V] in
theorem endpoint_window (v : V) (x : Block m) :
    c≤(ep v x).1.1 ∧ (ep v x).1.1≤ m ∧
    (ep v x).1.2/2^((ep v x).1.1-c)=(high small (rearrange L x)).val := by
  have actual (d : ℕ) (lower : c≤d) (upper : d≤ m) :
      c≤d ∧ d≤ m ∧ group d (rearrange L x)/2^(d-c)=(high small (rearrange L x)).val :=
    ⟨lower,upper,group_parent c d lower upper _⟩
  cases h : hub v with
  | true=>simpa [endpoint,h] using actual (m-g) hubLow (Nat.sub_le ..)
  | false=>
    let raw:=rearrangedLoad wt L
    let room (u) (y) : raw u y≤B:=safe u _
    let d:=leaf (D:=D) (f:=f) near raw room b v (rearrange L x)
    have upper : d≤ m:=max_le (hi v) ((depth_le raw _ D (f+1) B room v (rearrange L x)).trans (Nat.sub_le ..))
    exact (by simpa [endpoint,h,leafKey,raw,d] using actual d ((lo v).trans (le_max_left ..)) upper)

include hubLow lo hi in
omit [Fintype V] [DecidableEq V] in
/-- The original order of whole occurrences is retained in each remixed endpoint
record. The inverse layout selects the unique old occurrence feeding each low digit. -/
theorem terminal_window (v : V) (blockId : Block c) (z : Coordinates) (legal : z.1.2<2^z.1.1) :
    (∃x : Block m,ep v x=expand c blockId.val z) ↔
      ∃loX : Block (m-c),fieldsRelative c (ep v ((rearrange L).symm (join small blockId loX)))=z := by
  let rowLow:=endpoint_window near b L wt f D B g Y safe bad hub small hubLow lo hi v
  constructor
  · rintro ⟨x,hit⟩
    have facts:=rowLow x
    have coarse : high small (rearrange L x)=blockId:=by
      apply Fin.ext
      rw [←facts.2.2,hit]
      exact (relative_expand (c:=c) blockId.val z legal).2
    refine ⟨low (c:=c) (rearrange L x),?_⟩
    rw [←coarse,join_high_low,Equiv.symm_apply_apply,hit]
    exact (relative_expand (c:=c) blockId.val z legal).1
  · rintro ⟨j,hj⟩
    let x:=(rearrange L).symm (join small blockId j)
    have facts:=rowLow x
    have hx : (ep v x).1.2/2^((ep v x).1.1-c)=blockId.val:=by
      simpa [x] using facts.2.2
    refine ⟨x,?_⟩
    rw [←expand_relative (z:=ep v x) facts.1,hx]
    exact congrArg (expand c blockId.val) hj

omit [Fintype V] [DecidableEq V] in
theorem endpoint_tag (pos : 0<Y) (v : V) (x : Block m) (j : ℕ) (found : (ep v x).2=some j) : j<Y := by
  cases hubAt : hub v with
  | true=>simp [endpoint,hubAt] at found
  | false=>
    simp only [endpoint,hubAt,Bool.false_eq_true,ite_false,Option.some.injEq] at found
    rw [←found]
    exact (min_le_right ..).trans_lt (by omega)

theorem suffix_code_injective {r Y : ℕ} {a z : Coordinates}
    (ai : a.1.2<2^r) (zi : z.1.2<2^r)
    (at_ : ∀j,a.2=some j→j<Y) (zt : ∀j,z.2=some j→j<Y) :
    Stencil.shapeCode r Y a=Stencil.shapeCode r Y z ↔ a=z := by
  let opt (v : Option ℕ) : ℕ := v.elim 0 (·+1)
  have tagInjective : Function.Injective opt := by
    intro x y same
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some j => exact (Nat.succ_ne_zero j same.symm).elim
    | some i =>
      cases y with
      | none => exact (Nat.succ_ne_zero i same).elim
      | some j =>
        change i.succ = j.succ at same
        exact congrArg some (Nat.succ.inj same)
  have digitFit (u : Option ℕ) (bound : ∀ j, u = some j → j < Y) : opt u < Y+1 := by
    cases u with
    | none => exact Nat.zero_lt_succ _
    | some j => exact Nat.succ_lt_succ (bound j rfl)
  have separate (q : ℕ) {i j p l : ℕ} (ij : i < q) (pj : p < q)
      (same : j*q+i = l*q+p) : j = l ∧ i = p := by
    have quotient (h d : ℕ) (bound : d < q) : (h*q+d)/q = h := by
      rw [Nat.add_comm (h*q) d, Nat.add_mul_div_right d h (Nat.zero_lt_of_lt bound),
        Nat.div_eq_of_lt bound, Nat.zero_add]
    have remainder (h d : ℕ) (bound : d < q) : (h*q+d)%q = d := by
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt bound]
    exact ⟨(quotient j i ij).symm.trans ((congrArg (·/q) same).trans (quotient l p pj)),
      (remainder j i ij).symm.trans ((congrArg (·%q) same).trans (remainder l p pj))⟩
  constructor
  · intro same
    change (a.1.1*2^r+a.1.2)*(Y+1)+opt a.2 = (z.1.1*2^r+z.1.2)*(Y+1)+opt z.2 at same
    obtain ⟨coords,tags⟩ := separate (Y+1) (digitFit a.2 at_) (digitFit z.2 zt) same
    obtain ⟨depth,offset⟩ := separate (2^r) ai zi coords
    exact Prod.ext (Prod.ext depth offset) (tagInjective tags)
  · rintro rfl
    rfl

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
