import OAI.Hierarchy.DescentCoarseCellSum
import OAI.Hierarchy.DescentColonyScanLeaves

namespace OAI
/-! # The measured reset split restricts to each packed low-coordinate panel -/

namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentColonies DescentIssuedFallbackPanel
open scoped Classical BigOperators
noncomputable section
variable {m c : ℕ} (small : c≤m) {V : Type}

theorem join_group (hi : Block c) (x : Block (m-c)) (d : ℕ) :
    group (c+d) (join small hi x)=hi.val*2^(m-c-((m-c)-d))+group d x := by
  let lo:=(m-c)-d
  have len : m-(c+d)=lo := by dsimp [lo];omega
  have expand : 2^(m-c)=2^(m-c-lo)*2^lo := by
    rw [←pow_add];congr 1;dsimp [lo];omega
  have divide (a z : ℕ) :
      (a*2^(m-c)+z)/2^(m-(c+d))=a*2^(m-c-lo)+z/2^lo := by
    rw [len,expand,←Nat.mul_assoc,Nat.mul_comm (a*2^(m-c-lo)) (2^lo),
      Nat.mul_add_div (Nat.two_pow_pos _)]
  exact divide hi.val x.val

theorem mass_join (wt : V→Block m→ℕ) (v : V) (hi : Block c) (d : ℕ) (x : Block (m-c)) :
    mass wt v (c+d) (join small hi x)=mass (fun t j=>wt t (join small hi j)) v d x := by
  have prog:=sum_cell small (Equiv.refl _) hi (fun y=>group (c+d) y=group (c+d) (join small hi x)) (wt v) (by
    intro y h
    have hh:=group_ancestor (Nat.le_add_right c d) h
    exact (Fin.ext hh).trans (high_join small hi x))
  simpa only [mass,interval,Equiv.refl_symm,Equiv.refl_apply,join_group, Nat.add_right_inj,
    Finset.sum_filter] using prog

/-- No vote originating in another high cell can propagate into the marked
suffix, even along an arbitrary number of neighbor links. -/
theorem split_low (wt : V→Block m→ℕ) (adj : V→V→Prop) (D cap : ℕ)
    {v d x} (mark : Split wt adj D cap v d x) (lo : c≤d) :
    Split (fun t j=>wt t (join small (high small x) j)) adj D cap v (d-c) (low x) := by
  induction mark with
  | @heavy v d x exceed=>
    apply Split.heavy
    have eqn:=mass_join small wt v (high small x) (d-c) (low x)
    rw [Nat.add_sub_of_le lo,join_high_low] at eqn
    rwa [←eqn]
  | @parent v d x prev ih=>
    apply Split.parent
    convert ih (by omega : c≤d+1) using 1; omega
  | @neighbor v z d x edge prev ih=>
    apply Split.neighbor edge
    convert ih (by omega : c≤d+D) using 1; omega
  | @same v d x y eqn prev ih=>
    have highEq : high small x=high small y := Fin.ext (group_ancestor lo eqn)
    have grouped : group (d-c) (low (c:=c) x)=group (d-c) (low (c:=c) y) := by
      have xx:=join_group small (high small x) (low x) (d-c)
      have yy:=join_group small (high small y) (low y) (d-c)
      rw [Nat.add_sub_of_le lo,join_high_low] at xx yy
      rw [highEq] at xx
      omega
    apply Split.same grouped
    simpa only [highEq] using ih lo

theorem split_join (wt : V→Block m→ℕ) (adj : V→V→Prop) (D cap : ℕ) (hi : Block c) {v d x}
    (mark : Split (fun t j=>wt t (join small hi j)) adj D cap v d x) :
    Split wt adj D cap v (c+d) (join small hi x) := by
  induction mark with
  | heavy below=>exact .heavy (by rwa [mass_join small wt _ hi _ _])
  | parent old ih=>exact .parent (by simpa only [Nat.add_assoc] using ih)
  | neighbor edge old ih=>exact .neighbor edge (by simpa only [Nat.add_assoc] using ih)
  | same eqn old ih=>exact .same (by rw [join_group,join_group,eqn]) ih

theorem split_at (wt : V→Block m→ℕ) (adj : V→V→Prop) (D cap : ℕ)
    (v : V) (hi : Block c) (d : ℕ) (x : Block (m-c)) :
    Split wt adj D cap v (c+d) (join small hi x) ↔ Split (fun t j=>wt t (join small hi j)) adj D cap v d x := by
  constructor
  · intro yes
    simpa only [high_join,low_join,Nat.add_sub_cancel_left] using split_low small wt adj D cap yes (Nat.le_add_right c d)
  · exact split_join small wt adj D cap hi

private theorem split_earlier {n : ℕ} (wt : V→Block n→ℕ) (adj : V→V→Prop) (D cap : ℕ)
    {v x d e} (yes : Split wt adj D cap v e x) (before : d≤e) : Split wt adj D cap v d x := by
  revert yes
  induction before with
  | refl=>exact id
  | step _ ih=>intro h;exact ih (.parent h)

theorem split_iff_before {n : ℕ} (wt : V→Block n→ℕ) (adj : V→V→Prop)
    (D a B : ℕ) (safe : ∀v x,wt v x≤B) (v : V) (x : Block n) (d : ℕ) :
    Split wt adj D (2^a*B) v d x ↔ d<depth wt adj D a B safe v x := by
  refine ⟨fun yes=>?_,earlier_split wt adj D a B safe v x⟩
  by_contra! early
  have hit:=split_earlier wt adj D (2^a*B) yes early
  unfold depth at hit
  exact Nat.find_spec (p:=fun j => ¬Split wt adj D (2^a*B) v j x)
    ⟨n-a,fun h => (Nat.lt_irrefl _) (split_shallow wt adj D a B safe h)⟩ hit

theorem depth_at (wt : V→Block m→ℕ) (adj : V→V→Prop) (D a B : ℕ)
    (safe : ∀v x,wt v x≤B) (v : V) (hi : Block c) (x : Block (m-c)) :
    depth wt adj D a B safe v (join small hi x)-c=
      depth (fun t j=>wt t (join small hi j)) adj D a B (fun t _j=>safe t _) v x := by
  let big:=depth wt adj D a B safe v (join small hi x)
  let short:=depth (fun t j=>wt t (join small hi j)) adj D a B (fun t j=>safe t _) v x
  have same (d : ℕ) : c+d<big ↔ d<short :=
    (split_iff_before wt adj D a B safe v _ _).symm.trans ((split_at small wt adj D _ v hi d x).trans
      (split_iff_before _ adj D a B (fun t j=>safe t _) v x d))
  change big-c=short
  have h₁:=same short;have h₂:=same (big-c)
  omega

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
