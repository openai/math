import OAI.Hierarchy.DescentResetLocalRows
import OAI.Hierarchy.DescentResetThreshold
import OAI.Hierarchy.DescentResetExceptionalBits

namespace OAI
/-! # Testing a reset collision with one shared threshold and the measured low cell -/

namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentColonies DescentGL DescentBaseProfile DescentIssuedFallbackPanel DescentBaseVariance
open scoped BigOperators Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {m c : ℕ}

theorem group_parent (d e : ℕ) (before : d≤e) (depth : e≤m) (x : Block m) :
    group e x/2^(e-d)=group d x := by
  simp only [group,width,Nat.div_div_eq_div_mul,←pow_add,show m-e+(e-d)=m-d by omega]

theorem natural_bin (L : Layout m) (flow : Block m→ℕ) (j : ℕ) (up : j≤m) (x : Block m) :
    binLoad flow (dyadicLayout up L) (bin up x)=
      ∑y : Block m,if group j y=group j x then flow ((rearrange L).symm y) else 0 := by
  rw [←Equiv.sum_comp (rearrange L) (fun y=>if group j y=group j x then flow ((rearrange L).symm y) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  have hit : bin up x=dyadicLayout up L i ↔ group j (rearrange L i)=group j x := by
    rw [Fin.ext_iff,layout_id]
    exact eq_comm
  simp only [hit,Equiv.symm_apply_apply]

def binHere {r : ℕ} (flow : Block r→ℕ) (j : ℕ) (x : Block r) :=
  ∑y : Block r,if group j y=group j x then flow y else 0

theorem low_bin (small : c≤m) (L : Layout m) (flow : Block m→ℕ) (j : ℕ) (lo : c≤j) (up : j≤m)
    (hi : Block c) (x : Block (m-c)) :
    binLoad flow (dyadicLayout up L) (bin up (join small hi x))=
      binHere (fun y=>flow ((rearrange L).symm (join small hi y))) (j-c) x := by
  rw [natural_bin]
  have proj:=sum_cell small (Equiv.refl _) hi (fun y=>group j y=group j (join small hi x))
    (fun z=>flow ((rearrange L).symm z)) (by
      intro y good
      have h : high small y=high small (join small hi x):=Fin.ext (group_ancestor lo good)
      exact h.trans (high_join small hi x))
  simp only [Finset.sum_filter,Equiv.refl_symm,Equiv.refl_apply] at proj
  refine Eq.trans ?_ (proj.trans ?_)
  · apply Finset.sum_congr rfl
    intro y _
    by_cases h : group j y = group j (join small hi x) <;> simp [h]
  · unfold binHere
    apply Finset.sum_congr rfl
    intro i _
    have same := group_same small hi j lo i x
    let : Decidable (group j (join small hi i) = group j (join small hi x)) := Classical.propDecidable _
    exact if_congr same rfl rfl

theorem bin_onto (j : ℕ) (up : j≤m) (q : Block j) : ∃x : Block m,bin up x=q := by
  let x:=join up q (0 : Block (m-j))
  exact ⟨x,Fin.ext (congrArg Fin.val (high_join up q (0 : Block (m-j))))⟩

variable (small : c≤m) (near : V→Finset V) (b : V→ℕ) (baseLow : ∀v,c≤b v) (depth : ∀v,b v≤m)
variable (L : Layout m) (weight : V→Block m→ℕ) (traffic : V→V→Block m→ℕ)
variable (Δ f B K : ℕ) (hi : Block c)
abbrev edgeLevel (e : Contacts near) := max (b e.1) (b e.2.val)
def incident (v : V) (e : Contacts near) := e.1=v ∨ e.2.val=v

/-- Every test uses one live contact's rearranged donor values inside the common high cell.
The threshold comes from the zero-character sum of that same directed contact. -/
def «over» (v : V) (x : Block (m-c)) (caps : Contacts near→ℕ) : Prop :=
  ∃e : Contacts near,incident near v e ∧ ∃i : Block (m-c),group (b v-c) i=group (b v-c) x ∧
    threshold K (2^f*B) (edgeLevel near b e) (∑z,traffic e.1 e.2.val z) (caps e)<
      binHere (fun y=>traffic e.1 e.2.val ((rearrange L).symm (join small hi y))) (edgeLevel near b e-c) i

include baseLow in
omit [Fintype V] [DecidableEq V] in
theorem collision_at (v : V) (x : Block (m-c)) (caps : Contacts near→ℕ) (pos : 0<K)
    (fits : ∀e i,binHere (fun y=>traffic e.1 e.2.val ((rearrange L).symm (join small hi y)))
      (edgeLevel near b e-c) i≤caps e) :
    let id:=group (b v) (join small hi x)
    (∃e : Contacts near,∃q : Block (edgeLevel near b e),
      K*(∑z,traffic e.1 e.2.val z)+(2^f*B)*2^(edgeLevel near b e) <
        K*2^(edgeLevel near b e)*binLoad (traffic e.1 e.2.val)
          (dyadicLayout (max_le (depth e.1) (depth e.2.val)) L) q ∧
        ((reservationEndpoints b (fun e:Contacts near=>e.1) (fun e=>e.2.val) e q).1=(v,id) ∨
         (reservationEndpoints b (fun e:Contacts near=>e.1) (fun e=>e.2.val) e q).2=(v,id))) ↔
       «over» small near b L traffic f B K hi v x caps := by
  intro id
  have hiJ (e:Contacts near) : edgeLevel near b e≤m:=max_le (depth _) (depth _)
  have loJ (e:Contacts near) : c≤edgeLevel near b e:=(baseLow _).trans (le_max_left ..)
  have ends (e:Contacts near) (y:Block m) :
      reservationEndpoints b (fun e:Contacts near=>e.1) (fun e=>e.2.val) e (bin (hiJ e) y)=
        ((e.1,group (b e.1) y),(e.2.val,group (b e.2.val) y)) := by
    simp only [reservationEndpoints,bin,group_parent _ _ (le_max_left ..) (hiJ e),
      group_parent _ _ (le_max_right ..) (hiJ e)]
  have scaled (e:Contacts near) (i:Block (m-c)) := crossed K (2^f*B) (edgeLevel near b e)
    (∑z,traffic e.1 e.2.val z) (caps e) _ pos (fits e i)
  constructor
  · rintro ⟨e,q,large,edge⟩
    obtain ⟨y,rfl⟩:=bin_onto _ (hiJ e) q
    rw [ends] at edge
    have which : incident near v e ∧ group (b v) y=id := by
      rcases edge with a|a
      · rcases Prod.mk.inj a with ⟨rfl,id'⟩;exact ⟨Or.inl rfl,id'⟩
      · rcases Prod.mk.inj a with ⟨rfl,id'⟩;exact ⟨Or.inr rfl,id'⟩
    have hiy : high small y=hi :=
      (show high small y=high small (join small hi x) from Fin.ext (group_ancestor (baseLow v) which.2)).trans (high_join ..)
    have ydef : join small hi (low (c:=c) y)=y := by rw [←hiy,join_high_low]
    refine ⟨e,which.1,low y,(group_same small hi _ (baseLow v) _ x).mp (by rw [ydef];exact which.2),?_⟩
    apply (scaled e _).mpr
    rw [←low_bin small L _ _ (loJ e) (hiJ e),ydef]
    exact large
  · rintro ⟨e,which,i,hit,large⟩
    refine ⟨e,bin (hiJ e) (join small hi i),?_,?_⟩
    · rw [low_bin small L _ _ (loJ e) (hiJ e)]
      exact (scaled e i).mp large
    · rw [ends]
      have same := (group_same small hi _ (baseLow v) i x).mpr hit
      rcases which with h|h
      · exact Or.inl (Prod.ext h ((congrArg (fun t => group (b t) (join small hi i)) h).trans same))
      · exact Or.inr (Prod.ext h ((congrArg (fun t => group (b t) (join small hi i)) h).trans same))

theorem binHere_bound {r : ℕ} (flow : Block r→ℕ) (j : ℕ) (x : Block r)
    (cap : ℕ) (fits : ∀y,flow y≤cap) : binHere flow j x≤2^r*cap := by
  unfold binHere
  calc
    _≤∑_y : Block r,cap:=Finset.sum_le_sum fun y _=>by split <;> first | exact fits y | exact Nat.zero_le _
    _=2^r*cap:=by simp

include baseLow in
/-- The local stored split bit and the local failed-contact test give exactly the true
exceptional base selected by the measured reset, including coincident directed endpoints. -/
theorem keys_at (v : V) (x : Block (m-c)) (bound : ℕ) (ht : ∀u z i,traffic u z i≤bound) (positive : 0<K) (hB : 0<B) :
    (v,group (b v) (join small hi x))∈resetKeys near Δ f B K weight (fun u z i=>(traffic u z i:ℝ)) b depth L ↔
      Split (fun t j=>rearrangedLoad weight L t (join small hi j)) (fun u z=>z∈near u) (32*Nat.clog 2 (2*Δ))
        (2*(2^f*B)) v (b v-c) x ∨ «over» small near b L traffic f B K hi v x (fun _=>2^(m-c)*bound) := by
  rw [resetKeys_iff near Δ f B K hB positive weight traffic b depth L]
  apply or_congr
  · have part:=split_at small (rearrangedLoad weight L) (fun u z=>z∈near u) (32*Nat.clog 2 (2*Δ))
      (2*(2^f*B)) v hi (b v-c) x
    rw [Nat.add_sub_of_le (baseLow v)] at part
    exact ⟨fun ⟨i,marked,equal⟩=>part.mp (.same equal marked),fun yes=>⟨_,part.mpr yes,rfl⟩⟩
  · exact collision_at small near b baseLow depth L traffic f B K hi v x _ positive
      (fun e i=>binHere_bound _ _ _ _ (fun y=>ht _ _ _))

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
