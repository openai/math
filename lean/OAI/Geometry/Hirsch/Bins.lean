import OAI.Geometry.Hirsch.Decoration

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

open Naming

namespace Naming

variable (u : Dials) (p : ℕ)

theorem product (hp : p ≤ Naming.P u) : H u ^ p * (length u p * H u) = N u := by
  unfold length N; rw [← pow_succ,← pow_add]; congr 1; omega

theorem parent_lt (hp : p ≤ Naming.P u) (r : Radii u) : block u p r/H u < H u ^ p := by
  unfold block
  rw [Nat.div_div_eq_div_mul,Nat.div_lt_iff_lt_mul (Nat.mul_pos (length_pos ..) (Hpos _)),product _ _ hp]
  exact r.isLt

theorem card_block (j : ℕ) :
    (Finset.univ.filter (fun r : Radii u => block u p r = j)).card ≤ length u p := by
  rw [← Finset.card_range (length u p)]
  apply Finset.card_le_card_of_injOn (fun r => r.val % length u p)
  · exact fun r _ => Finset.mem_range.mpr (Nat.mod_lt _ (length_pos ..))
  · intro r hr s hs he
    have eq := (Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hs).2.symm
    change r.val / length u p = s.val / length u p at eq
    exact Fin.ext ((Nat.mod_add_div ..).symm.trans ((congrArg₂ (· + ·) he (congrArg (length u p * ·) eq)).trans
      (Nat.mod_add_div ..)))

end Naming

namespace Legs.Decoration

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (key : Bool → X) (p : ℕ)

def region (r : Radii u) := (A.active r).ball p (R u) (key false) ∪ (A.active r).ball p (R u) (key true)

theorem region_bound (r : Radii u) : (A.region key p r).card ≤ M u := by
  have h := ((A.active r).edges p).card (R u) (key false)
  have h' := ((A.active r).edges p).card (R u) (key true)
  unfold region M Network.ball
  exact (Finset.card_union_le ..).trans ((Nat.add_le_add h h').trans_eq (two_mul _).symm)

theorem region_sub (r : Radii u) (d : Bool) : (A.active r).ball p (R u) (key d) ⊆ A.region key p r := by
  cases d
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

def Calm (r : Radii u) := ∀ i ∈ A.region key p r, ∀ j ∈ A.region key p r, ∀ m,
  block u p m = block u p r → ¬A.Break m i j

variable {A key p} {r s : Radii u}

theorem Fixed.slots (h : A.Fixed) (hp : p ≤ Naming.P u) (he : block u p r/H u = block u p s/H u)
    {a : u.Ticket} (ha : u.phase a < p) (i : X) : (A.active r).slot a i = (A.active s).slot a i :=
  h i a r s (ancestor _ ha hp he)

theorem Fixed.region (h : A.Fixed) (hp : p ≤ Naming.P u) (he : block u p r/H u = block u p s/H u) :
    A.region key p r = A.region key p s := by
  have eq : (A.active r).edges p = (A.active s).edges p := by
    funext i a
    rcases a with d | a
    · rfl
    · by_cases ha : u.phase a < p
      · simp only [Network.edges,ite_eq_left ha,h.slots hp he ha]
      · simp [Network.edges,ha]
  unfold Decoration.region Network.ball; rw [eq]

theorem Fixed.agree (h : A.Fixed) (hp : p ≤ Naming.P u) (he : block u p r/H u = block u p s/H u)
    {I : Type} {Q : Network u I} {f : X → I} {k : ℕ} {i : X}
    (hh : (A.active r).Agree Q f p k i) : (A.active s).Agree Q f p k i := by
  induction k generalizing i with
  | zero => exact True.intro
  | succ k ih =>
    refine ⟨hh.1,hh.2.1,fun d hl => ⟨(hh.2.2.1 d hl).1,ih (hh.2.2.1 d hl).2⟩,?_⟩
    intro a ha
    rw [← h.slots hp he ha]
    exact ⟨(hh.2.2.2 a ha).1,ih (hh.2.2.2 a ha).2⟩

theorem Calm.permute (h : A.Calm key p r) (he : block u p s = block u p r) :
    ∃ e : Equiv.Perm (NodeName u), ∀ i ∈ A.region key p r, e (A.name r i) = A.name s i := by
  apply Network.permute
  intro i hi j hj
  rw [A.names,A.names]
  let eq := fun k => A.fan.view A.data k i = A.fan.view A.data k j
  have aux : ∀ x y : ℕ, x ≤ y → block u p x = block u p r → block u p y = block u p r → (eq x ↔ eq y) := by
    intro x y hxy hx
    induction y,hxy using Nat.le_induction with
    | base => exact fun _ => Iff.rfl
    | succ y hle ih =>
      intro hy
      have h₁ : block u p x ≤ block u p y := Nat.div_le_div_right hle
      have h₂ : block u p y ≤ block u p (y+1) := Nat.div_le_div_right (Nat.le_succ y)
      have mid : block u p y = block u p r := by omega
      exact (ih mid).trans ⟨fun hh => by_contra (fun hn => h i hi j hj y mid ⟨hh,hn⟩),
        fun hh => A.fan.trunc _ (Nat.le_succ _) hh⟩
  rcases le_total r.val s.val with hr | hr
  · exact aux _ _ hr rfl he
  · exact (aux _ _ hr he rfl).symm

def Good (A : L.Decoration) (key : Bool → X) (r : Radii u) := ∀ p ≤ Naming.P u, A.Calm key p r

theorem Good.model (h : A.Good key r) (hs : A.Safe) :
    ∃ Q : Network u (NodeName u), ∀ d, (A.active r).Agree Q (A.name r) (Naming.P u) (R u) (key d) := by
  obtain ⟨Q,hQ⟩ := A.model hs r (Naming.P u) _ (A.region_bound key _ r)
    (fun i hi j hj => h _ le_rfl i hi j hj _ rfl) (key true)
  exact ⟨Q,fun d => hQ _ _ (A.region_sub key _ r d)⟩

theorem Good.earn (h : A.Good key r) (fixed : A.Fixed) (v : u.Valid) (a : u.Ticket) (d : Bool)
    {Q : Network u (NodeName u)} (hq : (A.active r).Agree Q (A.name r) (Naming.P u) (R u) (key d))
    (hw : Q.want v a (A.name r (key d))) : A.Earn v a (block u (u.phase a) r) (key d) := by
  intro s he Q' hq'
  have hp : u.phase a ≤ Naming.P u := (u.phase_lt _).le
  have hr : Network.window u ≤ R u := by unfold R; omega
  obtain ⟨e,he'⟩ := (h _ hp).permute he
  have hh := fixed.agree hp (congrArg (· / H u) he) hq'
  have agree := (hq.less hp hr).compare hh (fun i hi =>
    he' i (A.region_sub key _ r d (((A.active r).edges _).grow _ hr hi)))
  have eq := he' (key d) (A.region_sub key _ r d (((A.active r).edges _).root _ _))
  exact eq ▸ (Network.local_want v a agree).mp hw

end Legs.Decoration
end OAI.Geometry.Hirsch.Layer.Board
