import OAI.Computability.BorderVNP.ShortenAddressCost
import OAI.Computability.BorderVNP.CrossingProfileSize

/-!
# Width entering a tile after sewing the selected profile

The sum below is over actual physical edges of the replacement pack. Each
selected interval contributes two endpoint hooks, each seed contributes its
finite profile network, and each unselected interval is retained just once.
Thus the weighted output count in a tile is bounded by the input count in
its neighboring donor addresses times a constant fixed before the pack
size, widths or histogram choices are given.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Finset
open scoped Classical

variable {D m : ℕ} {P : Type*} {bits : P → ℕ} {K : Type*} [Field K]
variable {A : Type} [Fintype A]

/-- Total hook and internal-profile width created per matched block, uniformly
over every attainable histogram of every size. -/
noncomputable def profileWidthBound (e : PaidIdentity K D m) : ℕ :=
  2*D*m + Fintype.card (Fin D × Bool) * Nat.clog 2 e.count +
    (∑ _ : Fin D × Bool, m) + ∑ a, ∑ x, (e.net a).width x

omit [Fintype A] in
/-- Hook widths and actual profile-internal widths at one seed are at most the
matched block count times the fixed width bound. -/
theorem seed_width_le (e : PaidIdentity K D m) (j : A → ℕ) {p : Pack D P bits K}
    (t : AddressPartition p.layout A) (b : ∀ a, Bundle p.layout (t.part a) (j a*m))
    (q : ProfileCounts e j) (a : A) :
    (∑ k, p.layout.cutWidths (t.part a) k) +
      (∑ x, (seedNetwork e j t b q a).width x) ≤ profileWidthBound e * j a := by
  have hhook : (∑ k, p.layout.cutWidths (t.part a) k) = 2 * D * (j a*m) := by
    exact_mod_cast (b a).hookWidth
  have hsum := profileCounts_total e j q a
  have terminal_ball (port : Fin D × Bool) : ‖antipodalPosition port‖ ≤ 1 := by
    rcases port with ⟨i,v⟩; cases v <;> simp [antipodalPosition]
  have hnet := Profile.totalWidth e.net antipodalPosition terminal_ball (j a) (q a).val hsum
  have hfactor (i : Fin e.count) : (q a).val i ≤ j a :=
    (single_le_sum (f := (q a).val) (fun k _ => Nat.zero_le _) (mem_univ i)).trans_eq hsum
  have hbound : (∑ i, (q a).val i * ∑ x, (e.net i).width x) ≤
      j a * (∑ i, ∑ x, (e.net i).width x) := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hfactor i)
  change _ + (∑ x, (Profile.network e.net antipodalPosition terminal_ball (j a) (q a).val).width x) ≤ _
  rw [hhook,hnet]
  unfold profileWidthBound
  linarith only [hbound]

/-- Width of edges selected by a test, such as positive-length charged
midpoint incidences in one output tile. -/
noncomputable def testedWidth {E : Type*} [Fintype E] (width : E → ℕ) (test : E → Prop) : ℕ :=
  ∑ e, if test e then width e else 0

/-- Width of active old intervals at each actual address. -/
noncomputable def addressWidth {E : Type*} [Fintype E] (width : E → ℕ)
    (active : E → Prop) (addr : E → A) (a : A) : ℕ :=
  testedWidth width (fun x => active x ∧ addr x = a)

omit [Fintype A] in
private theorem testedWidth_near {E : Type*} [Fintype E] (width : E → ℕ) (active : E → Prop)
    (addr : E → A) (near : Finset A) :
    testedWidth width (fun e => active e ∧ addr e ∈ near) =
      ∑ a ∈ near, addressWidth width active addr a := by
  unfold addressWidth testedWidth
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases he : active e <;> simp [he]

variable (e : PaidIdentity K D m) (j : A → ℕ) {p : Pack D P bits K}
  (t : AddressPartition p.layout A) (b : ∀ a, Bundle p.layout (t.part a) (j a*m))
  (q : ProfileCounts e j)

/-- The concrete sewn output layout of a joint histogram choice. -/
noncomputable abbrev sewnProfile := (p.layout.cut t.selected).sew (t.parallel (seedNetwork e j t b q))

/-- Each old retained cable and each new charged hook or profile edge is
charged to a nearby donor address. In particular a single occupied bin with
a large bundle is counted at its full width. -/
theorem sewnProfile_width_le
    (active : p.layout.Edge → Prop) (addr : p.layout.Edge → A) (donor : Equiv.Perm A)
    (near : Finset A) (post : (sewnProfile e j t b q).Edge → Prop)
    (hretain : ∀ x : {x : p.layout.Edge // x ∉ t.selected}, post (.inr (.inl x)) →
      active x.val ∧ addr x.val ∈ near)
    (hhook : ∀ a k, post (.inl (t.includePort a k)) → donor a ∈ near)
    (hnew : ∀ a x, post (.inr (.inr ⟨a,x⟩)) → donor a ∈ near)
    (hwidth : ∀ a, j a ≤ addressWidth p.layout.width active addr (donor a)) :
    testedWidth (sewnProfile e j t b q).width post ≤
      (1 + profileWidthBound e) * ∑ a ∈ near, addressWidth p.layout.width active addr a := by
  classical
  let count := addressWidth p.layout.width active addr
  let nets := seedNetwork e j t b q
  let keep (x : {x : p.layout.Edge // x ∉ t.selected}) :=
    if post (.inr (.inl x)) then p.layout.width x.val else 0
  let hook (k : p.layout.CutPorts t.selected) :=
    if post (.inl k) then p.layout.cutWidths t.selected k else 0
  let new (a : A) (x : (nets a).Edge) :=
    if post (.inr (.inr ⟨a,x⟩)) then (nets a).width x else 0
  have hdecomp : testedWidth (sewnProfile e j t b q).width post =
      (∑ x, keep x) + ∑ a, ((∑ k, hook (t.includePort a k)) + ∑ x, new a x) := by
    change (∑ x : p.layout.CutPorts t.selected ⊕
      ({x : p.layout.Edge // x ∉ t.selected} ⊕ (Σ a, (nets a).Edge)),
      if post x then (sewnProfile e j t b q).width x else 0) = _
    rw [Fintype.sum_sum_type]
    change (∑ k, hook k) + (∑ x : {x : p.layout.Edge // x ∉ t.selected} ⊕ (Σ a, (nets a).Edge),
      if post (.inr x) then (sewnProfile e j t b q).width (.inr x) else 0) = _
    rw [Fintype.sum_sum_type (fun x : {x : p.layout.Edge // x ∉ t.selected} ⊕ (Σ a, (nets a).Edge) =>
      if post (.inr x) then (sewnProfile e j t b q).width (.inr x) else 0)]
    change (∑ k, hook k) + ((∑ x, keep x) + ∑ x : Σ a, (nets a).Edge, new x.1 x.2) = _
    rw [← Equiv.sum_comp t.portIndex hook, Fintype.sum_sigma, Fintype.sum_sigma, sum_add_distrib]
    change (∑ a, ∑ k, hook (t.includePort a k)) + ((∑ x, keep x) + ∑ a, ∑ x, new a x) = _
    omega
  have hkeep : (∑ x, keep x) ≤ ∑ a ∈ near, count a := by
    let f (x : p.layout.Edge) := if active x ∧ addr x ∈ near then p.layout.width x else 0
    have hp (x : {x : p.layout.Edge // x ∉ t.selected}) : keep x ≤ f x.val := by
      dsimp [keep, f]
      by_cases h : post (.inr (.inl x))
      · simp [h,hretain x h]
      · simp [h]
    calc
      _ ≤ ∑ x : {x : p.layout.Edge // x ∉ t.selected}, f x.val := sum_le_sum fun x _ => hp x
      _ ≤ ∑ x, f x := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun x => x ∉ t.selected) f]
        exact Nat.le_add_right _ _
      _ = ∑ a ∈ near, count a := by
        rw [← testedWidth_near p.layout.width active addr near]
        apply sum_congr rfl
        intro x _
        by_cases hx : active x ∧ addr x ∈ near <;> simp [f,hx]
  have hparts (a : A) :
      (∑ k, hook (t.includePort a k)) + (∑ x, new a x) ≤
        if donor a ∈ near then profileWidthBound e * count (donor a) else 0 := by
    by_cases hn : donor a ∈ near
    · rw [ite_eq_left hn]
      apply le_trans _ (le_trans (seed_width_le e j t b q a) (Nat.mul_le_mul_left _ (hwidth a)))
      apply Nat.add_le_add
      · apply sum_le_sum
        intro k _
        have hk : p.layout.cutWidths t.selected (t.includePort a k) = p.layout.cutWidths (t.part a) k :=
          by cases k <;> rfl
        dsimp only [hook]
        rw [hk]
        split_ifs <;> omega
      · apply sum_le_sum
        intro x _
        change (if post (.inr (.inr ⟨a,x⟩)) then (nets a).width x else 0) ≤ (nets a).width x
        split_ifs <;> omega
    · have hh (k) : ¬post (.inl (t.includePort a k)) := fun h => hn (hhook a k h)
      have hN (x : (nets a).Edge) : ¬post (.inr (.inr ⟨a,x⟩)) := fun h => hn (hnew a x h)
      simp [hn,hook,new,hh,hN]
  have hsum := sum_le_sum (s := univ) fun a _ => hparts a
  have hdonor : (∑ a, if donor a ∈ near then profileWidthBound e * count (donor a) else 0) =
      profileWidthBound e * ∑ a ∈ near, count a := by
    rw [Equiv.sum_comp donor (fun a => if a ∈ near then profileWidthBound e * count a else 0)]
    rw [← sum_filter, Finset.filter_mem_eq_inter, univ_inter, mul_sum]
  rw [hdecomp, add_mul, one_mul]
  exact Nat.add_le_add hkeep (hsum.trans_eq hdonor)

end Shortening

end BorderVNP
end Computability
end OAI
