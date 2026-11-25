import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloTypes

/-! # Unary header to the padded five-axis validity mask in linear time -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryHalo
open IntegerMultiplication Code

/-- Singleton, fully occupied axes contribute no flags to the traversal. -/
private def trim (xs : List (ℕ × ℕ)) := xs.filter (fun p => decide (2 ≤ BoxOrder.total p))

private theorem trim_expand (xs : List (ℕ × ℕ)) (h : ∀ p ∈ xs, 0 < p.1) :
    BoxOrder.expand (trim xs) = BoxOrder.expand xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    have hp := h p List.mem_cons_self
    have hx := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨a,b⟩ := p
    by_cases hab : 2 ≤ a+b
    · simpa [trim, BoxOrder.total, hab, BoxOrder.expand] using
        congrArg (fun row : List Bool => (List.replicate a row).flatten ++ List.replicate (b*row.length) false) hx
    · have ha : a = 1 := by change 0 < a at hp; omega
      have hb : b = 0 := by omega
      subst a; subst b
      simpa [trim, BoxOrder.expand, BoxOrder.total] using hx

private def full (x : Tally) : Tally × Tally := (x,[])
private def extended (x y : Tally) : Tally × Tally := (x, (cutLists (x,y)).2)
private def axes (h : Header) : List (Tally × Tally) :=
  [full h.1, extended h.2.1 h.2.2.2.1, full h.2.2.1, extended h.2.1 h.2.2.2.1, full h.2.2.2.2]

private def keep (p : Tally × Tally) : List (Tally × Tally) :=
  bif Iter.small (tally 1, p.1 ++ p.2) then [p] else []

private def prepare (h : Header) := ((axes h).map keep).flatten

private theorem prepare_easy : Easy prepare := by
  have hfull : Easy full := by unfold full; fun_prop
  have hext : Easy (fun t : Tally × Tally => extended t.1 t.2) :=
    Easy.fst.pair (easy_cut Easy.identity).sndCompose
  have he : Easy (fun h : Header => extended h.2.1 h.2.2.2.1) :=
    (show Easy (fun h : Header => (h.2.1,h.2.2.2.1)) by fun_prop).compose hext
  have hp : Easy axes := by unfold axes; fun_prop
  have test : Easy (fun p : Tally × Tally => Iter.small (tally 1, p.1 ++ p.2)) :=
    ((Easy.const _).pair Easy.append).compose Iter.small_easy
  have hk : Easy keep := (test.pair Easy.identity).compose
    (Easy.ifst (Easy.const []) (show Easy (fun p : Tally × Tally => [p]) by fun_prop))
  exact hp.compose (hk.mapping.compose Easy.flatten)

private theorem prepare_header (s : Shape) : prepare s.header = BoxMask.header (trim s.axes) := by
  have h (xs : List (ℕ × ℕ)) : ((BoxMask.header xs).map keep).flatten = BoxMask.header (trim xs) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases h : 2 ≤ BoxOrder.total x
      · have ha : 1 < x.1+x.2 := h
        simp [BoxMask.header, trim, keep, Iter.small, BoxMask.encodeCounts, h,ha] at ih ⊢
        exact ih
      · have ha : ¬1 < x.1+x.2 := h
        simp [BoxMask.header, trim, keep, Iter.small, BoxMask.encodeCounts, h,ha] at ih ⊢
        exact ih
  have he : axes s.header = BoxMask.header s.axes := by
    simp [axes,Shape.header,Shape.axes,full,extended,BoxMask.header,BoxMask.encodeCounts,cutLists,tally]
  rw [prepare,he,h]

private theorem axis_pos {s : Shape} (g : Good s) : ∀ p ∈ s.axes, 0 < p.1 := by
  intro p hp
  simp only [Shape.axes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl <;> first | exact g.hP | exact g.hD | exact g.hG | exact g.hB

private theorem header_bound {s : Shape} (g : Good s) : size s.header ≤ 10*s.volume+9 := by
  have hi := g.hDE
  have hp : 1 ≤ s.P := g.hP
  have hg : 1 ≤ s.G := g.hG
  have hb : 1 ≤ s.B := g.hB
  have he : 1 ≤ s.E := g.hD.trans_le hi
  have bounds (x : ℕ) (h : x = s.P ∨ x = s.E ∨ x = s.G ∨ x = s.B) : x ≤ s.volume := by
    apply Nat.le_of_dvd (show 0 < s.volume by unfold Shape.volume; positivity)
    rcases h with rfl|rfl|rfl|rfl <;> unfold Shape.volume
    · exact ⟨s.E*s.G*s.E*s.B, by ac_rfl⟩
    · exact ⟨s.P*s.G*s.E*s.B, by ac_rfl⟩
    · exact ⟨s.P*s.E*s.E*s.B, by ac_rfl⟩
    · exact ⟨s.P*s.E*s.G*s.E, by ac_rfl⟩
  have p := bounds _ (.inl rfl)
  have e := bounds _ (.inr (.inl rfl))
  have g := bounds _ (.inr (.inr (.inl rfl)))
  have b := bounds _ (.inr (.inr (.inr rfl)))
  simp only [Shape.header,size_prod,size_tally,tally_length]
  omega

/-- The command is uniform in both field ranges and all three spectators.
It includes construction of the directory and every allocated mask bit. -/
theorem mask_task : Task (fun x : {s : Shape // Good s} => x.val.volume)
    (fun x => send x.val.header) (fun x => send x.val.mask) := by
  let input (x : {s : Shape // Good s}) := trim x.val.axes
  have legal (x : {s : Shape // Good s}) : ∀ p ∈ input x, 2 ≤ BoxOrder.total p := by
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  let use := BoxMask.task.on (fun x : {s : Shape // Good s} => ⟨input x, legal x⟩)
  have eq (x : {s : Shape // Good s}) : BoxOrder.expand (input x) = x.val.mask :=
    trim_expand _ (axis_pos x.property)
  have hm := use.conform (fun x => (congrArg List.length (eq x)).trans (mask_length _ x.property.hDE))
    (fun x => congrArg send (prepare_header x.val).symm) (fun x => congrArg send (eq x))
  apply ((prepare_easy.on (fun x : {s : Shape // Good s} => x.val.header)).compose hm).bound 12
  intro x
  have := header_bound x.property
  omega

end BinaryHalo

end NearSquareRoot
end Computability
end OAI
