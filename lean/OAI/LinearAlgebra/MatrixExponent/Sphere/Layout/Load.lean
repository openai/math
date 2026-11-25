import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing

/-! # Arity charges for tree routing -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical

variable {F V I : Type} {a b : Wire} {d : ℕ} (G : Bundled F a b)

/-- The total width from one station to another, in both orientations. -/
def Bundled.ties (u v : G.V) :=
  (∑ e, if G.src e = u ∧ G.dst e = v then G.width e else 0) +
    (∑ e, if G.dst e = u ∧ G.src e = v then G.width e else 0)

theorem Bundled.ties_le (u v : G.V) : G.ties u v ≤ G.arity v := by
  unfold ties arity
  rw [add_comm (∑ e, if G.src e = u ∧ G.dst e = v then G.width e else 0)]
  apply Nat.add_le_add
  · apply le_trans _ (Nat.le_add_left _ _)
    exact sum_le_sum (fun e _ => by split_ifs <;> simp_all)
  · exact sum_le_sum (fun e _ => by split_ifs <;> simp_all)

namespace Fanout
variable {G} {T : Trie V d} (H : Fanout G T I)

private theorem side_count (u v : G.V) (s : Relay G.V d) (w : ℕ) :
    (∑ j, if H.side u v j = s then w else 0) =
      if H.side u v s.2.1 = s then w else 0 := by
  apply Fintype.sum_eq_single s.2.1
  intro j hj
  exact ite_eq_right (fun h => hj (congrArg (fun x => x.2.1) h))

private theorem hits (s : Relay G.V d) :
    H.route.hits (.inr s) =
      (∑ e, if H.side (G.src e) (G.dst e) s.2.1 = s then G.width e else 0) +
      (∑ e, if H.side (G.dst e) (G.src e) s.2.1 = s then G.width e else 0) := by
  unfold Routes.hits
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  simp only [Sum.inr.injEq]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hr := Equiv.sum_comp Fin.revPerm
    (fun j => if H.side (G.dst e) (G.src e) j = s then G.width e else 0)
  simp only [Fin.revPerm_apply] at hr
  rw [hr, side_count, side_count]

theorem total [Field F] : ∑ s, H.route.net.arity (.inr s) = 4 * (d + 1)*∑ e, G.width e := by
  rw [Routes.total_relay]
  change 2 * (∑ e, ((d + 1) + (d + 1)) * G.width e) = _
  rw [← mul_sum]
  ring

private theorem sides_le (s : Relay G.V d) (L R : G.E → G.V) (p : G.E → Prop)
    [DecidablePred p] (h : ∀ e, H.side (L e) (R e) s.2.1 = s → p e) :
    (∑ e, if H.side (L e) (R e) s.2.1 = s then G.width e else 0) ≤
      ∑ e, if p e then G.width e else 0 := by
  apply sum_le_sum
  intro e _
  by_cases he : H.side (L e) (R e) s.2.1 = s
  · rw [ite_eq_left he, ite_eq_left (h e he)]
  · rw [ite_eq_right he]; exact Nat.zero_le _

theorem relay_le [Field F] (s : Relay G.V d) :
    H.route.net.arity (.inr s) ≤ 2 * G.arity s.1 := by
  rw [Routes.relay_arity, hits, Bundled.arity]
  have bound (L R : G.E → G.V) := H.sides_le s L R (fun e => L e = s.1)
    (fun _ he => congrArg Prod.fst he)
  have h := bound G.src G.dst
  have i := bound G.dst G.src
  omega

/-- On a frozen branch the address identifies one opposite station. -/
theorem frozen_relay [Field F] (s : Relay G.V d) (hf : T.frozen (H.site s.1).1) :
    ∃ v, H.route.net.arity (.inr s) ≤ 2 * G.ties s.1 v := by
  let p := (T.peer (H.site s.1).1 s.2.2, (H.site s.1).2)
  let v := if h : ∃ v, H.site v = p then h.choose else s.1
  have unique (u w : G.V) (h : H.side u w s.2.1 = s)
      (hn : (H.site w).1 ∈ T.near (H.site u).1) (hg : (H.site u).2 = (H.site w).2) :
      u = s.1 ∧ w = v := by
    have hu : u = s.1 := congrArg Prod.fst h
    subst u
    have he := congrArg (fun x => x.2.2) h
    simp only [side, Trie.address, ite_eq_left hf] at he
    have hw : H.site w = p := Prod.ext (by unfold p; rw [← he, T.peer_code hn]) hg.symm
    have hx : ∃ v, H.site v = p := ⟨w, hw⟩
    exact ⟨rfl, by unfold v; rw [dite_eq_left hx]; exact H.one (hw.trans hx.choose_spec.symm)⟩
  refine ⟨v, ?_⟩
  rw [Routes.relay_arity, hits, Bundled.ties]
  have hl := H.sides_le s G.src G.dst (fun e => G.src e = s.1 ∧ G.dst e = v)
    (fun e he => unique _ _ he (H.near e) (H.group e))
  have hr := H.sides_le s G.dst G.src (fun e => G.dst e = s.1 ∧ G.src e = v)
    (fun e he => unique _ _ he (T.symm _ _ (H.near e)) (H.group e).symm)
  omega

end Fanout
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
