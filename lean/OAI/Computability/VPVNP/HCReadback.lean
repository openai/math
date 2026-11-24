import OAI.Computability.VPVNP.GadgetPorts
import OAI.Computability.VPVNP.HCForward

/-!
# Reading an assignment from a spanning cycle of the exact-one graph

At a buffer, the predecessor and successor must lie on opposite sides. Two
consecutive buffers must point in the same direction: otherwise both intervening
ports would have to send edges to the same clause vertex, or both would need
incoming edges from it. Thus a single bit determines the direction of each track.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv

variable {k h c : ℕ} {occ : Fin h → Fin k × Fin c × Bool} {π : Perm (Vertex k h c)}

private theorem cannot_return (cyc : π.IsCycleOn Set.univ) (i : Fin k) {u v : Vertex k h c}
    (go : π u = v) : π v ≠ u := by
  simpa only [go] using no_two_cycle π cyc i u

private theorem allowed_predecessor (edge : ∀ v, Allowed occ v (π v)) (v : Vertex k h c) :
    Allowed occ (π.symm v) v := by simpa using edge (π.symm v)

private theorem no_two_incoming_buffers (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (i : Fin k) (j : Fin h)
    (arrive : ∀ b, π (portBuffer i j b) = .port i j b) : False := by
  have out (b : Bool) : π (.port i j b) = .clause (occ j).2.1 := by
    rcases (edge (.port i j b)).from_port with hb | ⟨hc, _⟩ | ⟨hcl, _⟩
    · exact (cannot_return cyc i (arrive b) hb).elim
    · have he := π.injective (hc.trans (arrive (!b)).symm)
      simp [portBuffer] at he
    · exact hcl
  have he := π.injective ((out false).trans (out true).symm)
  simp at he

private theorem no_two_outgoing_buffers (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (i : Fin k) (j : Fin h)
    (depart : ∀ b, π (.port i j b) = portBuffer i j b) : False := by
  have src (b : Bool) : π.symm (.port i j b) = .clause (occ j).2.1 := by
    rcases (allowed_predecessor edge (.port i j b)).to_port with hb | ⟨hc, _⟩ | ⟨hcl, _⟩
    · have hback := (π.symm_apply_eq.mp hb).symm
      exact (cannot_return cyc i (depart b) hback).elim
    · have he := (π.symm_apply_eq.mp hc).trans (depart (!b))
      simp [portBuffer] at he
    · exact hcl
  have he := π.symm.injective ((src false).trans (src true).symm)
  simp at he

/-- The two edges of a cycle incident to a buffer have the direction indicated
by the variable bit. -/
private def trackDirection (π : Perm (Vertex k h c)) (i : Fin k) (j : Fin (h + 1))
    (bit : Bool) : Prop :=
  if bit then π (.buffer i j) = nextPort i j ∧ π (prevPort i j) = .buffer i j
  else π (.buffer i j) = prevPort i j ∧ π (nextPort i j) = .buffer i j

private theorem trackDirection_step (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (i : Fin k) (j : Fin h) (bit : Bool)
    (here : trackDirection π i j.castSucc bit)
    (options : trackDirection π i j.succ true ∨ trackDirection π i j.succ false) :
    trackDirection π i j.succ bit := by
  cases bit with
  | false =>
    rcases options with right | left
    · have dep : ∀ b, π (.port i j b) = portBuffer i j b := by
        intro b
        cases b
        · simpa [portBuffer] using (show _ ∧ _ from here).2
        · simpa [portBuffer] using (show _ ∧ _ from right).2
      exact (no_two_outgoing_buffers cyc edge i j dep).elim
    · exact left
  | true =>
    rcases options with right | left
    · exact right
    · have arr : ∀ b, π (portBuffer i j b) = .port i j b := by
        intro b
        cases b
        · simpa [portBuffer] using (show _ ∧ _ from here).1
        · simpa [portBuffer] using (show _ ∧ _ from left).1
      exact (no_two_incoming_buffers cyc edge i j arr).elim

private theorem trackDirections (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) :
    ∃ x : Fin k → Bool, ∀ i t, trackDirection π i t (x i) := by
  classical
  have options (i : Fin k) (t : Fin (h + 1)) :
      trackDirection π i t true ∨ trackDirection π i t false :=
    buffer_directions π cyc edge i t
  let x (i : Fin k) := decide (trackDirection π i 0 true)
  refine ⟨x, fun i t => ?_⟩
  induction t using Fin.induction with
  | zero =>
    by_cases hi : trackDirection π i 0 true
    · simp [x, hi]
    · simpa [x, hi] using (options i 0).resolve_left hi
  | succ j ih =>
    exact trackDirection_step cyc edge i j (x i) ih (options i j.succ)

private theorem aligned_port_buffers {x : Fin k → Bool}
    (align : ∀ i t, trackDirection π i t (x i)) (i : Fin k) (j : Fin h) :
    π (portBuffer i j (!x i)) = .port i j (!x i) ∧
    π (.port i j (x i)) = portBuffer i j (x i) := by
  have left := align i j.castSucc
  have right := align i j.succ
  cases hx : x i <;> simp [trackDirection, hx] at left right <;> simp [portBuffer, left, right]

private theorem aligned_endpoint_buffers {x : Fin k → Bool}
    (align : ∀ i t, trackDirection π i t (x i)) (i : Fin k) :
    π (endpointBuffer i (x i)) = .endpoint i (x i) ∧
    π (.endpoint i (!x i)) = endpointBuffer i (!x i) := by
  have left := align i 0
  have right := align i (Fin.last h)
  cases hx : x i <;> simp [trackDirection, hx] at left right <;> simp [endpointBuffer, left, right]

private theorem aligned_ingress {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (i : Fin k) (j : Fin h) :
    π (.port i j (!x i)) =
      if (occ j).1 = i ∧ (occ j).2.2 = x i then .clause (occ j).2.1 else .port i j (x i) := by
  rcases (edge (.port i j (!x i))).from_port with hb | ⟨direct, hinactive⟩ | ⟨detour, hi, hb⟩
  · exact (cannot_return cyc i (aligned_port_buffers align i j).1 hb).elim
  · have h : ¬ ((occ j).1 = i ∧ (occ j).2.2 = x i) := by
      rintro ⟨hi, hb⟩
      rcases hinactive with hn | hn
      · exact hn hi
      · simp [hb] at hn
    simpa [h] using direct
  · have h : (occ j).1 = i ∧ (occ j).2.2 = x i := ⟨hi, by simpa using (congrArg Bool.not hb).symm⟩
    simpa [h] using detour

private theorem aligned_detour_exit {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (i : Fin k) (j : Fin h) (active : (occ j).1 = i ∧ (occ j).2.2 = x i) :
    π (.clause (occ j).2.1) = .port i j (x i) := by
  rcases (allowed_predecessor edge (.port i j (x i))).to_port with hb | ⟨cross, _⟩ | ⟨detour, _⟩
  · exact (cannot_return cyc i (aligned_port_buffers align i j).2
      (π.symm_apply_eq.mp hb).symm).elim
  · have depart := aligned_ingress cyc edge align i j
    rw [ite_eq_left active] at depart
    have he := (π.symm_apply_eq.mp cross).trans depart
    cases he
  · exact (π.symm_apply_eq.mp detour).symm

private theorem aligned_track_end {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (i : Fin k) :
    π (.sep i) = .endpoint i (!x i) ∧ π (.endpoint i (x i)) = .sep (finRotate k i) := by
  obtain ⟨arrive, depart⟩ := aligned_endpoint_buffers align i
  constructor
  · rcases (allowed_predecessor edge (.endpoint i (!x i))).to_endpoint with hb | hs
    · exact (cannot_return cyc i depart (π.symm_apply_eq.mp hb).symm).elim
    · exact (π.symm_apply_eq.mp hs).symm
  · exact (edge (.endpoint i (x i))).from_endpoint.resolve_left (cannot_return cyc i arrive)

private theorem aligned_exact {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i)) :
    Exact occ x := by
  intro a
  obtain ⟨j, hcl, hpred⟩ := allowed_to_clause_iff.mp (allowed_predecessor edge (.clause a))
  have toClause := (π.symm_apply_eq.mp hpred).symm
  have active : x (occ j).1 = (occ j).2.2 := by
    by_contra h
    have he : (!(occ j).2.2) = x (occ j).1 := by
      cases ha : (occ j).2.2 <;> cases hx : x (occ j).1 <;> simp_all
    rw [he, (aligned_port_buffers align (occ j).1 j).2] at toClause
    cases toClause
  refine ⟨j, ⟨hcl, active⟩, ?_⟩
  rintro s ⟨hs, hv⟩
  have from_s := aligned_ingress cyc edge align (occ s).1 s
  rw [ite_eq_left ⟨rfl, hv.symm⟩, hs] at from_s
  have he := π.injective (from_s.trans toClause.symm)
  exact (Vertex.port.inj he).2.1

private theorem read_aligned_cycle {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (exactly : Exact occ x) (v : Vertex k h c) : π v = nextVertex occ x exactly v := by
  cases v with
  | sep i => exact (aligned_track_end cyc edge align i).1
  | endpoint i b =>
    by_cases hb : b = x i
    · subst b
      simpa [nextVertex] using (aligned_track_end cyc edge align i).2
    · have he : b = !(x i) := by cases b <;> cases hx : x i <;> simp_all
      rw [nextVertex, ite_eq_right hb, he]
      exact (aligned_endpoint_buffers align i).2
  | buffer i j =>
    have atBuffer := align i j
    cases hi : x i <;> simp [trackDirection, hi] at atBuffer <;> simp [nextVertex, hi, atBuffer]
  | port i j b =>
    by_cases hb : b = x i
    · subst b
      simpa [nextVertex] using (aligned_port_buffers align i j).2
    · have he : b = !(x i) := by cases b <;> cases hx : x i <;> simp_all
      rw [he, nextVertex_ingress]
      exact aligned_ingress cyc edge align i j
  | clause a =>
    let j := chosen occ x exactly a
    obtain ⟨hcl, hv⟩ := chosen_spec occ x exactly a
    have he := aligned_detour_exit cyc edge align (occ j).1 j ⟨rfl, hv.symm⟩
    change π (.clause a) = .port (occ j).1 j (occ j).2.2
    simpa only [j, hcl, hv] using he

/-- Every allowed spanning cycle is precisely the traversal constructed from
an assignment satisfying every exact-one constraint. -/
theorem exists_exact_assignment (cyc : π.IsCycleOn Set.univ) (edge : ∀ v, Allowed occ v (π v)) :
    ∃ (x : Fin k → Bool) (hx : Exact occ x), π = cycleOfAssignment occ x hx := by
  obtain ⟨x, align⟩ := trackDirections cyc edge
  let hx := aligned_exact cyc edge align
  exact ⟨x, hx, Equiv.ext (read_aligned_cycle cyc edge align hx)⟩

/-- The outgoing arc at each separator recovers its track bit, so distinct
satisfying assignments give distinct tours. -/
theorem cycleOfAssignment_injective (occ : Fin h → Fin k × Fin c × Bool) :
    Function.Injective (fun x : {x : Fin k → Bool // Exact occ x} =>
      cycleOfAssignment occ x.val x.property) := by
  intro x y he
  apply Subtype.ext
  funext i
  have e := Equiv.congr_fun he (.sep i)
  have hb := (Vertex.endpoint.inj (show Vertex.endpoint (h := h) (c := c) i (!(x.val i)) =
    .endpoint i (!(y.val i)) from e)).2
  simpa using congrArg Bool.not hb

end HCGadget

end VPVNP
end Computability
end OAI
