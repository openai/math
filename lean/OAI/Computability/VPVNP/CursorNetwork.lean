import OAI.Computability.VPVNP.CursorRouting
import OAI.Computability.VPVNP.NetworkKernel
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Local vertex factors of the cursor network

Section 12 gives each mask system a field on each of the two outgoing arcs.
At a nonzero cursor its local factor tests the routing equalities. At cursor
zero it also evaluates the site's validator on the selected outgoing and
returning fields. These factors accept arbitrary independent half-wire
indices, as required by the substitutions in (12.2).
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting NetworkKernel

/-- A cursor position, consisting of the current mask-bit index and the site occupied at that
index. -/
abbrev Position (D : ℕ) := Fin D × Site D
/-- A directed cursor arc indexed by the current bit position, sending site, and decision to
flip that bit. -/
abbrev Arc (D : ℕ) := Fin D × Site D × Bool
/-- One Boolean word of the prescribed width for each system sharing a cursor arc. -/
abbrev Payload {S : Type} (bits : S → ℕ) := (s : S) → Fin (bits s) → Bool

variable {D : ℕ} {S : Type} [Fintype S] [NeZero D]

/-- The head of an arc after advancing the cursor and applying its bit choice. -/
def head (e : Arc D) : Position D := (finRotate D e.1, stepSite e.1 e.2.2 e.2.1)

omit [NeZero D] in
private theorem step_involutive (j : Fin D) (side : Bool) (x : Site D) :
    stepSite j side (stepSite j side x) = x := by
  cases side with
  | false => rfl
  | true => exact Fin.ext (by simp [stepSite_true_val])

open scoped Classical in
/-- The two arcs at a position are indexed by their sender and choice. -/
noncomputable def network (D : ℕ) (bits : S → ℕ) : Network where
  Site := Position D
  Edge := Arc D
  src e := (e.1, e.2.1)
  dst := head
  Payload _ := Payload bits
  siteFintype := inferInstance
  edgeFintype := inferInstance
  payloadFintype _ := inferInstance

/-- Source of the unique incoming arc with the prescribed choice. -/
def incomingArc (v : Position D) (side : Bool) : Arc D :=
  let prev := (finRotate D).symm v.1
  (prev, stepSite prev side v.2, side)

@[simp] theorem head_incomingArc (v : Position D) (side : Bool) :
    head (incomingArc v side) = v := by simp [head, incomingArc, step_involutive]

@[simp] theorem incomingArc_head (e : Arc D) :
    incomingArc (head e) e.2.2 = e := by simp [head, incomingArc, step_involutive]

variable {bits : S → ℕ}

/-- A site's half-wire arguments can be read using local outgoing and incoming
slot numbers, without consulting any other site's arguments. -/
def out (v : Position D) (z : (network D bits).Half v) (side : Bool) : Payload bits :=
  z.1 (v.1, v.2, side) rfl

/-- Incoming payload at a cursor position from the arc with the specified flip decision. -/
def inc (v : Position D) (z : (network D bits).Half v) (side : Bool) : Payload bits :=
  z.2 (incomingArc v side) (head_incomingArc v side).symm

/-- Assemble each system's sent payload from the outgoing arc selected by its current mask bit. -/
def sent (mask : S → Site D) (v : Position D) (z : (network D bits).Half v) : Payload bits :=
  fun s ↦ out v z ((mask s).val.testBit v.1.val) s

/-- Assemble each system's received payload from the incoming arc selected by its mask bit at
the preceding cursor position. -/
def received (mask : S → Site D) (v : Position D) (z : (network D bits).Half v) : Payload bits :=
  fun s ↦ inc v z ((mask s).val.testBit ((finRotate D).symm v.1).val) s

/-- Clamp every unused outgoing field, and at each nonzero cursor tie the
selected incoming and outgoing fields bitwise. -/
def Checks (mask : S → Site D) (v : Position D) (z : (network D bits).Half v) : Prop :=
  (∀ s side, side ≠ (mask s).val.testBit v.1.val → out v z side s = fun _ ↦ false) ∧
  (v.1 ≠ 0 → sent mask v z = received mask v z)

variable {k : Type*} [CommSemiring k]

open scoped Classical in
/-- The uncompressed tensor factors, one per position. The validator takes
the selected send vector followed by the selected receive vector. -/
noncomputable def factors (mask : S → Site D)
    (validator : Site D → Payload bits → Payload bits → k) : Factors k (network D bits) :=
  fun v z ↦ if Checks mask v z then
    if v.1 = 0 then validator v.2 (sent mask v z) (received mask v z) else 1
  else 0

private noncomputable abbrev shared (z : Arc D → Payload bits) (v : Position D) :=
  WireTensor.edgeAssignment (network D bits).src (network D bits).dst z v

private abbrev field (z : Arc D → Payload bits) (s : S) : ArcFields D (Fin (bits s) → Bool) :=
  fun j x b ↦ z (j, x, b) s

/-- The last cursor is the incoming cursor of every site validator. -/
private theorem rotate_of_step {i j : Fin D} (h : j.val = i.val + 1) : finRotate D i = j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne D)
  apply Fin.ext
  have hn : i ≠ Fin.last n := by
    rintro rfl
    have := j.isLt
    simp only [Fin.val_last] at h
    omega
  exact (coe_finRotate_of_ne_last hn).trans h.symm

private theorem rotate_of_last {i : Fin D} (h : i.val + 1 = D) : finRotate D i = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne D)
  have hi : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
  exact hi ▸ finRotate_last

private theorem prev_zero : ((finRotate D).symm 0).val + 1 = D := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne D)
  have he : (finRotate (n+1)).symm 0 = Fin.last n :=
    (finRotate (n+1)).symm_apply_eq.mpr finRotate_last.symm
  rw [he, Fin.val_last]

private theorem received_head (mask : S → Site D) (z : Arc D → Payload bits)
    (j : Fin D) (x : Site D) (s : S) :
    let b := (mask s).val.testBit j.val
    received mask (head (j,x,b)) (shared z _) s = z (j,x,b) s := by
  dsimp only
  simp only [received, head, Equiv.symm_apply_apply]
  change z (incomingArc (head (j, x, (mask s).val.testBit j.val)) _) s = _
  rw [incomingArc_head]

private noncomputable abbrev sends (mask : S → Site D) (z : Arc D → Payload bits) (x : Site D) :=
  sent mask (0,x) (shared z _)

private noncomputable abbrev receives (mask : S → Site D) (z : Arc D → Payload bits) (x : Site D) :=
  received mask (0,x) (shared z _)

private theorem ties_of_checks (mask : S → Site D) (z : Arc D → Payload bits)
    (h : ∀ v, Checks mask v (shared z v)) (s : S) :
    LocalTies (fun _ ↦ false) (mask s) (fun x ↦ sends mask z x s)
      (fun x ↦ receives mask z x s) (field z s) := by
  constructor
  · exact fun j x b hb ↦ (h (j,x)).1 s b hb
  · intro x; rfl
  · intro j l hj x
    let b := (mask s).val.testBit j.val
    let v := head (j,x,b)
    have hv : v.1 = l := rotate_of_step hj
    have hn : v.1 ≠ 0 := by rw [hv]; intro he; rw [he, Fin.val_zero] at hj; omega
    have he := congrFun ((h v).2 hn) s
    rw [received_head] at he
    change z (finRotate D j, stepSite j b x, (mask s).val.testBit (finRotate D j).val) s = _ at he
    change finRotate D j = l at hv
    rw [hv] at he
    exact he
  · intro j hj x
    have he := received_head mask z j x s
    change receives mask z _ s = _
    have hv : head (j,x,(mask s).val.testBit j.val) =
        (0,stepSite j ((mask s).val.testBit j.val) x) := Prod.ext (rotate_of_last hj) rfl
    dsimp only at he
    rw [hv] at he
    exact he

private theorem prev_succ {j : Fin D} (h : j ≠ 0) :
    j.val = ((finRotate D).symm j).val + 1 := by
  rw [coe_finRotate_symm_of_ne_zero h]
  have := Fin.val_ne_zero_iff.mpr h
  omega

private theorem checks_of_ties (mask : S → Site D) (z : Arc D → Payload bits)
    (a b : Site D → Payload bits)
    (h : ∀ s, LocalTies (fun _ ↦ false) (mask s) (fun x ↦ a x s) (fun x ↦ b x s)
      (field z s)) (v : Position D) : Checks mask v (shared z v) := by
  refine ⟨fun s side hs ↦ (h s).clamp v.1 v.2 side hs, ?_⟩
  intro hn
  funext s
  let j := (finRotate D).symm v.1
  let side := (mask s).val.testBit j.val
  let x := stepSite j side v.2
  have he := (h s).transit j v.1 (prev_succ hn) x
  change field z s v.1 v.2 ((mask s).val.testBit v.1.val) = field z s j x side
  simpa only [x, side, step_involutive] using he

/-- Returns at cursor zero pull the corresponding send back through the full
xor permutation for each individual mask. -/
def returned (mask : S → Site D) (a : Site D → Payload bits) (x : Site D) : Payload bits :=
  fun s ↦ a ((routePos (mask s) D).symm x) s

private def fieldEquiv (D : ℕ) (bits : S → ℕ) :
    (Arc D → Payload bits) ≃ ((s : S) → ArcFields D (Fin (bits s) → Bool)) where
  toFun := field
  invFun f e s := f s e.1 e.2.1 e.2.2
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 1200000 in
-- Reindexing the dependent system and half-wire products elaborates their finite instances.
/-- Contracting the actual two-arc graph gives one term per source setting.
All intermediate equalities and clamps are evaluated on their own half-wires. -/
theorem contract_eq (mask : S → Site D)
    (validator : Site D → Payload bits → Payload bits → k) :
    open scoped Classical in
    contract (network D bits) (factors mask validator) =
      ∑ a : Site D → Payload bits, ∏ x, validator x (a x) (returned mask a x) := by
  classical
  let wt (a : Site D → Payload bits) := ∏ x, validator x (a x) (returned mask a x)
  let send (a : Site D → Payload bits) := fun s x ↦ a x s
  let recv (a : Site D → Payload bits) := fun s x ↦ returned mask a x s
  have hinj : Function.Injective send := by
    intro a b h
    funext x s
    exact congrFun (congrFun h s) x
  have hmatch (a : Site D → Payload bits) (s : S) (x : Site D) :
      recv a s (routePos (mask s) D x) = send a s x := by simp [recv, returned, send]
  rw [← routed_contraction_eq (fun _ _ ↦ false) mask send recv hinj hmatch wt, contract_edgeSum]
  unfold routedContraction
  let N := network D bits
  let inst : Fintype (Arc D → Payload bits) :=
    @Pi.instFintype N.Edge N.Payload (fun x y ↦ Classical.propDecidable (x = y))
      N.edgeFintype N.payloadFintype
  refine Fintype.sum_equiv (M := k) (fieldEquiv D bits) _ _ fun z ↦ ?_
  let T (a : Site D → Payload bits) := ∀ s, LocalTies (fun _ ↦ false) (mask s)
    (send a s) (recv a s) (field z s)
  change (∏ v : Position D, factors mask validator v (shared z v)) =
    @dite k (∃ a, T a) (Classical.propDecidable _) (fun h ↦ wt h.choose) (fun _ ↦ 0)
  simp only [factors, Fintype.prod_ite_zero]
  by_cases h : ∃ a, T a
  · let a := h.choose
    have ha : T a := h.choose_spec
    rw [ite_eq_left (checks_of_ties mask z a (returned mask a) ha), dite_eq_left h,
      Fintype.prod_prod_type]
    change (∏ j : Fin D, ∏ x : Site D, if j = 0 then _ else 1) = wt a
    simp_rw [← Finset.ite_prod_one]
    rw [Fintype.prod_ite_eq']
    apply Finset.prod_congr rfl
    intro x _
    have hs : sends mask z x = a x := funext fun s ↦ (ha s).start x
    have hr : receives mask z x = returned mask a x := by
      funext s
      let j := (finRotate D).symm 0
      have hj : j.val + 1 = D := prev_zero
      let b := (mask s).val.testBit j.val
      have he := (ha s).arrival j hj (stepSite j b x)
      change field z s j (stepSite j b x) b = recv a s x
      simpa only [b, step_involutive] using he.symm
    exact congrArg₂ (validator x) hs hr
  · rw [dite_eq_right h, ite_eq_right]
    intro hc
    let a := sends mask z
    have ht := ties_of_checks mask z hc
    have hr (s : S) (x : Site D) : receives mask z x s = recv a s x := by
      have he := (ht s).receive_at ((routePos (mask s) D).symm x)
      simpa [a, recv, returned] using he
    apply h
    exact ⟨a, fun s ↦ (funext (hr s)) ▸ ht s⟩

end CursorNetwork

end VPVNP
end Computability
end OAI
