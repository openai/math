import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
import Mathlib.Data.Finset.Image
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Window
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select

/-!
# One selector per occurrence

Active cells select a local branch by its ordinal. The unused
positions have one valid word, zero, so they do not multiply the
contraction in small characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Selector
open Finset
open scoped Classical
variable {V J : Type} {L : ℕ} [NeZero L] (addr : J ↪ V)
  (S : J → Type) [∀ j, Fintype (S j)] (fits : ∀ j, Fintype.card (S j) ≤ L)

def scatter (x : ∀ j, S j) : V → Fin L :=
  Function.extend addr (fun j => Fin.castLE (fits j) (Fintype.equivFin _ (x j))) (fun _ => 0)

theorem scatter_at (x : ∀ j, S j) (j : J) :
    (scatter addr S fits x (addr j)).val = (Fintype.equivFin (S j) (x j)).val := by
  rw [scatter, addr.injective.extend_apply]
  rfl

theorem scatter_away (x : ∀ j, S j) (v : V) (h : v ∉ Set.range addr) :
    scatter addr S fits x v = 0 := Function.extend_apply' _ _ _ h

def scattered : Selector (∀ j, S j) (V → Fin L) where
  write := scatter addr S fits
  read t := if h : ∃ x, t = scatter addr S fits x then some h.choose else none
  valid t x := by
    split_ifs with h
    · constructor
      · intro he; rw [← Option.some.inj he]; exact h.choose_spec
      · intro he
        congr 1
        funext j
        apply (Fintype.equivFin _).injective
        apply Fin.ext
        rw [← scatter_at addr S fits, ← scatter_at addr S fits, ← h.choose_spec, ← he]
    · exact iff_of_false (by simp) (fun e => h ⟨x, e⟩)

theorem scattered_present (t : V → Fin L) (on : ∀ j, (t (addr j)).val < Fintype.card (S j))
    (off : ∀ v ∉ Set.range addr, t v = 0) : ∃ x, t = scatter addr S fits x := by
  let x j := (Fintype.equivFin (S j)).symm ⟨_, on j⟩
  refine ⟨x, funext fun v => ?_⟩
  by_cases h : v ∈ Set.range addr
  · obtain ⟨j, rfl⟩ := h
    apply Fin.ext
    rw [scatter_at]
    exact (congrArg Fin.val ((Fintype.equivFin (S j)).apply_symm_apply ⟨_, on j⟩)).symm
  · rw [off v h, scatter_away _ _ _ _ _ h]

variable [Fintype V] [Fintype J] {F : Type} [CommMonoidWithZero F]

theorem scattered_weight (t : V → Fin L) (weight : (j : J) → S j → F) (w : V → F)
    (on : ∀ j, w (addr j) = if h : (t (addr j)).val < Fintype.card (S j)
        then weight j ((Fintype.equivFin _).symm ⟨_, h⟩) else 0)
    (off : ∀ v ∉ Set.range addr, w v = if t v = 0 then 1 else 0) :
    (∏ v, w v) = ((scattered addr S fits).read t).elim 0 (fun x => ∏ j, weight j (x j)) := by
  cases h : (scattered addr S fits).read t with
  | none =>
    by_contra! hn
    have live (v : V) : w v ≠ 0 := fun e => hn (prod_eq_zero (mem_univ v) e)
    obtain ⟨x, hx⟩ := scattered_present addr S fits t
      (fun j => by by_contra! hn; exact live (addr j) (by rw [on, dite_eq_right (not_lt.mpr hn)]))
      (fun v hv => by by_contra! hn; exact live v (by rw [off v hv, ite_eq_right hn]))
    rw [((scattered addr S fits).valid t x).mpr hx] at h
    contradiction
  | some x =>
    have he : t = scatter addr S fits x := ((scattered addr S fits).valid _ _).mp h
    let active := univ.image addr
    have hw : (∏ v ∈ active, w v) = ∏ v, w v := prod_subset (subset_univ _) (by
      intro v _ hv
      have hi : v ∉ Set.range addr := by simpa [active] using hv
      rw [off v hi, he, scatter_away _ _ _ _ _ hi, ite_eq_left rfl])
    rw [← hw, show active = univ.image addr from rfl, prod_image addr.injective.injOn]
    apply prod_congr rfl
    intro j _
    simp only [on, he, scatter_at, Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Transcript.Selector
end

/-!
# A local weighted lookup at the initiator

The lookup receives records indexed by a fixed neighborhood walk.
The origin is always entry zero. Repeated addresses are erased before
reconstructing the intrinsic panel.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Coloring
open scoped Classical

variable {F V E T X J L N : Type} [Field F] [Fintype F]
  {r t m d h U R Q M g H D : ℕ} (p l : ℕ) [ExpChar F p]
  (hF : M * (2 * D + 1) < Fintype.card F) (j : Fin (R * M))

local notation "Meta" => Metadata F r t R Q U M N
local notation "Msg" => Reply F r t R (Stamp Q (R * M) U) N

def selected (u : Meta) := u.map Prod.fst = some (finProdFinEquiv.symm j).1

def send (g H : ℕ) (s : B ((d + 1) * U) → Meta) (i : ℕ) : Option Msg :=
  match s 0 with
  | none => none
  | some (v, k, pos, _) =>
    if v = (finProdFinEquiv.symm j).1 then
      (visible s).get p l g H M D hF v (pos (finProdFinEquiv.symm j).2)
        (fun i : Fin (U + 1) => created (fun _ : Unit => k) j () i.val) i
    else none

theorem send_off (s : B ((d + 1) * U) → Meta) (i : ℕ) (e : ¬selected j (s 0)) :
    send p l hF j g H s i = none := by
  unfold send selected at *
  cases e' : s 0 with
  | none => rfl
  | some y =>
    obtain ⟨v, k, pos, w⟩ := y
    simp only [e', Option.map_some, Option.some.injEq] at e
    simp only [ite_eq_right e]

def charge (g H : ℕ) (s : B ((d + 1) * U) → Meta) (i : ℕ) : F :=
  if selected j (s 0) then (send p l hF j g H s i).elim 0 Reply.weight
    else if i = 0 then 1 else 0

namespace Frame
variable [Fintype V] [Fintype E] {a : Atlas V E m d h}
  {π : Palette a (2 * U + 2) R} {ref : Reference J L N V E T X} {pos : V → Fin M → F}
  {origin : Stage F r t T V E X} (c : Palette a (horizon U (R * M) 0) Q)
  (x : Frame (π.plan pos) ref origin (p ^ l) g H Q j.val) (size : V → ℕ)

local notation "C" => commands c p l hF j x
local notation "I" => Fin (Plan.count (π.plan pos) j)
local notation "root" => Plan.root (π.plan pos) j
local notation "A" => π.records c pos x.record (info size x)

omit [Fintype F] [Fintype E] [ExpChar F p] in
theorem selected_iff (v : B m × B h) :
    selected j (A v) ↔ v ∈ Set.range ((root).trans a.coord) := by
  by_cases h : v ∈ Set.range a.coord
  · obtain ⟨w, rfl⟩ := h
    simp only [selected, Palette.records_at, Option.map_some, Option.some.injEq]
    rw [← π.mem_roots]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, congrArg a.coord hi⟩, fun ⟨i, hi⟩ => ⟨i, a.coord.injective hi⟩⟩
  · rw [Palette.records_away _ _ _ _ _ h]
    exact iff_of_false (by simp [selected]) (fun ⟨i, e⟩ => h ⟨_, e⟩)

theorem send_at (i : I) (z : ℕ) :
    send p l hF j g H (A ∘ a.around U (a.coord (root i))) z =
      if h : z < Fintype.card (C i).action.I then
        some ((panel c p l j x i).reply (C i).action ((Fintype.equivFin _).symm ⟨z, h⟩)
          (π.tiles x.record (info size x) (root i))) else none := by
  let v := root i
  have eq : π.mark v = (finProdFinEquiv.symm j).1 := (π.mem_roots _ _).mp ⟨i, rfl⟩
  unfold send
  simp only [Function.comp_apply, Atlas.around_zero, Palette.records_at, Palette.window]
  rw [ite_eq_left eq]
  let y := panel c p l j x i
  have he := (π.tiles x.record (info size x) v).get_spec p l g H M D hF y
    (π.panel_complete _ (x.match'.incident x.layout) _ _ _)
    (π.bodies _ _ _ (x.match'.incident x.layout) _ _) z
  exact he

end Frame
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Charging and broadcasting regional scripts on the fixed host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Frame
open Coloring Transcript
open scoped Classical

variable {F V E T X J L N : Type} [Field F] [Fintype F] [Fintype V] [Fintype E]
  {r t m d h U R Q M g H D k : ℕ} {a : Atlas V E m d h}
  {π : Palette a (2 * U + 2) R} {ref : Reference J L N V E T X} {pos : V → Fin M → F}
  {origin : Stage F r t T V E X} (c : Palette a (horizon U (R * M) 0) Q)
  (p l : ℕ) [ExpChar F p] (hF : M * (2 * D + 1) < Fintype.card F) (j : Fin (R * M))
  (x : Frame (π.plan pos) ref origin (p ^ l) g H Q j.val) (size : V → ℕ)

local notation "C" => commands c p l hF j x
local notation "I" => Fin (Plan.count (π.plan pos) j)
local notation "root" => Plan.root (π.plan pos) j
local notation "A" => π.records c pos x.record (info size x)

def budget (F : Type) (P g H M D U : ℕ) : ℕ := breadth P g H M D (Nat.card F + 1) ^ ((U + 1) * (M + 1))

variable (bk : budget F (p ^ l) g H M D U ≤ 2 ^ k)

include bk in
theorem fits (i : I) : Fintype.card (C i).action.I ≤ 2 ^ k :=
  (π.wave_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans bk

def code : Selector (Wave.Index C) (B m × B h → B k) :=
  Selector.scattered ((root).trans a.coord) _ (fits c p l hF j x bk)

local notation "S" => code c p l hF j x bk

def issue (tape : B m × B h → B k) (v : B m × B h) :=
  send p l hF j g H (A ∘ a.around U v) (tape v).val

theorem charge_prod (tape : B m × B h → B k) :
    (∏ v, charge p l hF j g H (A ∘ a.around U v) (tape v).val) =
      ((S).read tape).elim 0 (fun i => ∏ v, (C v).action.weight (i v)) := by
  apply Selector.scattered_weight
  · intro i
    have h := (selected_iff p l j c x size _).mpr (Set.mem_range_self i)
    change selected j (A (a.coord (root i))) at h
    change charge p l hF j g H (A ∘ a.around U (a.coord (root i))) _ = _
    simp only [charge, Function.comp_apply, Atlas.around_zero, h, ↓reduceIte, send_at]
    split_ifs <;> rfl
  · intro v hv
    have h := mt (selected_iff p l j c x size v).mp hv
    simp only [charge, Function.comp_apply, Atlas.around_zero, ite_eq_right h, Fin.val_eq_zero_iff]

theorem issue_at (i : I) (z : Wave.Index C) :
    issue c p l hF j x size ((S).write z) (a.coord (root i)) =
      some (reply c p l hF j x z size i) := by
  have eq := Selector.scatter_at ((root).trans a.coord) _ (fits c p l hF j x bk) z i
  change (((S).write z) (a.coord (root i))).val = _ at eq
  unfold issue
  rw [send_at, eq]
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply, reply]

omit [Fintype E] in
theorem issue_away (tape : B m × B h → B k) {v : B m × B h} (hv : v ∉ Set.range ((root).trans a.coord)) :
    issue c p l hF j x size tape v = none := by
  apply send_off
  rw [Function.comp_apply, Atlas.around_zero, selected_iff]
  exact hv

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Frame
end

/-! # Short selectors in finite extensions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
open Sphere.Surface

/-- The common selector budget includes the field elements used by a
movement step. Their contribution grows logarithmically with the field. -/
def selectorBits (A D M T Q : ℕ) :=
  (A * (1 + Nat.clog 2 (T + 1)) + Nat.clog 2 (Q + 1) * 2) * ((D ^ 5 + 1) * (M + 1))

theorem selector_bound (g ℓ D P b : ℕ) :
    ∃ A : ℕ, ∀ {T d : ℕ}, Scales g ℓ D T P b d → ∀ F : Type,
      let M := room ℓ D g
      let H := energy ℓ D (d * b)
      let N := depth ℓ D g P (d * b)
      let k := selectorBits A D M T (Nat.card F)
      M * (2 * N + 1) < A * (1 + T) ^ A ∧
      initialChoices ℓ D b d ≤ 2 ^ k ∧ Local.Frame.budget F P (2 * g) H M N (D ^ 5) ≤ 2 ^ k ∧
      finalChoices g ℓ D P b d ≤ 2 ^ k := by
  obtain ⟨A, hA⟩ := choice_bound g ℓ D P b
  refine ⟨A, ?_⟩
  intro T d sc F M H N k
  obtain ⟨hr, hv⟩ := hA sc
  let a := initialChoices ℓ D b d
  let x := moveChoices g ℓ D P b d
  let c := finalChoices g ℓ D P b d
  let L := (D ^ 5 + 1) * (M + 1)
  let t := 1 + Nat.clog 2 (T + 1)
  let q := Nat.clog 2 (Nat.card F + 1)
  change a * x * c ≤ 2 ^ (A * t) at hv
  have ha : 0 < a := by unfold a initialChoices; positivity
  have hc : 0 < c := by unfold c finalChoices; positivity
  have hx : 0 < x := by unfold x moveChoices branches breadth window; positivity
  have hb : branches P (2 * g) H M N ≤ x := Nat.le_self_pow (by positivity) _
  have h₀ : A * t ≤ k := (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ (show 0 < L by unfold L; positivity))
  have hall : a * x * c ≤ 2 ^ k := hv.trans (Nat.pow_le_pow_right (by decide) h₀)
  refine ⟨hr, (Nat.le_mul_of_pos_right a hx).trans ((Nat.le_mul_of_pos_right _ hc).trans hall),
    ?_, (Nat.le_mul_of_pos_left c (Nat.mul_pos ha hx)).trans hall⟩
  have hcore : (M + 1) * window P (2 * g) H N ^ 2 * (N + 1) ≤ 2 ^ (A * t) :=
    (Nat.le_mul_of_pos_right _ (by positivity : 0 < (M * (2 * N) + 1) ^ 2)).trans
      (hb.trans ((Nat.le_mul_of_pos_left x ha).trans ((Nat.le_mul_of_pos_right _ hc).trans hv)))
  change ((M + 1) * window P (2 * g) H N ^ 2 * (N + 1) * (Nat.card F + 1) ^ 2) ^ L ≤ 2 ^ ((A * t + q * 2) * L)
  conv_rhs => rw [pow_mul (2 : ℕ) (A * t + q * 2), pow_add (2 : ℕ) (A * t), pow_mul (2 : ℕ) q]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul hcore (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)) _

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end

/-!
# Routing the reply by a second neighborhood lookup

Repeated addresses at the origin carry identical replies. At an
occupied site, all replies come from the same initiator.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Coloring
open scoped Classical
variable {F V E T X J L N : Type} [Field F] [Fintype F]
  {r t m d h U R Q M g H D b : ℕ} (p l : ℕ) [ExpChar F p]
  (hF : M * (2 * D + 1) < Fintype.card F) (j : Fin (R * M))

local notation "Meta" => Metadata F r t R Q U M N

private def chooseReply {α β : Type} (f : α → Option β) :=
  if h : ∃ i v, f i = some v then some h.choose_spec.choose else none

private theorem choose_some {α β : Type} (f : α → Option β) (v : β)
    (h : ∃ i, f i = some v) (hu : ∀ i w, f i = some w → w = v) :
    chooseReply f = some v := by
  have e : ∃ i v, f i = some v := ⟨h.choose, v, h.choose_spec⟩
  rw [chooseReply, dite_eq_left e, hu _ _ e.choose_spec.choose_spec]

private theorem choose_none {α β : Type} (f : α → Option β) (h : ∀ i, f i = none) :
    chooseReply f = none := by simp [chooseReply, h]

def route (g H : ℕ) (data : B ((d + 1) * (U + 1)) → B ((d + 1) * U) → Meta)
    (index : B ((d + 1) * (U + 1)) → ℕ) : Meta :=
  let msg := chooseReply (fun i => send p l hF j g H (data i) (index i))
  (data 0 0).map fun u => (u.1, u.2.1, u.2.2.1, msg.elim u.2.2.2 (fun m => m.apply u.1 u.2.2.2))

namespace Frame
variable [Fintype V] [Fintype E] {a : Atlas V E m d h}
  {π : Palette a (2 * U + 2) R} {ref : Reference J L N V E T X} {pos : V → Fin M → F}
  {origin : Stage F r t T V E X} (c : Palette a (horizon U (R * M) 0) Q)
  (x : Frame (π.plan pos) ref origin (p ^ l) g H Q j.val) (size : V → ℕ)
  (bk : budget F (p ^ l) g H M D U ≤ 2 ^ b)
  (sel : Wave.Index (commands c p l hF j x))

local notation "C" => commands c p l hF j x
local notation "I" => Fin (Plan.count (π.plan pos) j)
local notation "root" => Plan.root (π.plan pos) j
local notation "A" => π.records c pos x.record (info size x)
local notation "S" => code c p l hF j x bk
local notation "A'" => π.records c pos (Wave.update C x.record sel) (Wave.carryInfo C sel (info size x))

theorem routed (v : B m × B h) :
    route p l hF j g H (fun i => A ∘ a.around U (a.around (U + 1) v i))
      (fun i => ((S).write sel (a.around (U + 1) v i)).val) = A' v := by
  let recv i := issue c p l hF j x size ((S).write sel) (a.around (U + 1) v i)
  unfold route
  simp only [Function.comp_apply, Atlas.around_zero]
  change (A v).map (fun u => (u.1, u.2.1, u.2.2.1,
    (chooseReply recv).elim u.2.2.2 (fun m => m.apply u.1 u.2.2.2))) = _
  by_cases e : v ∈ Set.range a.coord
  swap
  · rw [Palette.records_away _ _ _ _ _ e, Palette.records_away _ _ _ _ _ e]
    rfl
  obtain ⟨w, rfl⟩ := e
  rw [Palette.records_at, Palette.records_at]
  have cand (i u) (hu : recv i = some u) :
      ∃ k : I, a.near (U + 1) (root k) w ∧ u = reply c p l hF j x sel size k := by
    let v := a.around (U + 1) (a.coord w) i
    have hc : v ∈ Set.range ((root).trans a.coord) := by
      by_contra hn
      have h := issue_away c p l hF j x size ((S).write sel) hn
      exact Option.some_ne_none u (hu.symm.trans h)
    obtain ⟨k, hk⟩ := hc
    change a.coord (root k) = v at hk
    refine ⟨k, ((a.around_iff _ _ _).mp ⟨i, hk.symm⟩).symm, ?_⟩
    change issue c p l hF j x size ((S).write sel) v = some u at hu
    rw [← hk, issue_at] at hu
    exact Option.some.inj hu.symm
  by_cases h : ∃ k : I, a.near (U + 1) (root k) w
  · obtain ⟨k, hk⟩ := h
    have hm : chooseReply recv = some (reply c p l hF j x sel size k) := by
      apply choose_some
      · obtain ⟨i, hi⟩ := (a.around_iff _ _ _).mpr hk.symm
        exact ⟨i, by unfold recv; rw [hi, issue_at]⟩
      · intro i u hu
        obtain ⟨k', hk', rfl⟩ := cand i u hu
        rw [sole j hk' hk]
    rw [hm, receive c p l hF j x sel size w k hk]
    rfl
  · push Not at h
    have hm : chooseReply recv = none := choose_none _ (by
      intro i
      cases e : recv i with
      | none => rfl
      | some u =>
        obtain ⟨k, hk, _⟩ := cand i u e
        exact (h k hk).elim)
    rw [hm, untouched c p l hF j x sel size w h]
    rfl

end Frame
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# Common format of an entire wave schedule

The fields of a world may vary with the preceding expansion choices.
Only short metadata records are materialized. Exterior bits pass
through unchanged, in a separate format.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Assembly Coloring
open scoped Classical

/-- Common numerical parameters across the family of input states. -/
structure Design where
  r : ℕ
  t : ℕ
  m : ℕ
  d : ℕ
  h : ℕ
  U : ℕ
  R : ℕ
  Q : ℕ
  M : ℕ
  g : ℕ
  H : ℕ
  D : ℕ
  p : ℕ
  l : ℕ

namespace Design
variable (a : Design)

abbrev row (F N : Type) := Metadata F a.r a.t a.R a.Q a.U a.M N
abbrev waves := a.R * a.M
abbrev chart := a.p ^ a.l
abbrev port (j : ℕ) := Fmt.rows a.m a.d a.h (.addr j)
abbrev Menu (F N A : Type) (j : ℕ) := B j → A × a.row F N

end Design

/-- A scenario supplies the interpretation of the records and a linear
closure, which may sum over the private selectors of all its cells. -/
structure Scenario (F N A : Type) [Field F] (a : Design) (x y : Wire) where
  V : Type
  E : Type
  T : Type
  X : Type
  J : Type
  L : Type
  [fv : Fintype V]
  [fe : Fintype E]
  atlas : Atlas V E a.m a.d a.h
  π : Palette atlas (2 * a.U + 2) a.R
  c : Palette atlas (horizon a.U a.waves 0) a.Q
  ref : Reference J L N V E T X
  origin : Stage F a.r a.t T V E X
  pos : V → Fin a.M → F
  size : V → ℕ
  header : B a.m × B a.h → A
  controls : ∃ keys ext, origin.Controls keys ext
  room : ∀ z, origin.Reach a.chart a.g a.H a.U z → z.Room a.M a.D
  close : Val x → Val y → (X → F) →ₗ[F] F

attribute [instance] Scenario.fv Scenario.fe

namespace Scenario

variable {F N A : Type} [Field F] {a : Design} {x y : Wire} (w : Scenario F N A a x y)
  {j : ℕ}

abbrev At (i : ℕ) := Frame (w.π.plan w.pos) w.ref w.origin a.chart a.g a.H a.Q i

def stored {i : ℕ} (s : w.At i) (v : B a.m × B a.h) : A × a.row F N :=
  (w.header v, w.π.records w.c w.pos s.record (s.info w.size) v)

structure Code (i : ℕ) (menu : a.Menu F N A j) where
  frame : w.At i
  tape : (a.port j).obj
  host : ∀ v, (tape v).1 = w.atlas.graph v
  read : ∀ v, menu ((tape v.1).2 v.2) = w.stored frame v

def eval {i : ℕ} (s : w.At i) (z : Val x) (u : Val y) : F :=
  w.close z u (s.stage.value a.chart)

end Scenario

universe v
variable {F N A : Type} [Field F] {x y : Wire} {a : Design} {I : Type v} {j : ℕ}

def snapshot (w : I → Scenario F N A a x y) (Z : Format) (payload : I → Val x → Val y → Z.obj)
    (i : ℕ) (menu : a.Menu F N A j) : Snapshot.{v} F x y where
  state := Σ s, (w s).Code i menu
  eval s := (w s.1).eval s.2.frame
  port := (a.port j).pair Z
  encode s p q := (s.2.tape, payload s.1 p q)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end
