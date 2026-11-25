import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario

/-! # Short records for initial concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Boot
open Coloring Neighborhood

abbrev own (d r s e k : ℕ) := Format.pair (.addr e)
  (.pair (.addr ((d + 1) * r + 1)) (.pair (.addr ((d + 1) * s + 1)) (.addr k)))
abbrev query (d r s e k : ℕ) := (own d r s e k).pair (.vec d (own d r s e k))
abbrev selectors (m h k : ℕ) := Format.vec m (.vec h (.addr k))
abbrev source (m d h e k : ℕ) := (Fmt.rows m d h (.addr e)).pair (selectors m h k)

def cost (m d h r s e k v n : ℕ) (Z : Format) :=
  paintCost m d r + paintCost m d s + gatherCost m d v n +
    500 * (Fmt.rows m d h (query d r s e k)).width + 4 * Z.width

variable {m d h e k : ℕ} (r s : ℕ)

def colored (z : (source m d h e k).obj) : (Fmt.rows m d h (own d r s e k)).obj :=
  let g i := (z.1 i).1
  fun i => (g i, fun j => ((z.1 i).2 j, tone g r i, tone g s i, z.2 i j))

def around (z : (source m d h e k).obj) : (Fmt.rows m d h (query d r s e k)).obj :=
  let b := colored r s z
  fun i => ((b i).1, fun j => ((b i).2 j, fun l => (b ((b i).1 l)).2 j))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Boot
end

/-! # The initial dictionary and its single validity test -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere.Surface.Local SphereScale
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {g ℓ D T b d p l : ℕ}
    (S : Scheme F)

local notation "Cfg" => design S g ℓ D b d p l
local notation "R" => 2 * D ^ 5 + 2
local notation "Q" => horizon (D ^ 5) (Design.waves Cfg) 0

abbrev panelQuery (g ℓ D b d p l k : ℕ) :=
  Boot.query S.d (2 * D ^ 5 + 2) (horizon (D ^ 5) (design S g ℓ D b d p l).waves 0) S.ℓ k

local notation "Query" => panelQuery S g ℓ D b d p l

def panelMenu (hK : Ready K ℓ D g (p ^ l) b d) (k : ℕ) :
    (Cfg).Menu F (B S.k) (B S.ℓ) (Query k).width := fun j =>
  let v := (Design.number (Query k)).symm j
  if live S v.1.1 then
    if h : v.1.2.2.2.val < Fintype.card (Shape (probes ℓ D) b d) then
      viewStart S hK v.1.1 v.1.2.1 v.1.2.2.1 (fun i => (v.2 i).1) (fun i => (v.2 i).2.1)
        (fun j => decide (j ≠ 0)) ((Fintype.equivFin _).symm ⟨_, h⟩)
    else (v.1.1, none)
  else (v.1.1, none)

def panelGuard (_sc : Scales g ℓ D T (p ^ l) b d) (k : ℕ) (v : (Query k).obj) : F :=
  if live S v.1.1 then
    if v.1.2.2.2.val < Fintype.card (Shape (probes ℓ D) b d) then 1 else 0
  else if v.1.2.2.2 = 0 then 1 else 0

def panelTable (sc : Scales g ℓ D T (p ^ l) b d) (k : ℕ) : Table F :=
  weightTable (D := .addr (Query k).width) (Design.number (Query k)) (panelGuard S sc k)

def panelAround (_sc : Scales g ℓ D T (p ^ l) b d) {k : ℕ} (z : S.format.obj)
    (c : (Boot.selectors S.m S.h k).obj) : (Fmt.rows S.m S.d S.h (Query k)).obj :=
  Boot.around R Q (z, c)

def panelTape (sc : Scales g ℓ D T (p ^ l) b d) {k : ℕ} (z : S.format.obj)
    (c : (Boot.selectors S.m S.h k).obj) :=
  Fmt.update (D := .addr (Query k).width) (Design.number (Query k)) (panelAround S sc z c)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Choosing an initial shape once at each occupied occurrence -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere.Surface.Local SphereScale Transcript Finset
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h g ℓ D T b d p l k : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z)

local notation "Sh" => Shape (probes ℓ D) b d

private theorem fits (hk : initialChoices ℓ D b d ≤ 2 ^ k) : Fintype.card Sh ≤ 2 ^ k := by
  rw [card_shape]
  exact hk

def panelSelector (hk : initialChoices ℓ D b d ≤ 2 ^ k) :
    Selector (P.Occupied → Sh) (Boot.selectors S.m S.h k).obj :=
  (Selector.scattered A.coord (fun _ => Sh) (fun _ => fits hk)).relabel (Equiv.curry _ _ _)

omit [Field F] in
theorem panelSelector_at (hk : initialChoices ℓ D b d ≤ 2 ^ k) (s : P.Occupied → Sh) (v : P.Occupied) :
    (((P.panelSelector A hk).write s) (A.coord v).1 (A.coord v).2).val =
      (Fintype.equivFin Sh (s v)).val :=
  Selector.scatter_at A.coord (fun _ => Sh) (fun _ => fits hk) s v

variable (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
  (s : P.Occupied → Shape (probes ℓ D) b d) {t : S.Presentation z P.diagram}
  (H : P.Placed t A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val) (fun v => decide (v.2.2 ≠ 0)))
include H

theorem panelWeight (hk : initialChoices ℓ D b d ≤ 2 ^ k) (c : (Boot.selectors S.m S.h k).obj) :
    Fmt.weight (panelGuard S sc k) (panelAround S sc z c) =
      ((P.panelSelector A hk).read c).elim 0 (fun _ => 1) := by
  let w (v : B S.m × B S.h) := panelGuard S sc k (((panelAround S sc z c) v.1).2 v.2)
  have hw := Selector.scattered_weight A.coord (fun _ => Sh) (fun _ => fits hk)
    (Function.uncurry c) (fun _ _ => (1 : F)) w (by
      intro j
      have hj := (H.live_iff (A.coord j)).mpr ⟨j, rfl⟩
      simp only [w, panelGuard, panelAround, Boot.around, Boot.colored, hj, ite_true, Function.uncurry]
      split_ifs <;> rfl)
    (by
      intro v hv
      have hv' := mt (H.live_iff v).mp hv
      simp only [w, panelGuard, panelAround, Boot.around, Boot.colored, hv', ite_false, Function.uncurry]
      split_ifs <;> rfl)
  simp only [prod_const_one, Fintype.prod_prod_type] at hw
  exact hw

/-- The physical tape and the initial frame agree at every host, including vacant slots. -/
def panelCode (hr : P.LocalRanks) (hk : initialChoices ℓ D b d ≤ 2 ^ k) :
    (P.localWorld A sc hK s).Code 0 (panelMenu S hK k) where
  frame := P.start A sc hK s
  tape := panelTape S sc z ((P.panelSelector A hk).write s)
  host _ := rfl
  read := by
    intro i
    simp only [panelTape, Fmt.update, panelMenu, Equiv.symm_apply_apply, panelAround, Boot.around, Boot.colored]
    by_cases hi : i ∈ Set.range A.coord
    · obtain ⟨j, rfl⟩ := hi
      have hj := (H.live_iff (A.coord j)).mpr ⟨j, rfl⟩
      simp only [hj, ite_true, P.panelSelector_at, Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
      exact (P.start_at A sc hK s H hr j).symm
    · rw [ite_eq_right (mt (H.live_iff i).mp hi)]
      exact (P.start_away A sc hK s i hi).symm

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Pricing the two colorings and the initial shape lookup -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Assembly Coloring Rounds.Contraction

namespace Rates
variable (a : Rates)

def paintSize (d r : ℕ) :=
  let q := (d + 1) * r
  2 ^ ((Neighborhood.Check q).width + q + 1)

theorem paint (d r : ℕ) (hs : paintSize d r ≤ a.Y) :
    a.Host 213 (Neighborhood.paintCost a.m d r) := by
  let q := (d + 1) * r
  have ht : 2 ^ q ≤ a.Y :=
    (Nat.pow_le_pow_right (by decide) (by omega : q ≤ (Neighborhood.Check q).width + q + 1)).trans hs
  have hl := a.long
  have hx : 100 + (a.m + 2 ^ q) ≤ a.X := by omega
  have h₁ := Row.hosts (high (Nat.pow_le_pow_left hx 210))
  have h₂ := Row.hosts (Paid.scale (big (hs.trans a.incl)) 32)
  have h₃ : a.Host 1 (Neighborhood.Colors a.m q).width := by
    rw [Neighborhood.Colors, Format.width_vec, Format.width_addr]
    exact Row.hosts (big ((Nat.lt_two_pow_self (n := q)).trans_le (ht.trans a.incl)))
  exact ((h₁.scale 4).plus h₂).plus (h₃.scale 4)

end Rates

namespace Design
variable (a : Design) {F : Type} [Field F] (p : Prices F)

abbrev radius := 2 * a.U + 2
abbrev range := horizon a.U a.waves 0
abbrev own (e k : ℕ) := Boot.own a.d a.radius a.range e k
abbrev entryWidth (e k : ℕ) := (Boot.query a.d a.radius a.range e k).width
def entryCap (e k : ℕ) := 2 ^ a.h * (a.own e k).width
def entryCost (e k : ℕ) := Boot.cost a.m a.d a.h a.radius a.range e k
  (a.entryCap e k) (p.fee (a.m + a.d) (a.entryCap e k))

def coloringSize := Rates.paintSize a.d a.radius + Rates.paintSize a.d a.range

theorem entry_bound (e k : ℕ) (Z : Format) (X Y : ℕ)
    (hs : 10000 ≤ Y) (hl : 1000 + 10 * a.m + 10 * Y ≤ X)
    (hW : 1 + p.W ≤ Y) (hw : 1 + p.w ^ p.power ≤ X) (ht : 2 ^ a.d ≤ Y)
    (hb : a.entryWidth e k ≤ Y) (hc : a.coloringSize ≤ Y) :
    a.entryCost p e k Z ≤ 2 ^ a.m * X ^ 217 + (2 ^ (a.m + a.h) + Z.width) * Y ^ 217 := by
  let c : Rates := ⟨a.m, a.h, X, Y, hs, hl⟩
  let v := a.entryCap e k
  have he : a.entryWidth e k ≤ c.Y ^ 4 := hb.trans (Nat.le_self_pow (by decide) _)
  have hv : c.Row 4 v := by
    apply Rates.low
    refine le_trans ?_ he
    conv_rhs => rw [entryWidth, Boot.query, Format.width_pair]
    exact Nat.le_add_right ..
  have hf := c.fee p a.d v ht hW hw hv
  have hg := c.gather a.d v _ ht hv hf
  have hr := c.paint a.d a.radius ((Nat.le_add_right ..).trans hc)
  have hu := c.paint a.d a.range ((Nat.le_add_left ..).trans hc)
  have hrow := (c.rows a.d _ ht he).scale 500
  have h := Rates.Host.carry (z := Z.width) (((hr.plus hu).plus hg).plus hrow)
  rw [pow_add]
  refine le_trans ?_ (h.scale 4)
  unfold entryCost Boot.cost
  change _ + 4 * Z.width ≤ 4 * (_ + Z.width)
  rw [mul_add]
  exact Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by decide)) _

end Design
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# Concentration up to the final split

The pass-through register has an exact linear charge independent
of the old label width. The latter can grow when rounds repeat.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Design
open Assembly Coloring Rounds.Contraction
variable (a : Design) {F : Type} [Field F] (p : Prices F) (e k : ℕ)

abbrev lastWidth := a.widthAt (a.entryWidth e k) k a.waves

def arity := 3 + 2 * a.maxWidth (a.entryWidth e k) k

theorem entry_fits : 2 * a.entryWidth e k ≤ a.arity e k := by
  have h : a.entryWidth e k + k ≤ a.maxWidth (a.entryWidth e k) k := a.fits_width (Nat.zero_le _)
  unfold arity
  omega

theorem last_fits : a.lastWidth e k ≤ a.arity e k := by
  have h : a.lastWidth e k + k ≤ a.maxWidth (a.entryWidth e k) k := a.fits_width le_rfl
  unfold arity
  omega

/-- This multiplier depends only on the local geometric bounds. -/
def inflation := 10000 + a.coloringSize + 2 ^ a.hops + a.waves+
  2 * a.factor ^ a.waves * ((1 + 2 ^ a.d) * ((a.d + 1) * a.radius + (a.d + 1) * a.range + 2) + 1)

theorem arity_bound : a.arity e k ≤ a.inflation * (1 + e + k) := by
  have h₀ : a.entryWidth e k =
      (1 + 2 ^ a.d) * (e + (a.d + 1) * a.radius + (a.d + 1) * a.range + 2 + k) := by
    simp only [entryWidth, Boot.query, Boot.own, Format.width_pair, Format.width_vec, Format.width_addr]
    rw [Format.width_addr, Format.width_addr]
    ring
  have est (b c f x : ℕ) : 3 + 2 * (f * (b * (e + c + 2 + k) + k)) ≤
      (10000 + x + 2 * f * (b * (c + 2) + 1)) * (1 + e + k) := by ring_nf; omega
  unfold arity maxWidth inflation
  rw [h₀]
  simpa only [add_assoc] using est (1 + 2 ^ a.d) ((a.d + 1) * a.radius + (a.d + 1) * a.range)
    (a.factor ^ a.waves) (a.coloringSize + 2 ^ a.hops + a.waves)

def work (Z : Format) := a.entryCost p e k Z + a.price p (a.entryWidth e k) k Z

theorem work_split (Z : Format) :
    a.work p e k Z = a.work p e k (.addr 0) + (8 + 4 * a.waves) * Z.width := by
  simp only [work, entryCost, Boot.cost, price, totalCost, cost, Format.width_pair,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
  rw [Format.width_addr 0]
  ring

theorem work_bound (Z : Format) (X Y : ℕ) (hl : 1000 + 10 * a.m + 10 * Y ≤ X)
    (hW : 1 + p.W ≤ Y) (hw : 1 + p.w ^ p.power ≤ X) (hY : a.inflation * (1 + e + k) ≤ Y) :
    a.work p e k Z ≤ 2 ^ a.m * X ^ 218 + 2 ^ (a.m + a.h) * Y ^ 218 + (8 + 4 * a.waves) * Z.width := by
  rw [work_split]
  apply Nat.add_le_add_right
  have hi : a.inflation ≤ Y := (Nat.le_mul_of_pos_right _ (by omega)).trans hY
  have ha := (a.arity_bound e k).trans hY
  have h₀ := (a.entry_fits e k).trans ha
  have hs : 10000 ≤ Y ∧ a.coloringSize ≤ Y ∧ 2 ^ a.hops ≤ Y ∧ a.waves ≤ Y := by
    unfold inflation at hi
    generalize 2 ^ a.hops = z at hi ⊢
    omega
  let c : Rates := ⟨a.m, a.h, X, Y, hs.1, hl⟩
  have ht := (Nat.pow_le_pow_right (by decide : 0 < 2) a.degree_le_hops).trans hs.2.2.1
  have h₁ := a.entry_bound p e k (.addr 0) X Y hs.1 hl hW hw ht (by omega) hs.2.1
  have h₂ := a.price_bound p (a.entryWidth e k) k (.addr 0) X Y hs.1 hl hW hw hs.2.2.1
    (by unfold arity at ha; omega) hs.2.2.2
  rw [Format.width_addr, add_zero, pow_add] at h₁ h₂
  rw [pow_add]
  exact Rates.Paid.plus (show c.Host 217 _ from h₁) (show c.Host 215 _ from h₂)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Design
end

/-! # Initial shapes and scenarios for a grouped layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Routing.Private Sphere.Surface.Local SphereScale
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {a D T b d ℓ p l : ℕ} {θ L : ℝ}
    (P : Layer F x y) (B : P.template.Binning a D T (d * b) θ)
    (t : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales ((4 * 5) ^ 300) ℓ D T (p ^ l) b d) (hK : SphereScale.Ready K ℓ D ((4 * 5) ^ 300) (p ^ l) b d)

abbrev panelRadius (D : ℕ) := 2 * D ^ 5 + 2

abbrev panelStates (ℓ : ℕ) := Σ i, ((t i).normal (panelRadius D)).Occupied → Shape (probes ℓ D) b d

abbrev panelWorld (i : P.panelStates B t ℓ) :=
  ((t i.1).normal (panelRadius D)).localWorld ((t i.1).atlas _) sc hK i.2

abbrev panelPort := B.Flags.pair (Fmt.payload B.target.m (P.groupedVolume B) P.height)

abbrev panelPayload (i : P.panelStates B t ℓ) (z : Val x) (w : Val y) : (P.panelPort B).obj :=
  ((P.masked B t (panelRadius D)).encode i.1 z w).2

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Movement schedules for a grouped layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer

open Assembly Coloring Sphere.Surface.Local SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F] {x y : Wire}
    {a D T b d ℓ p l : ℕ} [ExpChar F p] {θ L : ℝ}
    (P : Layer F x y) (B : P.template.Binning a D T (d * b) θ)
    (t : ∀ i, B.Trial (P.presents i) L)

local notation "g" => ((4 * 5) ^ 300 : ℕ)
local notation "Cfg" => Input.design B.target g ℓ D b d p l
variable (sc : Scales g ℓ D T (p ^ l) b d) (hK : SphereScale.Ready K ℓ D g (p ^ l) b d)
    (hF : room ℓ D g *(2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F) (k : ℕ)

abbrev movedMenu := (Cfg).menuAt hF (Input.panelMenu B.target hK k) k (Cfg).waves le_rfl

abbrev moved : Snapshot.{1} F x y :=
  Sphere.Surface.Local.snapshot (P.panelWorld B t sc hK) (P.panelPort B) (P.panelPayload B t) (Cfg).waves (P.movedMenu B hK hF k)

def motionCalls := insert (Input.panelTable B.target sc k) ((Cfg).calls hF (Input.panelMenu B.target hK k) k)

theorem card_motionCalls : (P.motionCalls B sc hK hF k).card ≤ (Cfg).waves + 1 :=
  (Finset.card_insert_le ..).trans (Nat.succ_le_succ ((Cfg).card_calls ..))

variable {k} (q : Contraction.Prices F) {u : ℕ} {labels : Set (Table F)}

omit [Fintype F] [ExpChar F p] in
private theorem panelCity (i : P.panelStates B t ℓ) (v : Coloring.B B.target.m) (j : Coloring.B B.target.d) :
    (P.panelWorld B t sc hK i).atlas.graph v j ≠ v → ∃! l,
      (P.panelWorld B t sc hK i).atlas.graph ((P.panelWorld B t sc hK i).atlas.graph v j) l = v :=
  ((t i.1).atlas (panelRadius D)).reciprocal v j

omit [Field F] [Fintype F] [ExpChar F p] in
theorem panelWidth_eq (S : Scheme F) (G ℓ' D' b' d' p' l' k' : ℕ) :
    (Input.panelQuery S G ℓ' D' b' d' p' l' k').width =
    (Input.design S G ℓ' D' b' d' p' l').entryWidth S.ℓ k' := rfl

theorem movePanel (hk : Frame.budget F (Cfg).chart (Cfg).g (Cfg).H (Cfg).M (Cfg).D (Cfg).U ≤ 2 ^ k)
    (hw : B.target.m + (Cfg).hops ≤ q.w) (hu : (Cfg).arity B.target.ℓ k ≤ u)
    (ht : ↑(P.motionCalls B sc hK hF k) ⊆ labels) :
    Transforms F u labels
      (Sphere.Surface.Local.snapshot (P.panelWorld B t sc hK) (P.panelPort B) (P.panelPayload B t) 0
        (Input.panelMenu B.target hK k))
      (P.moved B t sc hK hF k) ((Cfg).price q ((Input.panelQuery B.target g ℓ D b d p l k).width) k (P.panelPort B)) := by
  have ha : 3 ≤ u := (Nat.le_add_right ..).trans hu
  have hb : 2 * (Cfg).maxWidth ((Input.panelQuery B.target g ℓ D b d p l k).width) k ≤ u := by
    rw [panelWidth_eq]
    exact (Nat.le_add_left ..).trans hu
  have ht' : ↑((Cfg).calls hF (Input.panelMenu B.target hK k) k) ⊆ labels := fun _ h => ht (Finset.mem_insert_of_mem h)
  have hu' : 0 < (Cfg).U := pow_pos sc.Dpos 5
  have h := priced_waves (a := Cfg) (e := (Input.panelQuery B.target g ℓ D b d p l k).width) (k := k) (P.panelWorld B t sc hK) (P.panelPort B) (P.panelPayload B t)
    hF (Input.panelMenu B.target hK k) q hk (P.panelCity B t sc hK)
    ha hu' hw hb ht'
  exact h

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end
