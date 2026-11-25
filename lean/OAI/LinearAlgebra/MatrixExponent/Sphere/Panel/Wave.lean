import OAI.LinearAlgebra.MatrixExponent.Sphere.Concentration.Kits
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.History
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.View
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Reorder
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Update

/-!
# Emission of a terminal configuration

Reindex the species into equally sized chunks, retain the selector and
motion wires inside each diagram, then pad and route the resulting
bundles on a common block host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.FinalBounds
open Sphere Surface Finset
open SphereScale (Scales chunks budget q)
open Sphere.Layout (Key Sharing Alphabet Place item)
open scoped Classical

variable {F Z X : Type} [Field F] {x y : Wire} {H D T b d g r t ℓ m : ℕ} {W : ℝ}
  {P : Input F x y H D T (d * b) g W} {Y : Alphabet P.Occupied}

section Chunked
variable {z : Stage F (chunks ℓ D * r) (chunks ℓ D * t) Z P.Occupied P.grid.Seam X}
  {A : Key.Source Y x y z} (h : P.FinalBounds A ℓ m) (sc : Scales g ℓ D T m b d)

abbrev geometry : (Key.share z A).Geo P (Sharing.allocation g ℓ) where
  site := Function.Embedding.subtype _
  near e := ⟨(h.near e).1.symm, (h.near e).2⟩
  count v := (h.positions v).trans sc.room_le
  chunks := sc.chunks_le
  degree := (Sharing.Geo.Raw.slots_fit sc le_rfl).2.2
  frozen := P.fixed (z := z)
  left := h.left
  right := h.right

omit [Field F] in
theorem raw (ht : chunks ℓ D * t = d) :
    (geometry h sc).Raw ℓ m b d z.scene.level
      (fun i => thinStation (item z.scene.cell i)) (fun k => k.isLeft) := by
  have hex (i : Place z.scene.cell) : (Key.share z A).exteriorLoad i = P.exterior A i := by
    unfold Sharing.exteriorLoad exterior
    congr!
  refine ⟨?_, h.seams, h.seamEnergy, h.energy, h.collected, h.collectors, ?_, ?_,
    h.light, h.heavy, h.aux, h.residue, ?_, ?_, ?_, ?_⟩
  · simpa only [Occupied, Fintype.card_coe] using P.occupied
  · simpa only [hex] using h.extMax
  · simpa only [hex] using h.extSquare
  · exact fun v => (Key.card_filter _ _).trans (h.keys v)
  · apply Key.width_le
    · intro i
      refine (h.selector i).trans (div_le_div_of_nonneg_right ?_ (by positivity))
      exact_mod_cast (Nat.le_mul_of_pos_right (d * b) sc.apos).trans sc.lower
    · intro j hj
      rw [ht]
      exact sc.hidden_width j (h.hidden j hj)
  · rintro (v | j) hj
    · exact h.selector v
    · contradiction
  · intro i hi j hj
    have hh := hi.2 _ (Key.mem_filter.mp hj)
    cases j <;> exact hh

end Chunked

variable {z : Stage F r t Z P.Occupied P.grid.Seam X} {A : Key.Source Y x y z}

abbrev profileType {E V : Type} [Fintype E] [Fintype V] {M r t : ℕ}
    (C : V → Surface.Cell F (M * r) (M * t) Z E X) (e : E → ℕ) :
    Fintype (Layout.Profile C e) := inferInstance

theorem emit (h : P.FinalBounds A ℓ m) (sc : Scales g ℓ D T m b d)
    {r' t' a u : ℕ} (hr : r = chunks ℓ D * r') (ht : t = chunks ℓ D * t')
    (ha : r = d * b) (hb : t = d) (hD : D = 2 ^ a) (hu : 0 < u)
    (hu' : u * D ^ (terminalExponent g ℓ) ≤ T) :
    ∃ (I : Type) (_ : Fintype I) (Q : I → LocalTerm F x y H u) (c : I → F),
      Fintype.card I ≤ P.termsBound ℓ m ∧
      (∀ x y, ∑ i, c i * (Q i).diagram.eval x y = ∑ j, z.value m (A.init x y j)) ∧
      ∀ i, Concentrated P (Q i) (terminalExponent g ℓ) a ℓ := by
  subst r t
  have hD' : 4 ≤ D := le_trans (by decide) sc.bound
  let G := geometry h sc
  have hraw := raw h sc hb
  have hc := hraw.budgets sc ha hb rfl le_rfl a
  let I := Layout.Profile z.scene.cell z.scene.level
  refine ⟨I, profileType _ _, fun p => G.output hD hD' p m hu, Layout.Profile.sign,
    hraw.term_count sc rfl h.positions, ?_, ?_⟩
  · intro x y
    have he := G.sum_output hD hD' (e := z.scene.level) m hu x y
    refine he.trans ?_
    have ht := Key.sum_stack Y (chunks ℓ D * t') z.hidden (A.init x y) (z.scene.value m)
    refine Eq.trans ?_ (ht.trans ?_)
    · exact sum_congr (by ext; simp) (fun _ _ => rfl)
    · exact sum_congr (by ext; simp) (fun _ _ => rfl)
  · exact fun p => G.concentrated hD hD' hc p m hu le_rfl hu'

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.FinalBounds
end

/-! # The terminal diagrams of a local expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Sphere Surface SphereScale Finset
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)
  (p : P.Tools K ℓ m) (sc : Scales g ℓ D T m b d)

theorem final_bounds (s : P.Occupied → Routing.Private.Shape (probes ℓ D) b d)
    (z : P.Configuration p)
    (hz : (P.plant p s).Reach m (2 * g) (SphereScale.energy ℓ D (d * b)) (D ^ 5) z)
    (hs : z.Stopped) : P.FinalBounds (P.shared p s hz sc.Rpos) ℓ m := by
  let A := P.shared p s hz sc.Rpos
  have hlarge : 100 ≤ budget g := (by have := budget_large g; omega)
  have hW : 0 ≤ W := le_trans (by positivity) P.occupied
  have hb : P.FinalBounds A ℓ m := by
    refine P.reached_bounds p s sc hz hs A (fun _ => rfl) (fun _ => rfl)
      (fun i => P.draw_collector p s hz (.inl i)) (fun i => P.draw_collector p s hz (.inr i))
      ?_ ?_ (P.selector_le p sc)
    · intro i _
      have he : P.drawLoad p s hz i ≤ 100 * D * T := by exact_mod_cast P.draw_max p s hz i
      exact he.trans (by gcongr)
    · have he := P.draw_fixed_squares p s hz
      refine le_trans ?_ (show W * T ≤ budget g * W * T by
        gcongr
        exact le_mul_of_one_le_left hW (by exact_mod_cast (show 1 ≤ budget g by omega)))
      refine le_trans (le_of_eq ?_) he
      let e : {i : Layout.Place z.scene.cell // P.fixed i} ≃
          {i : Layout.Place z.scene.cell // (Layout.item z.scene.cell i).label.role = .collector} :=
        Equiv.refl _
      exact Fintype.sum_equiv e (fun i => (P.exterior A i.val : ℝ) ^ 2)
        (fun i => (P.drawLoad p s hz i.val : ℝ) ^ 2) (fun _ => rfl)
  exact hb

include sc in
theorem terminal {a : ℕ} (hD : D = 2 ^ a) {u : ℕ} (hu : 0 < u)
    (hu' : u * D ^ (terminalExponent g ℓ) ≤ T) :
    ∀ s (z : P.Configuration p),
      (P.plant p s).Reach m (2 * g) (SphereScale.energy ℓ D (d * b)) (D ^ 5) z →
      z.Valid (D ^ 5) → z.Stopped → P.Emitted p z u (terminalExponent g ℓ) a := by
  intro s z hz _ hs
  have hb := P.final_bounds p sc s z hz hs
  obtain ⟨j, hj⟩ := sc.divides
  have hdb : d * b = chunks ℓ D * (j * b) := by rw [hj, mul_assoc]
  exact hb.emit sc hdb hj rfl rfl hD hu hu'

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Uniform local concentration from the sphere price -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Filter

/-- The host bound is chosen before the subdivision, the field threshold
before the scale, and the packet width before the diagram. -/
theorem local_law {k : Type} [Field k] [Finite k]
    (sync : Prices.SharedPrice (AlgebraicClosure k)) (ℓ : ℕ) : LocalLaw k ℓ := by
  intro g _
  refine ⟨Input.terminalExponent g ℓ, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * SphereScale.budget g)] with a ha
  let D := 2 ^ a
  have hD : 2 * SphereScale.budget g ≤ D := ha.trans Nat.lt_two_pow_self.le
  obtain ⟨K, _, _, _, p, l, b, _, _, hc⟩ := SphereScale.choose (ℓ := ℓ) k sync hD
  obtain ⟨A, hA⟩ := SphereScale.stack g ℓ D (p ^ l) b
  refine ⟨A, K, inferInstance, inferInstance, inferInstance, ?_⟩
  filter_upwards [hc] with T hT
  obtain ⟨d, sc, hK⟩ := hT
  refine ⟨d * b, sc.Rpos, sc.smallR, ?_⟩
  intro F _ _ _ hF u hu hu' x y h W P
  have : CharP F p := charP_of_injective_algebraMap' K p
  obtain ⟨kit⟩ := P.tools_exist sc hK
  exact hA sc F K p l rfl hF P kit u _ a (P.terminal kit sc rfl hu hu')

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset Function
open scoped Classical

variable {V : Type} [Fintype V]

/-- A symmetric family of closed neighborhoods admits a coloring
with one color per possible neighbor. -/
theorem distinguish (B : V → Finset V) (d : ℕ) (hd : ∀ i, (B i).card ≤ d)
    (sym : ∀ i j, j ∈ B i → i ∈ B j) :
    ∃ color : V → Fin (d + 1), ∀ i j, j ∈ B i → color i = color j → i = j := by
  have h (s : Finset V) : ∃ color : V → Fin (d + 1),
      ∀ i ∈ s, ∀ j ∈ s, j ∈ B i → color i = color j → i = j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨f, hf⟩ := ih
      have bound : ((B a).image f).card < (univ : Finset (Fin (d + 1))).card := by
        rw [card_univ, Fintype.card_fin]
        exact Nat.lt_succ_of_le (card_image_le.trans (hd a))
      obtain ⟨c, _, hc⟩ := exists_mem_notMem_of_card_lt_card bound
      refine ⟨update f a c, fun i hi j hj hm h => ?_⟩
      by_cases h₁ : i = a
      · subst i
        by_contra ne
        rw [update_self, update_of_ne (Ne.symm ne)] at h
        exact hc (h.symm ▸ mem_image_of_mem f hm)
      by_cases h₂ : j = a
      · subst j
        rw [update_self, update_of_ne h₁] at h
        exact (hc (h ▸ mem_image_of_mem f (sym i a hm))).elim
      rw [update_of_ne h₁, update_of_ne h₂] at h
      exact hf i ((mem_insert.mp hi).resolve_left h₁) j ((mem_insert.mp hj).resolve_left h₂) hm h
  obtain ⟨f, hf⟩ := h univ
  exact ⟨f, fun i j => hf i (mem_univ i) j (mem_univ j)⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring Finset
open scoped Classical
variable {m d : ℕ} (g : B m → B d → B m)

def ball (r : ℕ) (x : B m) := univ.image (expand r g x)

theorem mem_ball (r : ℕ) (x y : B m) : y ∈ ball g r x ↔ Reach g r x y := by
  simp only [ball, mem_image, mem_univ, true_and, mem]

theorem card_ball (r : ℕ) (x : B m) : (ball g r x).card ≤ 2 ^ ((d + 1) * r) := by
  exact card_image_le.trans_eq (by simp)

theorem color (r : ℕ) (hg : ∀ i j, g i j ≠ i → ∃ l, g (g i j) l = i) :
    ∃ c : B m → Fin (2 ^ ((d + 1) * r) + 1), ∀ i j, Reach g r i j → c i = c j → i = j := by
  have h := Sphere.Surface.Local.distinguish (ball g r) _ (card_ball g r)
    (fun i j h => (mem_ball _ _ _ _).mpr (((mem_ball _ _ _ _).mp h).symm hg))
  simpa only [mem_ball] using h

theorem Reach.join {g : B m → B d → B m} {x y z : B m} {r t : ℕ}
    (h : Reach g r x y) (h' : Reach g t y z) : Reach g (r + t) x z := by
  induction r generalizing x with
  | zero => simpa [show x = y from h] using h'
  | succ r ih =>
    obtain ⟨u, hx, hu⟩ := h
    rw [Nat.succ_add]
    exact ⟨u, hx, ih hu⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end

section
/-!
# Local coordinates on a host shared by independent networks

An occupied vertex is a host position and a block number. Different
blocks never share a seam. Colors distinguish the bounded neighborhood
of each host position independently of the number of blocks.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Coloring Assembly

structure Atlas (V E : Type) (m d h : ℕ) where
  coord : V ↪ B m × B h
  graph : B m → B d → B m
  reciprocal : ∀ i j, graph i j ≠ i → ∃ l, graph (graph i j) l = i
  src : E → V
  dst : E → V
  links : Function.Injective (fun i => (src i, dst i))
  adjacent : ∀ i, (coord (src i)).2 = (coord (dst i)).2 ∧
    ∃ j, graph (coord (src i)).1 j = (coord (dst i)).1

variable {V E : Type} {m d h q R : ℕ}

namespace Atlas

variable (a : Atlas V E m d h)

def near (R : ℕ) (x y : V) : Prop :=
  (a.coord x).2 = (a.coord y).2 ∧ Neighborhood.Reach a.graph R (a.coord x).1 (a.coord y).1

theorem near.refl (R : ℕ) (x : V) : a.near R x x :=
  ⟨rfl, Neighborhood.Reach.refl _ _ _⟩

theorem near_edge (i : E) : a.near 1 (a.src i) (a.dst i) :=
  ⟨(a.adjacent i).1, _, .inr (a.adjacent i).2, rfl⟩

variable {a} {x y z : V} {r s : ℕ}

theorem near.symm (e : a.near r x y) : a.near r y x :=
  ⟨e.1.symm, e.2.symm a.reciprocal⟩

theorem near.join (e : a.near r x y) (f : a.near s y z) : a.near (r + s) x z :=
  ⟨e.1.trans f.1, e.2.join f.2⟩

theorem near.mono (e : a.near r x y) (h : r ≤ s) : a.near s x y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact e.join (.refl a k y)

end Atlas

structure Palette (a : Atlas V E m d h) (R q : ℕ) where
  color : B m → Fin q
  valid : ∀ x y, Neighborhood.Reach a.graph R x y → color x = color y → x = y

theorem Atlas.palette (a : Atlas V E m d h) (R : ℕ) :
    Nonempty (Palette a R (2 ^ ((d + 1) * R) + 1)) := by
  obtain ⟨c, h⟩ := Neighborhood.color a.graph R a.reciprocal
  exact ⟨c, h⟩

namespace Palette
variable {a : Atlas V E m d h} (c : Palette a R q)

def mark (v : V) := c.color (a.coord v).1

def edge (i : E) := (c.mark (a.src i), c.mark (a.dst i))

theorem distinguish {x y : V} (h : a.near R x y) (e : c.mark x = c.mark y) : x = y :=
  a.coord.injective (Prod.ext (c.valid _ _ h.2 e) h.1)

theorem injective_at {x u v : V} {r : ℕ} (h : r + r ≤ R)
    (hu : a.near r x u) (hv : a.near r x v) (e : c.mark u = c.mark v) : u = v :=
  c.distinguish ((hu.symm.join hv).mono h) e

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# A unique coloring certified by local predecessor checks

At each host the choice of a fresh color depends only on colors
at smaller neighboring addresses. Uniqueness avoids a multiplicity
factor when the certificate is summed in positive characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood

open Finset Coloring

variable {m d q : ℕ}

private theorem free (f : B q → Option (B (q + 1))) : ∃ c, ∀ j, f j ≠ some c := by
  let v j := (f j).getD 0
  have bound : (univ.image v).card < (univ : Finset (B (q + 1))).card := by
    apply card_image_le.trans_lt
    simp [pow_succ]
  obtain ⟨c, _, h⟩ := exists_mem_notMem_of_card_lt_card bound
  refine ⟨c, fun j e => h (mem_image.mpr ⟨j, mem_univ _, ?_⟩)⟩
  simp only [v, e, Option.getD_some]

def choose (f : B q → Option (B (q + 1))) : B (q + 1) := (free f).choose

abbrev paletteSize (d r : ℕ) := 2 ^ ((d + 1) * r + 1)

variable (g : B m → B d → B m) (r : ℕ)

def tone (i : B m) : Fin (paletteSize d r) :=
  choose fun j => if _h : expand r g i j < i then some (tone (expand r g i j)) else none
termination_by i.val

def correct (t : B m → Fin (paletteSize d r)) (i : B m) : Prop :=
  t i = choose fun j => if expand r g i j < i then some (t (expand r g i j)) else none

theorem tone_correct (i : B m) : correct g r (tone g r) i := by
  unfold correct
  conv_lhs => rw [tone]
  rfl

theorem correct_iff (t : B m → Fin (paletteSize d r)) :
    (∀ i, correct g r t i) ↔ t = tone g r := by
  constructor
  · intro h
    funext i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      rw [show t i = _ from h i, show tone g r i = _ from tone_correct g r i]
      congr 1
      funext j
      split_ifs with he
      · rw [ih _ he]
      · rfl
  · rintro rfl; exact tone_correct g r

theorem tone_separates (reciprocal : ∀ i j, g i j ≠ i → ∃ k, g (g i j) k = i) (i j : B m)
    (edge : Reach g r i j) (he : tone g r i = tone g r j) : i = j := by
  have diff (i j : B m) (h : Reach g r i j) (lt : j < i) : tone g r i ≠ tone g r j := by
    obtain ⟨k, hk⟩ := mem.mpr h
    let f l := if expand r g i l < i then some (tone g r (expand r g i l)) else none
    intro eq
    have bad := (free f).choose_spec k
    change f k ≠ some (choose f) at bad
    apply bad
    rw [show choose f = tone g r i from (tone_correct g r i).symm, eq]
    simp [f, hk, lt]
  rcases lt_trichotomy i j with h|h|h
  · exact (diff j i (edge.symm reciprocal) h he.symm).elim
  · exact h
  · exact (diff i j edge h he).elim

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end

/-! # Preparing the local checks of a guessed host coloring -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring
variable {m q d t : ℕ} (F : Type) [Field F]

abbrev Colors (m q : ℕ) := Format.vec m (.addr (q + 1))
abbrev Entry (q : ℕ) := Format.pair .bit (.addr (q + 1))
abbrev Check (q : ℕ) := Format.vec q (Entry q)
abbrev Checks (m q : ℕ) := Format.vec m (Check q)

def previous (x : (Rows m q).obj × (Colors m q).obj) : (Checks m q).obj :=
  fun i j => (decide (x.1 i j < x.1 i 0), x.2 (x.1 i j))

private theorem cheap_previous (hm : m ≤ t) (hq : 2 ^ q ≤ t) :
    Cheap F m t (.pair (Rows m q) (Colors m q)) (Checks m q) previous 22 := by
  let A := Format.pair (Rows m q) (Colors m q)
  have hq' : q + 1 ≤ t := Nat.lt_two_pow_self.trans_le hq
  have hw : A.width ≤ 2 ^ m * (100 + t) ^ 3 := by
    simp only [A, Rows, Colors, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add]
    rw [Format.width_addr]
    refine Nat.mul_le_mul_left _ ((Nat.add_le_add (Nat.mul_le_mul hq hm) hq').trans ?_)
    ring_nf; omega
  have base := Cheap.id F hw
  have col (i : B q) := base.fst.comp (column F hm hq i)
  have get := Cheap.lookup F m t (.addr (q + 1)) hm (by rw [Format.width_addr]; exact hq')
  have lt : Cheap F 0 t (.pair (.addr m) (.addr m)) .bit (fun z => decide (z.1 < z.2)) 3 := by
    refine ⟨_, numeric_lt F m, ?_⟩
    rw [Format.width_pair, Format.width_addr, Format.width_bit]
    ring_nf; omega
  have bit (i : B q) : Cheap F m t A (.vec m (Entry q)) (fun x j => previous x j i) 16 := by
    have read := (base.snd.pair (col i)).comp get
    have test := ((col i).pair (col 0)).zip.comp (Cheap.map _ fun _ => lt)
    exact (test.pair read).zip.mono (by decide)
  have all := Cheap.share _ bit hq
  let B := Format.vec q (.vec m (Entry q))
  have bounds : (Checks m q).width ≤ 2 ^ m * (100 + t) ^ 3 := by
    simp only [Checks, Check, Entry, Format.width_vec, Format.width_pair]
    rw [Format.width_bit, Format.width_addr]
    apply Nat.mul_le_mul_left
    refine (Nat.mul_le_mul hq (Nat.add_le_add_left hq' 1)).trans ?_
    ring_nf; omega
  have hb : B.width = (Checks m q).width := by simp only [B, Checks, Check, Format.width_vec]; ring
  have flip : Cheap F m t B (Checks m q) (fun a i j => a j i) 4 :=
    Cheap.project F (hb.le.trans bounds) bounds (fun z => (z.2.1, z.1, z.2.2)) (fun _ _ => rfl)
  exact (all.comp flip).mono (by decide)

def prepareColor (r : ℕ) (x : (Rows m d).obj × (Colors m ((d + 1) * r)).obj) :=
  previous (expand r x.1, x.2)

theorem cheap_color (m d r : ℕ) (hr : 0 < r) :
    Cheap F m (m + 2 ^ ((d + 1) * r)) (.pair (Rows m d) (Colors m ((d + 1) * r)))
      (Checks m ((d + 1) * r)) (prepareColor r) 210 := by
  let q := (d + 1) * r
  let t := m + 2 ^ q
  have hm : m ≤ t := Nat.le_add_right _ _
  have hq : 2 ^ q ≤ t := Nat.le_add_left _ _
  have hd : 2 ^ d ≤ t := (Nat.pow_le_pow_right (by decide) (show d ≤ q from
    (Nat.le_succ d).trans (Nat.le_mul_of_pos_right _ hr))).trans hq
  have hw : (Format.pair (Rows m d) (Colors m q)).width ≤ 2 ^ m * (100 + t) ^ 3 := by
    simp only [Rows, Colors, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add]
    rw [Format.width_addr]
    refine Nat.mul_le_mul_left _ ((Nat.add_le_add (Nat.mul_le_mul hd hm) (Nat.lt_two_pow_self.trans_le hq)).trans ?_)
    ring_nf; omega
  have base := Cheap.id F hw
  have h := ((base.fst.comp (cheap F m d r hr)).pair base.snd).comp (cheap_previous F hm hq)
  exact h.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end

/-! # An exact host-coloring network with no high-arity labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {u m d q r : ℕ} {L : Set (Table F)}

private def colorOf (a : (Check q).obj) : (Format.addr (q + 1)).obj := (a 0).2

private def weight (a : (Check q).obj) : F :=
  if colorOf a = choose (fun i => if (a i).1 then some (a i).2 else none) then 1 else 0

private theorem weight_spec (g : (Rows m d).obj) (t : (Colors m ((d + 1) * r)).obj) (i : B m) :
    weight (F := F) (prepareColor r (g, t) i) = if correct g r t i then 1 else 0 := by
  by_cases h : correct g r t i
  · rw [ite_eq_left h, weight, ite_eq_left]
    simp only [colorOf, prepareColor, previous, origin, decide_eq_true_eq]
    exact h
  · rw [ite_eq_right h, weight, ite_eq_right]
    simp only [colorOf, prepareColor, previous, origin, decide_eq_true_eq]
    exact h

private theorem weights (g : (Rows m d).obj) (t : (Colors m ((d + 1) * r)).obj) :
    ∏ i, weight (F := F) (prepareColor r (g, t) i) = if t = tone g r then 1 else 0 := by
  simp only [weight_spec (F := F) g t]
  by_cases h : t = tone g r
  · simp [h, tone_correct]
  rw [ite_eq_right h, ← correct_iff] at *
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

private theorem small {A B : Format} (hu : 3 ≤ u) (f : A.obj → B.obj → F) :
    Kernel F u L A B f (32 * 2 ^ (A.width + B.width)) := by
  intro a b i j
  obtain ⟨v, h, hv⟩ := Net.dense a b (fun x y => f (view A i x) (view B j y))
  obtain ⟨s, hs, h⟩ := h.includeWide (L := L) hu
  have ha := (Fintype.card_congr i).trans (card_slots a)
  have hb := (Fintype.card_congr j).trans (card_slots b)
  exact ⟨s, by rw [← ha, ← hb] at hv; unfold Format.width; omega, h⟩

private theorem small_action {A B : Format} (hu : 3 ≤ u) (f : A.obj → B.obj) (w : A.obj → F) :
    Action F u L A B f w (32 * 2 ^ (A.width + B.width)) := small hu _

private theorem collapse {A C : Format} (hu : 3 ≤ u) (f : A.obj → C.obj)
    {a : (A.pair C).obj → C.obj} {w : (A.pair C).obj → F} {n : ℕ}
    (h : Action F u L (A.pair C) C a w n)
    (ha : ∀ x y, a (x, y) = y) (hw : ∀ x y, w (x, y) = if y = f x then 1 else 0) :
    Map F u L A C f (n + 4 * C.width) := by
  let _ := Fintype.ofFinite C.obj
  have hs := Kernel.sum_hidden hu h
  simp only [ha, hw, sum_ite_eq', mem_univ, ite_true] at hs
  simpa only [Map, eq_comm] using hs

def paintCost (m d r : ℕ) :=
  let q := (d + 1) * r
  4 * (2 ^ m * (100 + (m + 2 ^ q)) ^ 210) + 2 ^ m * (32 * 2 ^ ((Check q).width + q + 1)) + 4 * (Colors m q).width

/-- Only the host count, not the number of blocks, multiplies the
long-address work. Invalid colorings have weight zero. -/
theorem paint (m d r : ℕ) (hr : 0 < r) (hu : 3 ≤ u) :
    Map F u L (Rows m d) (Colors m ((d + 1) * r)) (fun g => tone g r) (paintCost m d r) := by
  let q := (d + 1) * r
  let A := Rows m d
  let C := Colors m q
  let D := Format.addr (q + 1)
  let B := Check q
  obtain ⟨n, h, hn⟩ := cheap_color F m d r hr
  have step : Action F u L B D colorOf weight (32 * 2 ^ (B.width + q + 1)) := by
    rw [Nat.add_assoc, ← show D.width = q + 1 from Format.width_addr _]
    exact small_action hu _ _
  have cells := Action.vec (A := B) (B := D) (fun _ : Coloring.B m => colorOf)
    (fun _ => weight) (fun _ => step)
  have both := cells.pre (Map.circuit (L := L) hu h)

  have size : 4 * n + 2 ^ m * (32 * 2 ^ (B.width + q + 1)) + 4 * C.width ≤ paintCost m d r := by
    unfold paintCost; dsimp only [B, C, q]; omega
  apply Map.mono (collapse (A := A) (C := C) hu (fun g => tone g r) both ?_ ?_) size
  · intro g t
    funext i
    simp only [Function.comp_apply, colorOf, prepareColor, previous, origin]
  · intro g t
    simp only [Function.comp_apply, weights]
    by_cases h : t = tone g r
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end

/-! # Naming occupied vertices and their incident seams by local colors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {V E : Type} {m d h q R U : ℕ} {a : Atlas V E m d h}

def Atlas.touches (a : Atlas V E m d h) (U : ℕ) (v : V) (i : E) :=
  a.near U v (a.src i) ∨ a.near U v (a.dst i)

theorem Atlas.touches.near {v : V} {i : E} (h : a.touches U v i) :
    a.near (U + 1) v (a.src i) ∧ a.near (U + 1) v (a.dst i) := by
  rcases h with h | h
  · exact ⟨h.mono (by omega), h.join (a.near_edge i)⟩
  · exact ⟨h.join (a.near_edge i).symm, h.mono (by omega)⟩

variable [Fintype V] [Fintype E]

private def names {B : Type} (f : V → B) (p : V → Prop) := (univ.filter p).image f

private theorem mem_names {B : Type} {f : V → B} {p : V → Prop} {b : B} :
    b ∈ names f p ↔ ∃ x, p x ∧ f x = b := by simp [names]

private def address {B : Type} (f : V → B) (p : V → Prop) : ↥(names f p) ↪ V where
  toFun i := (mem_names.mp i.property).choose
  inj' i j h := Subtype.ext ((mem_names.mp i.property).choose_spec.2.symm.trans
    ((congrArg f h).trans (mem_names.mp j.property).choose_spec.2))

private theorem addr_spec {B : Type} (f : V → B) (p : V → Prop) (i : names f p) :
    p (address f p i) ∧ f (address f p i) = i.val := (mem_names.mp i.property).choose_spec

namespace Palette

variable (c : Palette a R q) (U : ℕ) (v : V)

def vertices := names c.mark (a.near U v)
def labels := names c.edge (a.touches U v)
def vertex : ↥(c.vertices U v) ↪ V := address c.mark (a.near U v)
def seam : ↥(c.labels U v) ↪ E := address c.edge (a.touches U v)

def center : c.vertices U v := ⟨c.mark v, mem_names.mpr ⟨v, .refl _ _ _, rfl⟩⟩

omit [Fintype E] in
theorem vertex_spec (j : c.vertices U v) :
    a.near U v (c.vertex U v j) ∧ c.mark (c.vertex U v j) = j.val := addr_spec _ _ j

omit [Fintype V] in
theorem seam_spec (j : c.labels U v) :
    a.touches U v (c.seam U v j) ∧ c.edge (c.seam U v j) = j.val := addr_spec _ _ j

variable {U v} (hr : 2 * U + 2 ≤ R)
include hr

omit [Fintype E] in
theorem center_eq : c.vertex U v (c.center U v) = v :=
  c.injective_at (by omega) (c.vertex_spec ..).1 (.refl _ _ _) (c.vertex_spec ..).2

omit [Fintype E] in
theorem vertex_range {w : V} : w ∈ Set.range (c.vertex U v) ↔ a.near U v w := by
  constructor
  · rintro ⟨i, rfl⟩; exact (c.vertex_spec ..).1
  · intro hw
    let j : c.vertices U v := ⟨c.mark w, mem_names.mpr ⟨w, hw, rfl⟩⟩
    exact ⟨j, c.injective_at (by omega) (c.vertex_spec ..).1 hw (c.vertex_spec ..).2⟩

omit [Fintype V] in
theorem seam_range {i : E} : i ∈ Set.range (c.seam U v) ↔ a.touches U v i := by
  constructor
  · rintro ⟨j, rfl⟩; exact (c.seam_spec ..).1
  · intro hi
    let j : c.labels U v := ⟨c.edge i, mem_names.mpr ⟨i, hi, rfl⟩⟩
    obtain ⟨hj, he⟩ := c.seam_spec U v j
    refine ⟨j, a.links (Prod.ext ?_ ?_)⟩
    · exact c.injective_at (by omega) hj.near.1 hi.near.1 (congrArg Prod.fst he)
    · exact c.injective_at (by omega) hj.near.2 hi.near.2 (congrArg Prod.snd he)

/-- Initiators of the same color have no shared vertex or incident seam. -/
theorem separate {w : V} (hn : v ≠ w) (he : c.mark v = c.mark w) :
    Disjoint (Set.range (c.vertex U v)) (Set.range (c.vertex U w)) ∧
      Disjoint (Set.range (c.seam U v)) (Set.range (c.seam U w)) := by
  have no (z : V) (h : a.near (U + 1) v z) (k : a.near (U + 1) w z) : False :=
    hn (c.distinguish ((h.join k.symm).mono (by omega)) he)
  refine ⟨Set.disjoint_left.mpr (fun z h k => ?_), Set.disjoint_left.mpr (fun j h k => ?_)⟩
  · exact no z (((c.vertex_range hr).mp h).mono (by omega)) (((c.vertex_range hr).mp k).mono (by omega))
  · exact no _ ((c.seam_range hr).mp h).near.1 ((c.seam_range hr).mp k).near.1

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Restricting the motion data to a colored neighborhood -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {F V E K N T X J L : Type} {r t m d h q R U g : ℕ}
  {a : Atlas V E m d h}

structure Incident (G : Record F r t V E K N) (a : Atlas V E m d h) : Prop where
  loopless : ∀ e, a.src e ≠ a.dst e
  endpoints : ∀ v e, e ∈ (G.ports v).map Prod.fst ↔ a.src e = v ∨ a.dst e = v

theorem Matches.incident {G : Record F r t V E K N} {ref : Reference J L N V E T X}
    {β : V ⊕ ℕ → K} {s : Stage F r t T V E X} (h : Matches ref.world β s G)
    (hl : s.Layout a.src a.dst g) : Incident G a := by
  refine ⟨hl.loopless, fun v e => ?_⟩
  have he := h.ports v
  change s.ports v = (G.ports v).map id at he
  rw [List.map_id] at he
  rw [← he]
  exact hl.incident v e

namespace Palette

variable [Fintype V] [Fintype E] (c : Palette a R q) (U : ℕ) (v : V)

abbrev Region (F : Type) (r t : ℕ) (K N : Type) :=
  Record F r t ↥(c.vertices U v) ↥(c.labels U v) K N

def localPorts (l : List (E × F)) : List (↥(c.labels U v) × F) :=
  l.filterMap (fun y => if h : c.edge y.1 ∈ c.labels U v then some (⟨c.edge y.1, h⟩, y.2) else none)

def extract (G : Record F r t V E K N) : c.Region U v F r t K N where
  rows i := G.rows (c.vertex U v i)
  ports i := c.localPorts U v (G.ports (c.vertex U v i))
  level i := G.level (c.seam U v i)
  footprint i := G.footprint (c.vertex U v i)

variable {U v} (hr : 2 * U + 2 ≤ R)
include hr

omit [Fintype V] in
private theorem ports_eq (l : List (E × F)) (hl : ∀ x ∈ l, a.touches U v x.1) :
    (c.localPorts U v l).map (Prod.map (c.seam U v) id) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨i, hi⟩ := (c.seam_range hr).mpr (hl x (by simp))
    have e : c.edge x.1 = i.val := by rw [← hi, (c.seam_spec U v i).2]
    rw [localPorts, List.filterMap_cons]
    simp only [e, i.property, ↓reduceDIte, List.map_cons]
    change (c.seam U v i, x.2) :: (c.localPorts U v l).map _ = x :: l
    rw [hi, ih (fun y hy => hl y (.tail _ hy))]

variable {G : Record F r t V E K N}

theorem view (hl : Incident G a) : View G (c.vertex U v) (c.seam U v) (c.extract U v G) := by
  refine ⟨fun _ => rfl, fun i => ?_, fun _ => rfl, fun _ => rfl⟩
  symm
  apply c.ports_eq hr
  intro x hx
  have near := (c.vertex_spec U v i).1
  rcases (hl.endpoints _ _).mp (List.mem_map_of_mem hx) with e|e
  · exact .inl (e.symm ▸ near)
  · exact .inr (e.symm ▸ near)

theorem covers (hl : Incident G a) : Covers (c.extract U v G).ports (c.center U v) U := by
  let f := c.vertex U v
  let k := c.seam U v
  let H := c.extract U v G
  have e := c.view hr (v := v) hl
  have go (n b : ℕ) (i : c.vertices U v) (hb : b + n ≤ U) (hi : a.near b v (f i)) :
      Covers H.ports i n := by
    induction n generalizing b i with
    | zero => trivial
    | succ n ih =>
      intro x hx
      have h' : (k x.1, x.2) ∈ G.ports (f i) := by
        rw [e.ports]
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      obtain ⟨w, ne, edge, other⟩ : ∃ w, w ≠ f i ∧ a.near 1 (f i) w ∧
          k x.1 ∈ (G.ports w).map Prod.fst := by
        let j := k x.1
        rcases (hl.endpoints _ _).mp (List.mem_map.mpr ⟨_, h', rfl⟩) with hp|hp
        · rw [← hp]
          exact ⟨a.dst j, (hl.loopless j).symm, a.near_edge j, (hl.endpoints _ _).mpr (.inr rfl)⟩
        · rw [← hp]
          exact ⟨a.src j, hl.loopless j, (a.near_edge j).symm, (hl.endpoints _ _).mpr (.inl rfl)⟩
      obtain ⟨i', he⟩ := (c.vertex_range hr).mpr ((hi.join edge).mono (by omega : b + 1 ≤ U))
      subst w
      rw [e.ports] at other
      obtain ⟨_, hmem, he⟩ := List.mem_map.mp other
      obtain ⟨⟨u, y⟩, hmem', rfl⟩ := List.mem_map.mp hmem
      have hsame := k.injective he
      subst u
      exact ⟨i', y, fun eq => ne (congrArg f eq), hmem', ih (b + 1) i' (by omega) (hi.join edge)⟩
  exact go U 0 (c.center U v) (by omega) (by unfold f; rw [c.center_eq hr]; exact .refl a 0 v)

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# A deterministic wave lookup on colored regions

The complete input to the local kernel is a panel indexed by host
colors and ordered pairs of colors. A panel does not contain the
ambient graph or the interpretation of its local names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open scoped Classical
variable {F V E X T J L K N : Type} {m d h q R U r t n : ℕ}

structure Panel (F : Type) (r t q U : ℕ) (K N : Type) where
  vertices : Finset (Fin q)
  edges : Finset (Fin q × Fin q)
  center : vertices
  input : Record F r t vertices edges K N
  pos : F
  fresh : Fin (U + 1) → K

namespace Panel

variable (a : Panel F r t q U K N)

def key (j : ℕ) := a.fresh ⟨min j U, by omega⟩
def safe := Covers a.input.ports a.center U

variable [Field F] [Fintype F] (p l g H M D : ℕ) [ExpChar F p] (hF : M * (2 * D + 1) < Fintype.card F)

def action : Script F r t a.vertices a.edges K N :=
  if e : a.safe then (a.input.run p l g H U M D hF a.center a.pos a.key e).choose
    else Script.pure a.input

theorem spec (e : a.safe) :
    let s := a.action p l g H M D hF
    s.Ordered a.key 0 U ∧ s.Runs a.input (p ^ l) g H U M D a.center a.pos ∧
      Fintype.card s.I ≤ breadth (p ^ l) g H M D (Nat.card F + 1) ^ ((U + 1) * (M + 1)) := by
  rw [action, dite_eq_left e]
  exact (a.input.run p l g H U M D hF a.center a.pos a.key e).choose_spec

abbrev Kernel (F : Type) (r t q : ℕ) (K N : Type) :=
  Σ (v : Finset (Fin q)) (e : Finset (Fin q × Fin q)), Script F r t v e K N

def kernel : Kernel F r t q K N :=
  ⟨a.vertices, a.edges, a.action p l g H M D hF⟩

end Panel

namespace Palette
variable [Fintype V] [Fintype E] {a : Atlas V E m d h} (c : Palette a R q)

def panel (U : ℕ) (G : Record F r t V E K N) (v : V) (z : F) (ν : ℕ → K) : Panel F r t q U K N :=
  ⟨c.vertices U v, c.labels U v, c.center U v, c.extract U v G, z, fun i => ν i.val⟩

variable [Field F] [Fintype F] (hr : 2 * U + 2 ≤ R) (G : Record F r t V E K N) (hG : Incident G a)
  (ref : Reference J L N V E T X) (p l g H M D : ℕ) [ExpChar F p]
  (hF : M * (2 * D + 1) < Fintype.card F) (v : Fin n ↪ V) (z : Fin n → F) (ν : V → ℕ → K)

def wave (i : Fin n) : Command F r t T V E X K N (p ^ l) g H U M D ref.key where
  vertices := c.vertices U (v i)
  edges := c.labels U (v i)
  ref := ref.region (c.vertex U (v i)) (c.seam U (v i))
  shared := rfl
  input := c.extract U (v i) G
  action := (c.panel U G (v i) (z i) (ν (v i))).action p l g H M D hF
  start := c.center U (v i)
  pos := z i
  runs := ((c.panel U G (v i) (z i) (ν (v i))).spec p l g H M D hF (c.covers hr hG)).2.1

local notation "C" => c.wave hr G hG ref p l g H M D hF v z ν

theorem prepared (color : ∀ i j, c.mark (v i) = c.mark (v j)) : Wave.Prepared C G ref :=
  ⟨⟨fun i j h => (c.separate hr (v.injective.ne h) (color i j)).1,
    fun i j h => (c.separate hr (v.injective.ne h) (color i j)).2⟩,
    rfl, fun _ => rfl, fun _ => rfl, fun i => c.view hr (v := v i) hG⟩

theorem wave_target (i : Fin n) : (C i).target = (v i, z i) := by
  exact Prod.ext (c.center_eq hr) rfl

theorem wave_ordered (i : Fin n) : (C i).action.Ordered (ν (v i)) 0 U := by
  have hh := ((c.panel U G (v i) (z i) (ν (v i))).spec p l g H M D hF (c.covers hr hG)).1
  intro j
  obtain ⟨bound, h⟩ := hh j
  refine ⟨bound, fun k => ?_⟩
  rw [zero_add] at bound
  have hk : k.val ≤ U := k.isLt.le.trans bound
  have e := h k
  simp only [Panel.key, panel, zero_add, min_eq_left hk] at e
  rw [zero_add]
  exact e

theorem wave_bound (i : Fin n) : Fintype.card (C i).action.I ≤
    breadth (p ^ l) g H M D (Nat.card F + 1) ^ ((U + 1) * (M + 1)) :=
  ((c.panel U G (v i) (z i) (ν (v i))).spec p l g H M D hF (c.covers hr hG)).2.2

/-- Includes the index type, multiplicities, coefficients, output
records and allocation order. Equal panels have identical kernels. -/
theorem wave_kernel (i : Fin n) :
    (⟨c.vertices U (v i), c.labels U (v i), (C i).action⟩ : Panel.Kernel F r t q K N) =
      (c.panel U G (v i) (z i) (ν (v i))).kernel p l g H M D hF := rfl

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end
