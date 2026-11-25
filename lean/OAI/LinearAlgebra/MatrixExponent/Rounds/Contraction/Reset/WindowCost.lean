import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Label
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Attachment.WriteNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Described
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Apply
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.ShortNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Factor
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Elect

/-! # Attaching the frozen border to the elected reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}
    [NeZero Y] [NeZero w]
    (h : Input A L P p r 1 u u z payload d B K H σ) (s : Slice Δ Y w t)
    (hC : Δ ≤ C) (hk : 2 ^ t ≤ K) (R : Rotor F Y w) (hc : 1 ≤ κ)
    (cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w)
local notation "X" => (frame A L u z payload Δ C P)
local notation "b" => book T u t z B
local notation "M" => meter L t z B
local notation "N" => raw R T L u t z Δ C B r

abbrev Choice := History.Reset.Setup.Selection (poll h s hC hk) R (fun q => fits h s hC hk q R hc cost)
  (board h s hC hk) b M (Nat.sub_le T.scheme.h r)

def choose : Choice h s hC hk R hc cost :=
  History.Reset.Setup.select (poll h s hC hk) R (fun q => fits h s hC hk q R hc cost)
    (board h s hC hk) b M (Nat.sub_le T.scheme.h r) (fun q => room h s hC hk q R hc cost)

namespace Choice
variable {h s hC hk R hc cost} (E : Choice h s hC hk R hc cost) (q : (frame A L u z payload Δ C P).state)
local notation "U" => poll h s hC hk q
local notation "hf" => fits h s hC hk q R hc cost
local notation "G" => History.Reset.Setup.graph U R hf
local notation "g" => E.graph q
local notation "S" => E.layout q

theorem valid : (b).Ready S (g).1 :=
  ready h s hC hk q R hc cost S (g).1 (History.Reset.Setup.hop S g (E.describes q))

abbrev query : A.Query N (slots A r) 0 := History.Reset.Setup.query A M S g q.val.raw

abbrev posted : (N).Encodes (E.query q).fresh G := History.Reset.Setup.outputEncodes M S g (E.valid q) (E.placed q).block (E.describes q)
  (Reset.valid h s hC hk q R hc cost)

end Choice
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Budgets for selecting, printing and attaching a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing History.Reset
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {x y : Wire} {Y w : ℕ} {T : Template F}
    (R : Rotor F Y w) (A : Attachment T) (L : BorderLimit F x y)
    (u t z Δ C B r : ℕ) (p : Prices F)

local notation "a" => (T.scheme.h - r)
local notation "k" => Nat.clog 2 (T.scheme.h + 1)
local notation "n" => (T.scheme.h - (T.scheme.h - r) + 8)
local notation "j" => History.Reset.Child.extra R Δ (T.scheme.h - (T.scheme.h - r))
local notation "Y₀" => raw R T L u t z Δ C B r
local notation "Y₁" => next R T L u t z Δ C B r
local notation "s" => slots A r

def width := Template.Mix.arity T k (indices T Δ z B) + Tile.attachedWidth T Y₀ A k n j s +
  2 * (Y₀).scheme.ℓ + A.rebuildWidth Y₁ s 0

def setupCost := 40 * A.format.width + Template.Mix.cost T k (indices T Δ z B) (T.scheme.h - t - a)
def decideCost := Tile.attachedCost T Y₀ A k n j s (p.fee (T.scheme.m + T.scheme.d) (Tile.volume T Y₀ k n))
def controlCost := setupCost A t z Δ B r + decideCost R A L u t z Δ C B r p + A.sweepCost Y₀ s 0

def rebuildCost :=
  let v := 2 ^ T.scheme.d * T.scheme.m + 2 ^ T.scheme.h * A.ℓ
  let v' := (Attachment.Inspect.Packet T.scheme.m T.scheme.d 0 a (A.bundle Y₁ s 0)).width
  A.rebuildCost Y₁ s 0 v (p.fee (T.scheme.m + T.scheme.d) v) v' (p.fee ((Y₁).scheme.m + (Y₁).scheme.d) v')

def params (P : Bound) : Template.Mix.Params :=
  ⟨a, u, Δ, C, denominator L, Template.Encodes.margin Δ, (2 : ℝ) ^ t * P.load⟩

def labels (P : Bound) (gates : Finset (Table F)) :=
  insert (BatchDescent.Snapshot.sweepTable Y₀) (insert (A.rebuildGate Y₁ s 0 0)
    (gates ∪ Template.Mix.keys T k (indices T Δ z B) (params (T := T) L u t Δ C r P)))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Attaching the frozen border to the elected reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}
    [NeZero Y] [NeZero w]
    (h : Input A L P p r 1 u u z payload d B K H σ) (s : Slice Δ Y w t)
    (hC : Δ ≤ C) (hk : 2 ^ t ≤ K) (R : Rotor F Y w) (hc : 1 ≤ κ)
    (cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w)
local notation "X" => (frame A L u z payload Δ C P)
local notation "b" => book T u t z B
local notation "M" => meter L t z B
local notation "N" => raw R T L u t z Δ C B r

namespace Choice
variable {h s hC hk R hc cost} (E : Choice h s hC hk R hc cost) (q : (frame A L u z payload Δ C P).state)
local notation "U" => poll h s hC hk q
local notation "hf" => fits h s hC hk q R hc cost
local notation "G" => History.Reset.Setup.graph U R hf
local notation "g" => E.graph q
local notation "S" => E.layout q

local notation "Z" => E.query q
local notation "e" => E.posted q

theorem active : Attachment.Relocation.WriteActive e (Z).active :=
  History.Reset.Setup.query_active A M S g q.val.raw e rfl

theorem moves : (Z).R.Moves q.val.q e (History.Reset.Setup.resetSlot A U q.val.q.slot) :=
  (E.placed q).moves A M q.val.q e rfl rfl

theorem agrees : (Z).M.Agrees q.val.q.core.post.toPresentation (e).post.toPresentation :=
  (S).move_agrees (E.valid q).lengths (E.valid q).agrees _ (E.placed q).parent

def result := (Z).apply (E.moves q) (E.active q) (E.agrees q) (show (N).full = true from h.full)

theorem fits : (E.result q).Fits payload :=
  (Z).fits (E.moves q) (E.active q) (E.agrees q) (show (N).full = true from h.full) q.property.2

theorem spare : A.Sparse (N).sweep (slots A r) (copies t B) (E.result q).raw := by
  obtain ⟨δ, hδ, hl, hb⟩ := charges h q (gain t) G (estimates h s hC hk q R hc cost).2.1.2.2
  exact (Z).spare (E.moves q) (E.active q) (E.agrees q) (show (N).full = true from h.full) hδ hl hb

theorem exterior (l : MatrixExponent.slots x ⊕ MatrixExponent.slots y) :
    let j := ((E.result q).q.pres.boundary l).val
    let old := (q.val.q.pres.boundary l).val
    (Z).sweep.R.kept q.val.raw j.1.1 = some old.1.1 ∧ j.1.2 = A.outer (N).sweep old.1.2 ∧ j.2.val = old.2.val :=
  by unfold result; apply Attachment.Query.exterior

end Choice
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # One reset writer shared by all states of the attached network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Choice
open Assembly Packing History.Reset
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}
    [NeZero Y] [NeZero w]
    {h : Input A L P p r 1 u u z payload d B K H σ} {s : Slice Δ Y w t}
    {hC : Δ ≤ C} {hk : 2 ^ t ≤ K} {R : Rotor F Y w} {hc : 1 ≤ κ}
    {cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w}
    (E : Choice h s hC hk R hc cost)
local notation "X" => (frame A L u z payload Δ C P)
local notation "k" => Nat.clog 2 (T.scheme.h + 1)
local notation "n" => (T.scheme.h - (T.scheme.h - r) + 8)
local notation "j" => History.Reset.Child.extra R Δ (T.scheme.h - (T.scheme.h - r))
local notation "N" => raw R T L u t z Δ C B r
local notation "M" => meter L t z B
local notation "Tapes" => (fun i : (frame A L u z payload Δ C P).state => Board.tape (board h s hC hk i))

theorem selected : Tile.Local T N k n j (Nat.sub_le ..) rfl Tapes
    (fun i => ((E.query i).fresh, (E.query i).M.commands)) := by
  exact E.fields (by have := s.core; omega) (by simp [h.full])
    (fun i => i.property.1.neutral) (fun i => E.valid i)

theorem attached : Tile.QueryLocal T N A k n j (slots A r) (Nat.sub_le ..) rfl Tapes E.query := by
  intro q q' v v' i i' eq
  exact Board.query_eq A M (E.placed q) (E.placed q') (by omega)
    (by have := s.core; omega) (by simp [h.full]) eq q.val.raw q'.val.raw
    (E.selected q q' v v' i i' eq)

theorem local_net :
    ∃ gates : Finset (Table F), gates.card ≤ 3 ∧
      (∀ f ∈ gates, Processor.arity f ≤ Tile.attachedWidth T N A k n j (slots A r)) ∧
      ∀ {v m : ℕ} {W : Set (Table F)}, 3 ≤ v → Tile.attachedWidth T N A k n j (slots A r) ≤ v →
        (∀ f ∈ gates, f ∈ W) → Access F v W (T.scheme.m + T.scheme.d) (Tile.volume T N k n) m →
        Computes F v W (A.format.pair (Tile.pair T k)) (A.Requests N (slots A r) 0)
          (fun i : (X).state => (i.val.raw, (board h s hC hk i).tape))
          (fun i => (E.query i).requests) (fun _ => 1) (Tile.attachedCost T N A k n j (slots A r) m) := by
  exact Tile.attached_net T N A k n j (slots A r) (Nat.sub_le ..) rfl Tapes E.query E.headers
    E.selected E.control (fun i => E.build i) E.attached (fun i => i.val.q.core.reciprocal) (by omega)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Choice
end

/-! # Width, degree and evaluation of the reattached reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Query
open Packing Coloring
variable {F T : Type} [Field F] [Fintype T] {x y a b : Wire} {D Y : Template F} {A : Attachment D}
  {k m u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u} {H : HostNet F L Y.scheme.h v}
  {Z : Border F T a b x y} (q : A.Query Y k m)
  {old : A.Encloses q.old G Z} {fresh : Y.Encodes q.fresh H} {slot : T → B k}
  (h : q.R.Moves old fresh slot) (ok : Relocation.WriteActive fresh q.active)
  (move : q.M.Agrees old.core.post.toPresentation fresh.post.toPresentation) (full : Y.full = true)

theorem apply_eq (he : ∀ i j, H.diagram.eval i j = G.diagram.eval i j) (i : Val a) (j : Val b) :
    (Z.attach G.diagram).eval i j = q.sweep_weight * (q.apply h ok move full).diagram.eval i j := by
  refine Eq.trans ?_ (Z.attach_factor fresh.post.toPresentation i j)
  rw [Z.eval_attach, Z.eval_attach]
  simp only [he]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Query

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Choice
open Assembly Packing
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}
    [NeZero Y] [NeZero w]
    {h : Input A L P p r 1 u u z payload d B K H σ} {s : Slice Δ Y w t}
    {hC : Δ ≤ C} {hk : 2 ^ t ≤ K} {R : Rotor F Y w} {hc : 1 ≤ κ}
    {cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w}
    (E : Choice h s hC hk R hc cost) (q : (frame A L u z payload Δ C P).state)
local notation "U" => poll h s hC hk q
local notation "hf" => Reset.fits h s hC hk q R hc cost
local notation "Q" => History.Reset.Setup.result U R hf
local notation "G" => History.Reset.Setup.graph U R hf
local notation "N" => raw R T L u t z Δ C B r
local notation "Z" => A.transport (Template.sweep N) (slots A r)

theorem eval (v : Val x) (j : Val y) :
    q.val.diagram.eval v j = (E.query q).sweep_weight * (E.result q).diagram.eval v j := by
  unfold result
  apply Attachment.Query.apply_eq
  exact (estimates h s hC hk q R hc cost).1

set_option maxHeartbeats 750000 in
theorem preserved (hg : gain t ≤ K) :
    Ready Z L z 3 (C ^ (900 + Y + 1)) (after L P K (2 * resetWidth κ w) (2 * resetWidth κ w) σ) (E.result q) := by
  obtain ⟨_, bounds, width, moves, mass⟩ := estimates h s hC hk q R hc cost
  have ha := q.property.1
  unfold result
  refine moved_ready q.val (E.query q) G q.val.q (E.posted q) _
    (E.moves q) (E.active q) (E.agrees q) (show (N).full = true from h.full) ha
    ⟨((Q).owner (Classical.choice ha.live, 0)).2⟩ ?_ ?_ moves ⟨bounds.1, ?_, ?_⟩ width mass
  · intro _ j eq
    exact j.property (Prod.ext ((Q).support j.val).1 eq)
  · exact (E.valid q).floor ha.span
  · exact fun j => (bounds.2.1 j).trans (Reduction.degree_reset (s.core.trans hC))
  · intro v j
    change (G).load v j ≤ (K : ℝ) * P.load
    exact (bounds.2.2 v j).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hg) ((Nat.cast_nonneg _).trans h.load))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Choice
end

/-! # Selecting the mixer while retaining the old border labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing Coloring
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ : ℝ}
    (h : Input A L P p r 1 u u z payload d B K H σ) (s : Slice Δ Y w t)
    (hC : Δ ≤ C) (hk : 2 ^ t ≤ K) (R : Rotor F Y w) (gates : Finset (Table F))
local notation "X" => (frame A L u z payload Δ C P)
local notation "k" => Nat.clog 2 (T.scheme.h + 1)
local notation "keys" => labels R A L u t z Δ C B r P gates
local notation "D" => indices T Δ z B
local notation "Z" => params (T := T) L u t Δ C r P
local notation "N" => raw R T L u t z Δ C B r

theorem few (hg : gates.card ≤ 3) : (keys).card ≤ 17 := by
  unfold labels
  iterate 2
    apply (Finset.card_insert_le ..).trans
    apply Nat.add_le_add_right
  exact (Finset.card_union_le ..).trans (Nat.add_le_add hg (Template.Mix.few T k D Z))

theorem start {v : ℕ} (hu : 3 ≤ v) (hw : width R A L u t z Δ C B r ≤ v) :
    Computes F v keys A.format (A.format.pair (History.Reset.Tile.pair T k))
      (fun i : (X).state => i.val.raw) (fun i => (i.val.raw, (board h s hC hk i).tape))
      (fun _ => 1) (setupCost A t z Δ B r) := by
  let L' : Set (Table F) := keys
  have hk' : T.scheme.h < 2 ^ k := Nat.le_pow_clog (by decide : 1 < 2) _
  have hkeys : (Template.Mix.keys T k D Z : Set (Table F)) ⊆ L' :=
    fun _ hj => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hj))
  have hf : Template.Mix.arity T k D ≤ v := by unfold width at hw; omega
  have select : Circuit F A.format T.format Prod.fst (A.format.width + 2 * T.format.width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  have init := (Map.circuit hu select).comp (Template.Mix.prepare_net T k D Z hf hkeys t hk')
  let data := fun i : (X).state => i.val.raw
  have pre := Computes.of_map (x := data) (y := fun i => (board h s hC hk i).tape) init (fun _ => rfl)
  have cp := Computes.of_map (x := data) (Map.circuit (L := L') hu (Circuit.id F A.format)) (fun _ => rfl)
  have net := cp.pair hu pre
  simp only [one_mul] at net
  refine net.mono ?_
  have ha : T.format.width ≤ A.format.width := by rw [Attachment.width]; exact Nat.le_add_right ..
  change _ + (_ + (_ + Template.Mix.cost T k D (T.scheme.h - t - (T.scheme.h - r)))) ≤ _
  unfold setupCost
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Combining the shared reset dictionaries and withdrawing scalar factors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Choice
open Assembly Packing Coloring History.Reset
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}
    [NeZero Y] [NeZero w]
    {h : Input A L P p r 1 u u z payload d B K H σ} {s : Slice Δ Y w t}
    {hC : Δ ≤ C} {hk : 2 ^ t ≤ K} {R : Rotor F Y w} {hc : 1 ≤ κ}
    {cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w}
    (E : Choice h s hC hk R hc cost)

local notation "X" => (frame A L u z payload Δ C P)
local notation "k" => Nat.clog 2 (T.scheme.h + 1)
local notation "n" => (T.scheme.h - (T.scheme.h - r) + 8)
local notation "j" => History.Reset.Child.extra R Δ (T.scheme.h - (T.scheme.h - r))
local notation "N" => raw R T L u t z Δ C B r
local notation "N'" => next R T L u t z Δ C B r
local notation "s'" => slots A r

theorem device {v : ℕ} (hu : 3 ≤ v) (hw : width R A L u t z Δ C B r ≤ v)
    (lo : 1 ≤ T.scheme.m) (hi : T.scheme.m + T.scheme.d ≤ p.w) :
    ∃ W : Finset (Table F), W.card ≤ 17 ∧ A.rebuildGate N' s' 0 0 ∈ W ∧
      Computes F v W A.format (A.Requests N' s' 0)
        (fun i : (X).state => i.val.raw) (fun i => (E.query i).sweep.requests)
        (fun i => (E.query i).sweep_weight) (controlCost R A L u t z Δ C B r p) := by
  obtain ⟨gates, card, _, net⟩ := E.local_net
  let keys := labels R A L u t z Δ C B r P gates
  have hpre := start h s hC hk R gates hu hw
  have ha : Tile.attachedWidth T N A k n j s' ≤ v := by unfold width at hw; omega
  have hs : 2 * (N).scheme.ℓ ≤ v := by unfold width at hw; omega
  have small (f) (hf : f ∈ gates) : f ∈ (keys : Set _) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hf))
  have ready := net hu ha small (p.access hu (lo.trans (Nat.le_add_right ..)) hi _)
  have sweep := Attachment.Query.sweep_net (L := (keys : Set (Table F))) E.query hu hs
    (Finset.mem_insert_self ..)
  have run := (hpre.comp ready).comp sweep
  simp only [one_mul] at run
  exact ⟨keys, few R gates card, Finset.mem_insert_of_mem (Finset.mem_insert_self ..), run⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Choice
end

/-! # Reattaching old records to the selected reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing Coloring History.Reset
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}

def supplyCost (R : Rotor F Y w) (A : Attachment T) (L : BorderLimit F x y)
    (u t z Δ C B r : ℕ) (p : Prices F) :=
  let N := next R T L u t z Δ C B r
  controlCost R A L u t z Δ C B r p + 24 * (A.Requests N (slots A r) 0).width +
    rebuildCost R A L u t z Δ C B r p

namespace Choice
variable [NeZero Y] [NeZero w] {h : Input A L P p r 1 u u z payload d B K H σ}
    {s : Slice Δ Y w t} {hC : Δ ≤ C} {hk : 2 ^ t ≤ K} {R : Rotor F Y w} {hc : 1 ≤ κ}
    {cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w}
    (E : Choice h s hC hk R hc cost)

local notation "X" => (frame A L u z payload Δ C P)
local notation "shift" => History.Reset.Child.extra R Δ (T.scheme.h - (T.scheme.h - r))
local notation "N" => next R T L u t z Δ C B r
local notation "s'" => slots A r
local notation "V" => A.Requests N s' 0
local notation "U" => A.transport N s'
local notation "Wiring" => Format.pair V (Attachment.format U)

abbrev swept (i : (X).state) := (E.query i).sweep

theorem rebuild {v : ℕ} {W : Set (Table F)}
    (hu : 3 ≤ v) (hw : width R A L u t z Δ C B r ≤ v)
    (lo : 1 ≤ T.scheme.m) (hi : T.scheme.m + T.scheme.d ≤ p.w) (end' : (N).scheme.m + (N).scheme.d ≤ p.w)
    (allow : A.rebuildGate N s' 0 0 ∈ W) :
    Computes F v W V (U).format (fun i => (E.swept i).requests) (fun i => (E.swept i).result)
      (fun _ => 1) (rebuildCost R A L u t z Δ C B r p) := by
  have first := lo.trans (Nat.le_add_right _ T.scheme.d)
  have last : 1 ≤ (N).scheme.m + (N).scheme.d :=
    (lo.trans (Nat.le_add_right _ shift)).trans (Nat.le_add_right ..)
  exact Attachment.Query.rebuild_net hu (Nat.sub_le ..)
    (p.access hu first hi _) le_rfl (p.access hu last end' _) le_rfl
    (Setup.parent T shift) (fun _ => none) E.swept 0 (fun _ _ _ => rfl)
    (fun i => i.val.q.core.reciprocal) (fun i => (E.posted i).reciprocal)
    (fun _ _ => rfl) ((Nat.le_add_left ..).trans hw) allow

def pending (i : (X).state) : (Wiring).obj := ((E.swept i).requests, (E.swept i).result)

theorem supply {v : ℕ} (hu : 3 ≤ v) (hw : width R A L u t z Δ C B r ≤ v)
    (lo : 1 ≤ T.scheme.m) (hi : T.scheme.m + T.scheme.d ≤ p.w) (end' : (N).scheme.m + (N).scheme.d ≤ p.w) :
    ∃ W : Finset (Table F), W.card ≤ 17 ∧
      Computes F v W A.format Wiring (fun i : (X).state => i.val.raw) E.pending
        (fun i => (E.query i).sweep_weight) (supplyCost R A L u t z Δ C B r p) := by
  obtain ⟨W, hw', ok, net⟩ := E.device hu hw lo hi
  have decode := E.rebuild (W := ↑W) hu hw lo hi end' ok
  have keep := Computes.of_map (L := (W : Set (Table F))) (x := fun i => (E.swept i).requests)
    (Map.circuit hu (Circuit.id F V)) (fun _ => rfl)
  have run := net.comp (keep.pair hu decode)
  simp only [mul_one] at run
  refine ⟨W, hw', run.mono ?_⟩
  unfold supplyCost
  dsimp only
  omega

end Choice
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Total transformation with an attached payload and sparse frozen labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing Coloring
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}

omit [Fintype F] in
private theorem raise {I : Type*} {X Y : Format} {v n : ℕ} {W L : Set (Table F)}
    {x : I → X.obj} {y : I → Y.obj} {c : I → F}
    (h : Computes F v L X Y x y c n) (hl : L ⊆ W) : Computes F v W X Y x y c n :=
  let ⟨f, hf, he⟩ := h
  ⟨f, hf.widen le_rfl hl, he⟩

omit [Fintype F] in
private theorem send {X Y : Snapshot.{1} F x y} {v n : ℕ} {W : Set (Table F)}
    (dest : X.state → Y.state) (weight : X.state → F)
    (ev : ∀ i a b, X.eval i a b = weight i * Y.eval (dest i) a b)
    (net : Computes F v W X.port Y.port
      (fun i : X.state × Val x × Val y => X.encode i.1 i.2.1 i.2.2)
      (fun i => Y.encode (dest i.1) i.2.1 i.2.2) (fun i => weight i.1) n) :
    Transforms F v W X Y n := by
  obtain ⟨f, hf, he⟩ := net
  refine ⟨f, hf, fun i => ⟨Unit, inferInstance, fun _ => dest i, fun _ => weight i, ?_, ?_⟩⟩
  · intro a b
    rw [Fintype.sum_unique]
    exact ev i a b
  · intro a b j
    rw [Fintype.sum_unique]
    exact he (i, a, b) j

def runCost (R : Rotor F Y w) (A : Attachment T) (L : BorderLimit F x y)
    (u t z Δ C B r payload : ℕ) (p : Prices F) :=
  supplyCost R A L u t z Δ C B r p + 4 * (Attachment.payload x y payload T.scheme.m).width +
    A.shrinkCost (next R T L u t z Δ C B r) (slots A r) (copies t B) x y payload

namespace Choice
variable [NeZero Y] [NeZero w] {h : Input A L P p r 1 u u z payload d B K H σ}
    {s : Slice Δ Y w t} {hC : Δ ≤ C} {hk : 2 ^ t ≤ K} {R : Rotor F Y w} {hc : 1 ≤ κ}
    {cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w}
    (E : Choice h s hC hk R hc cost)

local notation "src" => (frame A L u z payload Δ C P)
local notation "N" => Template.sweep (raw R T L u t z Δ C B r)
local notation "k'" => slots A r
local notation "U" => A.transport N k'
local notation "Wiring" => Format.pair (A.Requests (next R T L u t z Δ C B r) (slots A r) 0)
  (Attachment.format (A.transport (next R T L u t z Δ C B r) (slots A r)))
local notation "D" => Attachment.payload x y payload T.scheme.m
local notation "B'" => after L P K (2 * resetWidth κ w) (2 * resetWidth κ w) σ
local notation "C'" => (C ^ (900 + Y + 1))
local notation "I" => (Assembly.Snapshot.state src × Val x × Val y)

def oldBits (i : I) := i.1.val.data i.1.property.2 i.2.1 i.2.2

def output (i : I) :=
  ((E.result i.1).raw, (E.result i.1).data (E.fits i.1) i.2.1 i.2.2)

def Carries (v : ℕ) (L' : Set (Table F)) (n : ℕ) :=
  Computes F v L' ((Wiring).pair D) ((U).port x y payload)
    (fun i : I => (E.pending i.1, oldBits i)) E.output (fun _ => 1) n

set_option maxHeartbeats 500000 in
private theorem transform {v n : ℕ} {W : Set (Table F)} (hg : gain t ≤ K)
    (net : Computes F v W (src).port ((U).port x y payload)
      (fun i : I => (src).encode i.1 i.2.1 i.2.2) E.output
      (fun i => (E.query i.1).sweep_weight) n) :
    Transforms F v W src (interim A N k' (copies t B) L u z payload 3 C' B') n := by
  let Y' := interim A (raw R T L u t z Δ C B r).sweep k' (copies t B) L u z payload 3 C' B'
  let dest (i : (src).state) : Y'.state :=
    Subtype.mk (E.result i) (And.intro (And.intro (E.preserved i hg) (E.spare i)) (E.fits i))
  refine send (X := src) (Y := Y') dest (fun i => (E.query i).sweep_weight) ?_ ?_
  · intro i a b
    exact E.eval i a b
  · exact net

theorem controller {v : ℕ} (hu : 3 ≤ v) (hw : width R A L u t z Δ C B r ≤ v)
    (lo : 1 ≤ T.scheme.m) (hi : T.scheme.m + T.scheme.d ≤ p.w) (end' : (N).scheme.m + (N).scheme.d ≤ p.w)
    (hg : gain t ≤ K) (fit : A.shrinkWidth N k' (copies t B) ≤ v) :
    ∃ labels : Finset (Table F), labels.card ≤ 18 ∧ ∀ {W : Set (Table F)} {n : ℕ},
      (labels : Set _) ⊆ W → E.Carries v W n →
      Transforms F v W src (frame (A.shrink N k' (copies t B)) L u z payload 3 C' B')
        (runCost R A L u t z Δ C B r payload p + n) := by
  obtain ⟨old, hcard, net⟩ := E.supply hu hw lo hi end'
  let gate := A.shrinkGate N k' (copies t B)
  refine ⟨insert gate old, (Finset.card_insert_le ..).trans (by omega), ?_⟩
  intro W n include' ship
  have inc : (old : Set (Table F)) ⊆ W := fun _ hx => include' (Finset.mem_insert_of_mem hx)
  have first := raise net inc
  have keep := Computes.of_map (x := fun i : I => oldBits i) (L := W) (Map.circuit hu (Circuit.id F D))
    (fun _ => rfl)
  have run := ((first.restrict Prod.fst).par keep).comp ship
  simp only [mul_one, Function.comp_apply] at run
  have lift := transform E hg run
  have all := lift.comp (Contraction.shrink hu fit (include' (Finset.mem_insert_self ..)))
  exact all.mono (by unfold runCost next; omega)

end Choice
end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Width of a local reset decision -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly Assembly.History.Reset Case Coloring

variable {F : Type} [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B

theorem height_short : Short (fun i : I => i.height) := levels.short

theorem data_short : Short (fun i : I => (Tile.data i.T).width) := by
  refine (Case.bits.add counters).mono fun i => ?_
  rw [Format.width_pair, Format.width_addr, Format.width_addr]

theorem walks_bound : Short (fun i : I => 2 ^ ((i.T.scheme.d + 1) * depth d B i)) := by
  have h : Short (fun i : I => 2 ^ (i.n + 8)) := tiles.short.exp_add (short_const (2 ^ 8))
  refine (h.pow (d + 1)).mono fun i => ?_
  rw [← pow_mul, mul_comm (i.n + 8)]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.add_le_add_right i.h.degree 1))

theorem mask_bound : Short (fun i : I => (Tile.coincides i.T.scheme.d (depth d B i)).width) := by
  refine ((walks_bound (F := F) d B).mul (walks_bound d B)).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec, Format.width_bit, mul_one]

theorem stats_bound : Short (fun i : I => (i.T.Statistics (keyBits d B i)).width) := by
  have hc : Short (fun i : I => i.T.CountBits) :=
    (spans.short.of_exp.add (short_const 1)).add (height_short d B)
  refine ((((height_short d B).add (short_const 1)).clog).add (Case.slots.short.mul hc)).mono fun i => ?_
  rw [Format.width_pair, Format.width_vec, Format.width_addr, Format.width_addr]

theorem row_bound : Short (fun i : I => (Tile.row i.T i.a (keyBits d B i)).width) := by
  have hf : Short (fun i : I => (Group.Flags i.T.scheme.d).width) := by
    refine (Case.slots.short.mul (short_const 2)).mono fun i => ?_
    rw [Format.width_vec, Format.width_pair, Format.width_bit]
  refine ((stats_bound d B).add (hf.add (tiles.short.mul (data_short d B)))).mono fun i => ?_
  rw [Format.width_pair, Format.width_pair (Group.Flags _), Format.width_vec (i.T.scheme.h - i.a)]

theorem history_bound :
    Short (fun i : I => (Window.Walks (depth d B i) i.T.scheme.d (Tile.row i.T i.a (keyBits d B i))).width) := by
  refine ((walks_bound d B).mul (row_bound d B)).mono fun i => ?_
  rw [Format.width_vec]

theorem sample_bound : Short (fun i : I =>
    (Tile.sample i.T i.a (keyBits d B i) (depth d B i) (shift P Δ d B i)).width) := by
  have extra := (child_factor P Δ d B).short.of_exp
  have start := (short_const 1).add extra
  have end' := (mask_bound (F := F) d B).add (history_bound d B)
  refine (start.add (((height_short d B).add Case.groups.short).add end')).mono fun i => ?_
  simp only [Tile.sample, Format.width_pair, Format.width_addr]
  rfl

theorem answer_bound : Short (fun i : I => (Tile.output i.T (child P Δ C t d B i)).width) := by
  have h := child_bound P Δ C t d B
  have s : Short (fun i : I => (BatchDescent.Trail.pointer i.T.scheme 0).width) := by
    refine ((short_const 1).add ((height_short d B).add spans.short.of_exp)).mono fun i => ?_
    simp only [BatchDescent.Trail.pointer, Format.width_pair, Format.width_addr, i.h.single]
    rw [Format.width_bit, Format.width_addr 0, zero_add, zero_add]
  refine ((h.bits.add h.count).add (h.spans.mul s)).mono fun i => ?_
  rw [Format.width_pair, Format.width_pair, Format.width_addr, Format.width_addr,
    Format.width_vec, Format.width_vec, show (child P Δ C t d B i).scheme.k = 0 from rfl, pow_zero, one_mul]

theorem printWidth_bound : Short (fun i : I =>
    Tile.printWidth i.T (child P Δ C t d B i) (keyBits d B i) (depth d B i) (shift P Δ d B i)) :=
  (sample_bound P Δ d B).add (answer_bound P Δ C t d B)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Width of reset summaries over varying coefficient fields -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Coloring Template Case

variable {F : Type} [Field F] (Δ d B : ℕ)
local notation "I" => Case F 1 d B
local notation "K" => keyBits d B
abbrev digits (i : I) := indices i.T Δ i.z B
local notation "D" => digits Δ d B

theorem apply_bound : Cost (fun i : I => Mixing.applyCost i.height (History.Reset.Tile.data i.T) i.m) := by
  have h := (height_short (F := F) d B).add (data_short d B)
  have p := ((short_const 100).mul (((short_const 1).add h).pow 2)).add (((short_const 100).add h).pow 8)
  refine (Mixed.short Case.m (Short.block p)).mono fun i => ?_
  have hm : i.height ≤ i.m := (Nat.le_mul_of_pos_left _ (by decide : 0 < 4)).trans i.h.four
  simpa only [add_assoc] using BatchDescent.Restore.application i.height i.m (History.Reset.Tile.data i.T) hm

theorem indices_bound : Short (fun i : I => indices i.T Δ i.z B) := by
  let c := 4 * (Template.Encodes.margin Δ) ^ 2 + 4
  refine (((short_const c).add (height_short d B)).add
    ((short_const (B ^ 3)).add units.short)).mono fun i => ?_
  apply Nat.add_le_add_left
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add]
  calc
    _ ≤ (B ^ 3 + 1) * (1 + i.z) := by simp only [add_mul, mul_add, one_mul, mul_one]; omega
    _ ≤ _ := Nat.mul_le_mul Nat.lt_two_pow_self (Nat.le_pow_clog (by decide) _)

theorem keys_bound : Short (fun i : I => 2 ^ (K i)) :=
  ((height_short d B).add (short_const 1)).exp_clog

theorem cols_bound : Short (fun i : I => 2 ^ i.T.widthCols) :=
  Case.slots.short.exp_add (short_const (2 ^ 1))

theorem precision_bound : Short (fun i : I => Mixing.precision i.height (D i)) :=
  ((short_const 2).mul ((height_short d B).add (indices_bound Δ d B))).add (short_const 1)

theorem profile_arity : Short (fun i : I =>
    Mixing.arity i.T.widthCols i.height (K i) i.T.profileBits (D i)) := by
  have hh := indices_bound (F := F) Δ d B
  have hk := keys_bound (F := F) d B
  have a := (short_const 4).mul (precision_bound (F := F) Δ d B)
  have b := (Case.bits.add counters).add ((cols_bound d B).mul hh)
  have c := ((short_const 2).add hk.of_exp).add (hk.mul hh)
  refine (a.add (b.add c)).mono fun i => ?_
  unfold Mixing.arity profileBits digits
  omega

theorem counterBits : Short (fun i : I => i.T.CounterBits) :=
  spans.short.of_exp.add (short_const 1)

theorem headWidth : Short (fun i : I => (Mix.Heads i.T (K i)).width) := by
  refine ((cols_bound d B).mul ((short_const 1).add ((short_const 1).add (keys_bound d B).of_exp))).mono
    fun i => ?_
  simp only [Mix.Heads, Mixing.Header, Format.width_vec, Format.width_pair, Format.width_addr]
  exact le_rfl

theorem windowWidth : Short (fun i : I => (Mix.Window i.T (K i)).width) := by
  have s : Short (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.short
  have k := (keys_bound (F := F) d B).of_exp
  refine ((short_const 1).add ((s.mul (short_const 2)).add (k.add (s.mul k)))).mono fun i => ?_
  simp only [Mix.Window, Group.Flags, Mixing.Num, Format.width_vec, Format.width_pair, Format.width_addr]
  exact le_rfl

theorem summandWidth : Short (fun i : I => (i.T.Summand (D i)).width) := by
  refine ((indices_bound Δ d B).add (Case.slots.short.mul (counterBits d B))).mono fun i => ?_
  rw [Format.width_pair, Format.width_addr, Format.width_vec, Format.width_addr]

theorem summaryWidth : Short (fun i : I => Mix.arity i.T (K i) (indices i.T Δ i.z B)) := by
  have a := ((short_const 3).add (data_short (F := F) d B)).add (summandWidth Δ d B)
  have b := (a.add ((indices_bound Δ d B).add (height_short d B))).add (keys_bound d B).of_exp
  exact (((b.add (windowWidth d B)).add (headWidth d B)).add (Case.bits.add counters)).add
    (profile_arity Δ d B)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Paying for profile tests once and short arithmetic at each host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Coloring Case

variable {F : Type} [Field F] (Δ d B : ℕ)
local notation "I" => Case F 1 d B
local notation "K" => keyBits d B
local notation "D" => digits Δ d B

private theorem twice {g : I → ℕ} (hg : Long g) : Cost (fun i : I => 2 ^ i.height * (2 ^ i.height * g i)) := by
  refine (Mixed.long Case.m hg).mono fun i => ?_
  rw [← mul_assoc, ← pow_add]
  have hf : 4 * i.height ≤ i.m := i.h.four
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))

private theorem once {g : I → ℕ} (hg : Long g) : Cost (fun i : I => 2 ^ i.height * g i) :=
  (twice d B hg).mono fun _ => Nat.le_mul_of_pos_left _ (by positivity)

private theorem rowCost : Row (fun i : I => Mixing.rowCost i.height (K i) (D i)) := by
  have p := (precision_bound (F := F) Δ d B).block
  have a := (height_short (F := F) d B).block
  have k := (keys_bound (F := F) d B).block
  have g := (indices_bound (F := F) Δ d B).block
  let x (j) := block_const (k := F) (b := 1) (d := d) (B := B) j
  have hcorr : Row (fun i : I => Mixing.corrCost i.height (D i)) :=
    Block.blocks ((((x 1).add g).add p).add ((((x 2).mul a).add (x 3)).mul
      ((x 1).add ((x 4).mul p))) |>.add (((x 1).add p).add p))
  have small := Long.row (Block.long (k.mul g))
  have hp : Row (fun i : I => Mixing.pairCost i.height (K i) (Mixing.precision i.height (D i)) (D i)) := by
    refine ((p.blocks.add small).add (((Block.blocks (p.add g)).left k).scale 2)).mono fun i => ?_
    simp only [Mixing.pairCost, pow_add, mul_assoc]
    exact le_rfl
  have hword := p.add g
  have last := (Block.blocks (((x 1).add hword).add hword)).left k
  refine (((hcorr.add (small.scale 4)).add (hp.scale 4)).add last).mono fun i => ?_
  simp only [Mixing.rowCost, Mixing.wordLength, pow_add, mul_assoc]
  exact le_rfl

private theorem testCost {g : I → ℕ} (hg : Case.Block g) :
    Cost (fun i : I => Mixing.testCost (i.m + i.T.widthCols) (K i + i.height) (g i) i.height) := by
  have hk := (keys_bound (F := F) d B).block
  have he := (cols_bound (F := F) d B).block
  have l := hg.long.add (hosts.add he.long.of_exp)
  have hc : Cost (fun i : I => Mixing.collectCost (i.m + i.T.widthCols) (K i + i.height) (g i)) := by
    have a := ((block_const 3).mul hg).add (((block_const 100).add hg).pow 5)
    refine ((Block.blocks a).expand he |>.left hk).mono fun i => ?_
    unfold Mixing.collectCost
    rw [pow_add]
    exact le_of_eq (by ac_rfl)
  have hm : Cost (fun i : I => Mixing.maskCost (K i + i.height) i.height (g i + (i.m + i.T.widthCols))) := by
    refine (((once d B l).left hk).add (((twice d B l).left hk).scale (Install.localCost 1))).mono fun i => ?_
    unfold Mixing.maskCost
    rw [pow_add]
    exact le_of_eq (by ac_rfl)
  have t := (height_short (F := F) d B).long
  have h₁ := (twice d B (((long_const 100).add l).pow 5)).left hk
  have h₂ := once d B (((long_const 100).add (t.add (l.add (hk.long.of_exp.add t)))).pow 42)
  refine ((hc.add hm).add (h₁.add h₂)).mono fun i => ?_
  unfold Mixing.testCost
  rw [mul_add, pow_add]
  exact le_of_eq (by ac_rfl)

theorem profile_cost : Cost (fun i : I =>
    Mixing.extractionCost i.m i.T.widthCols i.height (K i) i.T.profileBits (D i)
      + Mixing.cost (i.m + i.T.widthCols) i.height (K i) (D i)) := by
  have hk := (keys_bound (F := F) d B).block
  have he := (cols_bound (F := F) d B).block
  have hg := (indices_bound (F := F) Δ d B).block
  have w := (precision_bound (F := F) Δ d B).block.add hg
  have cost : Cost (fun i : I => Mixing.cost (i.m + i.T.widthCols) i.height (K i) (D i)) :=
    ((rowCost Δ d B).expand he).add ((testCost d B w).scale 4)
  refine Mixed.add ?_ cost
  have a := (block_const 1).add (profile_arity (F := F) Δ d B).block
  have hd := Long.row (Block.long (hk.mul hg))
  have h₁ := (he.long.row.add ((block_const 1).blocks)).mul a
  have h₂ := (hd.left he).add (Block.blocks (he.mul hg))
  have h₃ := Row.expand (hg.blocks.add hd) he
  refine ((Row.hosts h₁).add (((Row.hosts h₂).add (h₃.scale 2)).scale 4)).mono fun i => ?_
  change _ + 4 * ((Format.vec i.m (.pair (Mixing.Matrix i.T.widthCols (K i) (D i))
    (Mixing.Matrix i.height i.T.widthCols (D i)))).width + 2 * (Mixing.Rows _ _ _ _).width) ≤ _
  simp only [Mixing.Matrix, Mixing.Rows, Mixing.Input, Mixing.Num, Format.width_vec, Format.width_pair,
    Format.width_addr, mul_one]
  exact le_rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Bounds for gathering a reset window -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly Assembly.History.Reset Case Coloring

variable {F : Type} [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "keys" => keyBits d B
local notation "walk" => depth d B

theorem pair_budget {A Z : I → Format}
    (h : Cost (fun i => (A i).width)) (k : Cost (fun i => (Z i).width)) :
    Cost (fun i => ((A i).pair (Z i)).width) :=
  (h.add k).mono fun _ => (Format.width_pair ..).le

private theorem vec_budget {A : I → Format} (h : Row (fun i => (A i).width)) :
    Cost (fun i => (Format.vec i.m (A i)).width) :=
  h.hosts.mono fun _ => (Format.width_vec ..).le

private theorem height_budget : Cost (fun i : I => (Format.addr i.height).width) := by
  refine (height_short (F := F) d B).long.row.cost.mono fun i => ?_
  rw [Format.width_addr]

theorem pair_bound : Cost (fun i : I => (Tile.pair i.T (keys i)).width) :=
  pair_budget d B Case.Child.parent.format (pair_budget d B (height_budget d B) (vec_budget d B (stats_bound d B).long.row))

theorem window_groups {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Fmt.groups i.m i.T.scheme.d i.a (A i)).width) := by
  have hc : Long (fun i : I => 2 ^ i.T.scheme.d * i.m) := Case.slots.short.long.mul hosts
  refine (Row.hosts (hc.row.add h.block.groups)).mono fun i => ?_
  exact (Fmt.width_rows ..).le

private theorem data_budget : Cost (fun i : I => (Mixing.Data i.height (Tile.data i.T) i.m).width) := by
  refine ((data_short (F := F) d B).block.blocks.hosts).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec]

private theorem groups_budget : Cost (fun i : I => (Mixing.Groups i.height i.a (Tile.data i.T) i.m).width) := by
  refine (Row.hosts (Block.groups (tiles.short.block.mul (data_short d B).block))).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec, Format.width_vec]

theorem packet_bound : Cost (fun i : I => Tile.packetCost i.T i.a (keys i)) := by
  have h₁ := pair_budget d B (height_budget (F := F) d B) (data_budget d B)
  have h₂ := window_groups d B (row_bound (F := F) d B)
  exact (((((pair_bound d B).scale 10).add (h₁.scale 2)).add (groups_budget d B)).add (h₂.scale 2)).add (apply_bound d B)

theorem maskCost_bound : Cost (fun i : I => Tile.maskCost i.T (walk i)) := by
  have h : Long (fun i : I => (100 + (i.m + 2 ^ ((i.T.scheme.d + 1) * walk i))) ^ 50) :=
    ((long_const 100).add (hosts.add (walks_bound d B).long)).pow 50
  exact Case.Child.parent.format.add (Mixed.long Case.m h)

local notation "dest" => child P Δ C t d B
local notation "growBy" => Reset.shift P Δ d B

theorem carry_blocks {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Format.vec (dest i).scheme.m (.vec (dest i).scheme.h (A i))).width) := by
  have H := child_bound P Δ C t d B
  refine (H.cost (H.layer h.block)).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec]

def readCost (i : I) := i.p.fee (i.m + i.T.scheme.d) (Tile.volume i.T (dest i) (keys i) (walk i))

theorem windowCost_bound : Cost (fun i : I =>
    Tile.windowCost i.T (dest i) (keys i) (walk i) (growBy i) (readCost P Δ C t d B i)) := by
  have hc : Cost (fun i : I => (Tile.gathered i.T (dest i) (keys i) (walk i)).width) :=
    pair_budget d B (pair_bound d B) (pair_budget d B (vec_budget d B (mask_bound d B).long.row)
      (window_groups d B (history_bound d B)))
  have hpre := (((pair_bound d B).add (packet_bound d B)).add (maskCost_bound d B)).add hc
  have hquery := carry_blocks P Δ C t d B (sample_bound P Δ d B)
  have hv : Row (fun i : I => Tile.volume i.T (dest i) (keys i) (walk i)) :=
    (history_bound d B).block.groups
  have hread := Case.Child.parent.read Case.slots.short hv
  have hsteps : Short (fun i : I => walk i + 1) :=
    (tiles.short.of_exp.add (short_const 8)).add (short_const 1)
  exact ((hpre.scale 100).add (hquery.scale 136)).add (hread.left hsteps.block)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end
