import OAI.LinearAlgebra.MatrixExponent.Assembly.FreezeInput.Retain
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Factor
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.ShortNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.OuterRows
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.ContractRates
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Issue
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.TraceNet

/-! # Fetching ordered labels after changing the host and block sets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Receive
open Coloring

abbrev Input (m d n l m' d' a p t : ℕ) (A : Format) :=
  Format.pair (Fmt.rows m d n (.addr l))
    (Fmt.bank m' d' (.vec a (A.pair (.vec t (.pair (.addr p) (.addr n))))))

abbrev Output (m d _n l m' d' a p t : ℕ) (A : Format) :=
  Fmt.bank m' d' (.pair (.vec p (.addr m))
    (.pair (.vec p (.vec d (.addr m))) (.vec a (A.pair (.vec t (.addr l))))))

def cost (m d n l m' d' a p t : ℕ) (A : Format) (v c : ℕ) :=
  gatherCost m d v c + 500 * ((Input m d n l m' d' a p t A).width +
    (Output m d n l m' d' a p t A).width + 2 ^ (m + d) * (2 ^ d * m + 2 ^ n * l) +
    2 ^ m' * (2 ^ p * (2 ^ n * l) + 2 ^ n * (100 + n + 2 ^ p + 2 ^ t + l) ^ 100))

variable {m d n l m' d' a p t : ℕ} {A : Format}
variable (parent : B m' → B m) (step : B p → Option (B d))

local notation "X" => Input m d n l m' d' a p t A
local notation "Y" => Output m d n l m' d' a p t A

def nav (x : (X).obj) (i : B m') (j : B p) : B m :=
  (step j).elim (parent i) (x.1 (parent i)).1

def receive (x : (X).obj) : (Y).obj := fun i =>
  ((x.2 i).1, nav parent step x i, fun j => (x.1 (nav parent step x i j)).1,
   fun k => (((x.2 i).2 k).1, fun b =>
     let e := ((x.2 i).2 k).2 b
     (x.1 (nav parent step x i e.1)).2 e.2))

local notation "R" => Format.pair (Format.vec d (Format.addr m)) (Format.vec n (Format.addr l))
local notation "G" => Format.vec m (Format.vec d R)
local notation "Side" => Fmt.bank m' d' (Format.pair (Format.vec p (Format.addr m))
  (Format.pair (Format.vec p (Format.vec d (Format.addr m))) (Format.vec a A)))
local notation "Ask" => Format.vec m' (Format.pair (Format.vec p (Format.vec n (Format.addr l)))
  (Format.vec a (Format.vec t (Format.pair (Format.addr p) (Format.addr n)))))
local notation "Got" => Format.vec m' (Format.vec a (Format.vec t (Format.addr l)))

private def prep (x : (X).obj) : ((X).pair (Fmt.bank m d R)).obj :=
  (x, fun i => ((x.1 i).1, x.1 i))

private def remote (x : ((X).pair G).obj) (i : B m') (j : B p) : (R).obj :=
  (step j).elim (x.1.1 (parent i)) (x.2 (parent i))

private def spread (x : ((X).pair G).obj) : ((Side).pair Ask).obj :=
  (fun i => ((x.1.2 i).1, nav parent step x.1 i, fun j => (remote parent step x i j).1,
     fun k => ((x.1.2 i).2 k).1),
   fun i => (fun j => (remote parent step x i j).2, fun k => ((x.1.2 i).2 k).2))

private def join (x : ((Side).pair Got).obj) : (Y).obj := fun i =>
  ((x.1 i).1, (x.1 i).2.1, (x.1 i).2.2.1, fun k => ((x.1 i).2.2.2 k, x.2 i k))

variable {F : Type} [Field F]

private theorem prep_net : Circuit F X ((X).pair (Fmt.bank m d R)) prep
    ((X).width + 2 * ((X).pair (Fmt.bank m d R)).width) := by
  let tap : ((X).pair (Fmt.bank m d R)).pins → (X).pins
    | .inl z => z
    | .inr (i, .inl z) => .inl (i, .inl z)
    | .inr (i, .inr z) => .inl (i, z)
  exact Circuit.project tap (by rintro x (z|⟨i, z|z⟩) <;> rfl)

private theorem spread_net : Circuit F ((X).pair G) ((Side).pair Ask) (spread parent step)
    (((X).pair G).width + 34 * ((Side).pair Ask).width) := by
  have tap (i : B m') (j : B p) (z : (R).pins) :
      ∃ w, ∀ x, (R).code (remote parent step x i j) z = ((X).pair G).code x w := by
    cases h : step j with
    | none => exact ⟨.inl (.inl (parent i, z)), fun _ => by rw [remote, h]; rfl⟩
    | some k => exact ⟨.inr (parent i, k, z), fun _ => by rw [remote, h]; rfl⟩
  apply Window.Tile.project_const
  rintro (⟨i, z|⟨j, z⟩|⟨j, z⟩|⟨k, z⟩⟩|⟨i, ⟨j, z⟩|⟨k, z⟩⟩)
  · exact .inl ⟨.inl (.inr (i, .inl z)), fun _ => rfl⟩
  · change (∃ w, ∀ x, (Format.addr m).code (nav parent step x.1 i j) z = ((X).pair G).code x w) ∨
      ∃ b, ∀ x : ((X).pair G).obj, (Format.addr m).code (nav parent step x.1 i j) z = b
    cases h : step j with
    | none => exact .inr ⟨(Format.addr m).code (parent i) z, fun _ => by rw [nav, h]; rfl⟩
    | some k => exact .inl ⟨.inl (.inl (parent i, .inl (k, z))), fun _ => by rw [nav, h]; rfl⟩
  · exact .inl (tap i j (.inl z))
  · exact .inl ⟨.inl (.inr (i, .inr (k, .inl z))), fun _ => rfl⟩
  · exact .inl (tap i j (.inr z))
  · exact .inl ⟨.inl (.inr (i, .inr (k, .inr z))), fun _ => rfl⟩

private theorem join_net : Circuit F ((Side).pair Got) Y join
    (((Side).pair Got).width + 2 * (Y).width) := by
  let tap : (Y).pins → ((Side).pair Got).pins
    | (i, .inl z) => .inl (i, .inl z)
    | (i, .inr (.inl z)) => .inl (i, .inr (.inl z))
    | (i, .inr (.inr (.inl z))) => .inl (i, .inr (.inr (.inl z)))
    | (i, .inr (.inr (.inr (k, .inl z)))) => .inl (i, .inr (.inr (.inr (k, z))))
    | (i, .inr (.inr (.inr (k, .inr z)))) => .inr (i, k, z)
  exact Circuit.project tap (by rintro x ⟨i, z|z|z|⟨k, z|z⟩⟩ <;> rfl)


variable {u v c : ℕ} {L : Set (Table F)} {I : Type*}

/-- Only the old graph needs to be reciprocal. Each old host sends its neighbor
list and block labels together. The fixed parent and step maps then place the
required lists at the new hosts before any block requests are resolved. -/
theorem run (hu : 3 ≤ u) (ha : a ≤ n) (ht : Access F u L (m + d) v c)
    (hv : 2 ^ d * m + 2 ^ n * l ≤ v) (x : I → (X).obj)
    (hx : ∀ i, Fmt.Reciprocal (.vec n (.addr l)) (x i).1) :
    Computes F u L X Y x (fun i => receive parent step (x i)) (fun _ => 1)
      (cost m d n l m' d' a p t A v c) := by
  have start := Computes.of_map (L := L) (x := x) (Map.circuit hu (prep_net (F := F))) (fun _ => rfl)
  have keep := Computes.of_map (L := L) (x := x) (Map.circuit hu (Circuit.id F X)) (fun _ => rfl)
  have move := gather_neighbors R hu ht (by simpa using hv)
    (fun i => (prep (x i)).2) hx
  let y (i : I) : ((X).pair G).obj := (x i, Fmt.gather R (prep (x i)).2)
  have pick (i : I) (j : B m') (k : B p) :
      remote parent step (y i) j k = (x i).1 (nav parent step (x i) j k) := by
    unfold remote nav
    cases step k <;> rfl
  have read := Circuit.map (fun _ : B m' => _) (fun _ => local_read F n a p t l ha)
  have endNet := ((spread_net (F := F) (d' := d') (A := A) parent step).comp
    ((Circuit.id F Side).par read)).comp (join_net (n := n))
  have stop := Computes.of_map (L := L) (x := y) (y := fun i => receive parent step (x i))
    (Map.circuit hu endNet) (by
      intro i
      simp only [Function.comp_apply, Prod.map, id_eq, spread, pick]
      rfl)
  have done := (start.comp (keep.par move)).comp stop
  simp only [mul_one] at done
  refine done.mono ?_
  have hb : (Fmt.bank m d R).width ≤ 2 * (X).width := by
    simp only [Input, Fmt.bank, Fmt.rows, Format.width_pair, Format.width_vec, mul_add]
    omega
  have hg : (G).width = 2 ^ (m + d) * (2 ^ d * m + 2 ^ n * l) := by
    simp only [Format.width_pair, Format.width_vec, Format.width_addr, pow_add, mul_assoc]
  have hs : (Side).width + (Got).width = (Y).width := by
    simp only [Output, Fmt.bank, Format.width_pair, Format.width_vec, mul_add]
    omega
  have hq : (Ask).width ≤ 2 ^ m' * (2 ^ p * (2 ^ n * l)) + (X).width := by
    simp only [Input, Fmt.bank, Format.width_pair, Format.width_vec, Format.width_addr, mul_add]
    omega
  unfold cost
  rw [Format.width_pair X (Fmt.bank m d R), Format.width_pair X G, Format.width_pair Side Ask,
    Format.width_pair Side Got, mul_add (2 ^ m')]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Receive
end

/-! # Wiring the requests for old attachment labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring
open scoped Classical

variable {F : Type} {D Y : Template F} (A : Attachment D) (Y : Template F) (k p : ℕ)

abbrev Requests := A.format.pair
  (Y.format.pair (.vec Y.scheme.m (.vec Y.scheme.h (.pair .bit (A.orders Y k p)))))

abbrev Inputs := Receive.Input D.scheme.m D.scheme.d D.scheme.h A.ℓ
  Y.scheme.m Y.scheme.d Y.scheme.h p (depth Y k) (A.ticket Y k p)

variable {A Y k p}

private theorem question_pin (self : B p) (b : (ask (D := D) Y k p).pins) :
    (∃ w, ∀ x, (ask (D := D) Y k p).code (A.question self x) b =
      (A.ticket Y k p).code x w) ∨
    ∃ c, ∀ x : (A.ticket Y k p).obj, (ask (D := D) Y k p).code (A.question self x) b = c := by
  let H := Format.pair (.addr p) (.addr D.scheme.h)
  obtain ⟨i, z⟩ := b
  change (∃ w, ∀ x, H.code (A.question self x i) z = (A.ticket Y k p).code x w) ∨
    ∃ c, ∀ x : (A.ticket Y k p).obj, H.code (A.question self x i) z = c
  by_cases hi : ∃ j, request Y k j = i
  · obtain ⟨l|l, rfl⟩ := hi
    · simp only [question, (request Y k).injective.extend_apply, Sum.elim_inl]
      rcases z with z|z
      · exact .inl ⟨.inr (.inr (.inl (l, .inr (.inl z)))), fun _ => rfl⟩
      · exact .inl ⟨.inr (.inr (.inl (l, .inr (.inr (.inl z))))), fun _ => rfl⟩
    · simp only [question, (request Y k).injective.extend_apply, Sum.elim_inr]
      rcases z with z|z
      · exact .inr ⟨(Format.addr p).code self z, fun _ => rfl⟩
      · exact .inl ⟨.inr (.inr (.inr (l, .inr (.inl z)))), fun _ => rfl⟩
  · exact .inr ⟨H.code (self, 0) z, fun _ => by rw [question, Function.extend_apply' _ _ _ hi]⟩

namespace Query
variable (q : Query A Y k p) (self : B p)

def requests : (A.Requests Y k p).obj := (q.old, q.fresh, fun i j => (q.ticketAt i j).2)

def inputs : (A.Inputs Y k p).obj :=
  (A.rows q.old, fun i => (Y.nav q.fresh i, fun j => (q.ticketAt i j, A.question self (q.ticketAt i j))))

theorem inputs_net [Field F] {u : ℕ} {L : Set (Table F)} {I : Type*}
    (hu : 3 ≤ u) (q : I → Query A Y k p) (self : B p) :
    Computes F u L (A.Requests Y k p) (A.Inputs Y k p)
      (fun i => (q i).requests) (fun i => (q i).inputs self) (fun _ => 1)
      (4 * ((A.Requests Y k p).width + 34 * (A.Inputs Y k p).width)) := by
  let X := A.Requests Y k p
  let Z := A.Inputs Y k p
  let T := A.ticket Y k p
  let pull (i : B Y.scheme.m) (j : B Y.scheme.h) (x : X.obj) : T.obj :=
    ((x.2.1.1 i).2 j, x.2.2 i j)
  let f (x : X.obj) : Z.obj :=
    (A.rows x.1, fun i => (Y.nav x.2.1 i, fun j => (pull i j x, A.question self (pull i j x))))
  have ht (i : B Y.scheme.m) (j : B Y.scheme.h) (z : T.pins) :
      ∃ w, ∀ x, T.code (pull i j x) z = X.code x w := by
    rcases z with z|z
    · exact ⟨.inr (.inl (.inl (i, .inr (j, z)))), fun _ => rfl⟩
    · exact ⟨.inr (.inr (i, j, z)), fun _ => rfl⟩
  have net : Circuit F X Z f (X.width + 34 * Z.width) := by
    apply Window.Tile.project_const
    rintro (⟨i, z|z⟩ | ⟨i, z|⟨j, z|z⟩⟩)
    · exact .inl ⟨.inl (.inl (.inl (i, .inl z))), fun _ => rfl⟩
    · exact .inl ⟨.inl (.inr (i, z)), fun _ => rfl⟩
    · exact .inl ⟨.inr (.inl (.inl (i, .inl z))), fun _ => rfl⟩
    · exact .inl (ht i j z)
    · rcases question_pin (A := A) (Y := Y) (k := k) self z with ⟨w, hw⟩ | ⟨b, hb⟩
      · obtain ⟨l, hl⟩ := ht i j w
        exact .inl ⟨l, fun x => (hw (pull i j x)).trans (hl x)⟩
      · exact .inr ⟨b, fun x => hb (pull i j x)⟩
  exact Computes.of_map (Map.circuit hu net) (fun _ => rfl)

end Query
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Computing the inspection records for a family of attachment queries -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring

variable {F : Type} {D Y : Template F} (A : Attachment D) (Y : Template F) (k p : ℕ)

def reviewCost (v c v' c' : ℕ) :=
  4 * ((A.Requests Y k p).width + 34 * (A.Inputs Y k p).width) +
  Receive.cost D.scheme.m D.scheme.d D.scheme.h A.ℓ Y.scheme.m Y.scheme.d Y.scheme.h p
    (depth Y k) (A.ticket Y k p) v c +
  Inspect.cost D.scheme.m D.scheme.d Y.scheme.m Y.scheme.d p Y.scheme.h (A.bundle Y k p) v' c'

variable {A Y k p} [Field F] {u v c v' c' : ℕ} {L : Set (Table F)} {I : Type*}

/-- The two exchanges use the old and new host graphs respectively.
The parent map and the choice of steps are fixed across the family. -/
theorem Query.review_net (hu : 3 ≤ u) (ha : Y.scheme.h ≤ D.scheme.h)
    (ht : Access F u L (D.scheme.m + D.scheme.d) v c)
    (hv : 2 ^ D.scheme.d * D.scheme.m + 2 ^ D.scheme.h * A.ℓ ≤ v)
    (ht' : Access F u L (Y.scheme.m + Y.scheme.d) v' c')
    (hv' : (Inspect.Packet D.scheme.m D.scheme.d p Y.scheme.h (A.bundle Y k p)).width ≤ v')
    (parent : B Y.scheme.m → B D.scheme.m) (step : B p → Option (B D.scheme.d))
    (Q : I → Query A Y k p) (self : B p)
    (nav : ∀ i j l, (Q i).M.nav j l = (step l).elim (parent j) (D.nav (Q i).old.1 (parent j)))
    (oldRecip : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (Q i).old.1.1)
    (newRecip : ∀ i, Fmt.Reciprocal (.vec Y.scheme.h (.addr Y.scheme.ℓ)) (Q i).fresh.1) :
    Computes F u L (A.Requests Y k p) (.vec Y.scheme.m (.vec Y.scheme.h (A.Review Y k p)))
      (fun i => (Q i).requests) (fun i => (Q i).review self) (fun _ => 1)
      (A.reviewCost Y k p v c v' c') := by
  let X i := (Q i).inputs self
  let Z i := Receive.receive parent step (X i)
  have pre := Query.inputs_net (L := L) hu Q self
  have fetch := Receive.run parent step hu ha ht hv X oldRecip
  have post := Inspect.run hu ht' hv' Z newRecip
  have he (i : I) : Inspect.view (Z i) = (Q i).review self := by
    have hn : (Q i).M.nav = Receive.nav parent step (X i) :=
      funext fun j => funext fun l => nav i j l
    funext j l
    unfold Query.review Query.received
    rw [hn]
    rfl
  have done := (pre.comp fetch).comp post
  simp only [he, mul_one] at done
  exact done

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# Rebuilding the attached network with one short dictionary

The same dictionary reads the two local records and the shared
address mask at each occurrence. Its arity does not include the
width of a global host name.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (Y : Template F) (k p : ℕ)

def rebuildWidth := (A.Review Y k p).width + (A.transport Y k).ℓ

def rebuildLabel (self : B p) (x : (A.Review Y k p).obj) : B (A.transport Y k).ℓ :=
  (A.record Y k).serial (rebuild self x)

def rebuildGate (self : B p) :=
  weightTable (A := A.Review Y k p) (D := .addr (A.transport Y k).ℓ)
    (A.rebuildLabel Y k p self) (fun _ => (1 : F))

def rebuildCost (v c v' c' : ℕ) :=
  24 * (A.Requests Y k p).width + 8 * Y.format.width + A.reviewCost Y k p v c v' c' +
    2 ^ Y.scheme.m * (2 ^ Y.scheme.h * (1 + A.rebuildWidth Y k p))

theorem rebuild_arity (self : B p) : wd (A.rebuildGate Y k p self).1 + wd (A.rebuildGate Y k p self).2.1 =
    A.rebuildWidth Y k p := by
  simp only [rebuildGate, weightTable, lookup, wd_word, rebuildWidth]
  rw [Format.width_addr]

variable {A Y k p}

abbrev Query.result (q : Query A Y k p) := q.R.write q.old q.fresh q.active (q.R.links q.old q.fresh q.M)

theorem Query.rebuild_net {u v c v' c' : ℕ} {L : Set (Table F)} {I : Type*}
    (hu : 3 ≤ u) (ha : Y.scheme.h ≤ D.scheme.h)
    (ht : Access F u L (D.scheme.m + D.scheme.d) v c)
    (hv : 2 ^ D.scheme.d * D.scheme.m + 2 ^ D.scheme.h * A.ℓ ≤ v)
    (ht' : Access F u L (Y.scheme.m + Y.scheme.d) v' c')
    (hv' : (Inspect.Packet D.scheme.m D.scheme.d p Y.scheme.h (A.bundle Y k p)).width ≤ v')
    (parent : B Y.scheme.m → B D.scheme.m) (step : B p → Option (B D.scheme.d))
    (Q : I → Query A Y k p) (self : B p)
    (nav : ∀ i j l, (Q i).M.nav j l = (step l).elim (parent j) (D.nav (Q i).old.1 (parent j)))
    (oldRecip : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (Q i).old.1.1)
    (newRecip : ∀ i, Fmt.Reciprocal (.vec Y.scheme.h (.addr Y.scheme.ℓ)) (Q i).fresh.1)
    (back : ∀ i j, (Q i).M.nav j self = (Q i).R.parent j)
    (fit : A.rebuildWidth Y k p ≤ u) (allow : A.rebuildGate Y k p self ∈ L) :
    Computes F u L (A.Requests Y k p) (A.transport Y k).format
      (fun i => (Q i).requests) (fun i => (Q i).result) (fun _ => 1)
      (A.rebuildCost Y k p v c v' c') := by
  let X := A.Requests Y k p
  let E := A.Review Y k p
  let H := Format.addr (A.transport Y k).ℓ
  let μ := A.rebuildLabel Y k p self
  have hwidth : E.width + H.width = A.rebuildWidth Y k p := by rw [show H.width = _ from Format.width_addr _]; rfl
  have localMap : Map F u L E H μ (1 + A.rebuildWidth Y k p) := by
    rw [← hwidth, ← add_assoc]
    exact Kernel.lookup (hwidth.le.trans fit) allow
  have inspect := review_net hu ha ht hv ht' hv' parent step Q self nav oldRecip newRecip
  have decode := Map.vec (t := Y.scheme.m) _ (fun _ =>
    Map.vec (t := Y.scheme.h) _ (fun _ => localMap))
  have codes := inspect.comp (Computes.of_map decode (y := fun i => (Q i).result.2) (by
    intro i
    funext j t
    exact congrArg (A.record Y k).serial ((Q i).rebuild_eq self (back i) j t)))
  have keep : Circuit F X Y.format (fun r => r.2.1) (X.width + 2 * Y.format.width) :=
    Circuit.project (Sum.inr ∘ Sum.inl) (fun _ _ => rfl)
  have view := Computes.of_map (x := fun i => (Q i).requests) (L := L) (Map.circuit hu keep) (fun _ => rfl)
  have h := view.pair hu codes
  simp only [mul_one] at h
  exact h.mono (by unfold rebuildCost; unfold X; omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Withdrawing core scalars while preserving attachment requests -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Coloring Packing
open scoped Classical

variable {F : Type} [Field F]

namespace BatchDescent.Trail.Move
variable {S U : Scheme F} {k : ℕ}

abbrev sweep (M : Move S U k) : Move S U.sweep k := ⟨M.nav, M.read⟩

theorem Agrees.sweep {x y : Wire} {G H : Diagram F x y}
    {r : S.format.obj} {s : U.format.obj} {M : Move S U k}
    {p : S.Presentation r G} {q : U.Presentation s H}
    (h : M.Agrees p q) : M.sweep.Agrees p q.sweep := by
  have hb (j : slots x ⊕ slots y) : (q.sweep.boundary j).val = (q.boundary j).val := by
    cases j with
    | inl i => exact q.sweep_end (.inl (.inl i))
    | inr i => exact q.sweep_end (.inr (.inl i))
  constructor
  · intro j
    rw [hb]
    exact h.mapped j
  · intro w hw
    obtain ⟨j, hj⟩ := h.active w hw
    exact ⟨j, by rw [hb]; exact hj⟩

end BatchDescent.Trail.Move

namespace Assembly.Attachment
variable {D Y : Template F} {A : Attachment D} {k p : ℕ}

namespace Relocation

abbrev sweep (R : A.Relocation Y k) : A.Relocation Y.sweep k := ⟨R.parent, R.prev⟩

variable {T : Type} [Fintype T] {x y a b : Wire} {u v : ℕ} {L : Fringe x y T}
  {G : HostNet F L D.scheme.h u} {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y}
  {r : A.format.obj} {s : Y.format.obj} {q : A.Encloses r G Z} {e : Y.Encodes s H}

theorem Moves.sweep {R : A.Relocation Y k} {slot : T → B k} (h : R.Moves q e slot) :
    R.sweep.Moves q e.sweep slot := ⟨h.positive, h.iff⟩

theorem WriteActive.sweep {live : B Y.scheme.m → B Y.scheme.h → Bool} (h : WriteActive e live) :
    WriteActive e.sweep live := h

end Relocation

abbrev Query.sweep (q : A.Query Y k p) : A.Query Y.sweep k p :=
  ⟨q.R.sweep, q.M.sweep, q.old, q.fresh, q.active⟩

def Query.sweep_weight (q : A.Query Y k p) : F := Fmt.weight Y.scheme.scalar q.fresh.1

def sweepCost (A : Attachment D) (Y : Template F) (k p : ℕ) :=
  4 * A.format.width +
    (updateCost Y.scheme.m Y.scheme.d Y.scheme.h (.addr Y.scheme.ℓ) (.addr Y.scheme.ℓ) +
      4 * (Format.vec Y.scheme.m Y.header).width +
      4 * (Format.vec Y.scheme.m (.vec Y.scheme.h (.pair .bit (A.orders Y k p)))).width)

theorem Query.sweep_net {u : ℕ} {L : Set (Table F)} {I : Type*}
    (q : I → A.Query Y k p) (hu : 3 ≤ u) (ha : 2 * Y.scheme.ℓ ≤ u)
    (hl : BatchDescent.Snapshot.sweepTable Y ∈ L) :
    Computes F u L (A.Requests Y k p) (A.Requests Y.sweep k p)
      (fun i => (q i).requests) (fun i => (q i).sweep.requests)
      (fun i => (q i).sweep_weight) (A.sweepCost Y k p) := by
  let B := Format.addr Y.scheme.ℓ
  let V := Format.vec Y.scheme.m (.vec Y.scheme.h (.pair .bit (A.orders Y k p)))
  have step := update (m := Y.scheme.m) (d := Y.scheme.d) (h := Y.scheme.h) (A := B) (D := B)
    id Y.scheme.scalar hu (by simpa [B, two_mul] using ha) hl
  have keep (X : Format) := Action.of_map (Map.circuit (L := L) hu (Circuit.id F X))
  have run := (keep A.format).par ((step.par (keep (.vec Y.scheme.m Y.header))).par (keep V))
  simp only [one_mul, mul_one] at run
  exact Computes.of_action run (fun _ => rfl) (fun _ => rfl)

end Assembly.Attachment
end OAI.LinearAlgebra.MatrixExponent
end

/-! # Applying a validated move and core sweep to an attached frame -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Query
open Packing Coloring BatchDescent
open scoped Classical

variable {F : Type} [Field F] {T : Type} [Fintype T] {x y a b : Wire} {D Y : Template F} {A : Attachment D}
  {k m u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u} {H : HostNet F L Y.scheme.h v}
  {Z : Border F T a b x y} (q : A.Query Y k m)
  {old : A.Encloses q.old G Z} {fresh : Y.Encodes q.fresh H} {slot : T → B k}
  (h : q.R.Moves old fresh slot) (ok : Relocation.WriteActive fresh q.active)
  (move : q.M.Agrees old.core.post.toPresentation fresh.post.toPresentation) (full : Y.full = true)

def apply : (A.transport Y.sweep k).Data a b v :=
  ⟨T, x, y, L, H.sweep, Z, q.sweep.result, h.sweep.enclose ok.sweep move.sweep full⟩

theorem fits {height : ℕ} (fit : A.scheme.Fits (A.rows q.old) (volume a b D.scheme.m) height) :
    (q.apply h ok move full).Fits height :=
  h.sweep.fits ok.sweep move.sweep full fit

theorem floor {w : ℕ} (low : ∀ j, w ≤ fresh.post.toPresentation.borderWidth j) :
    ∀ j, w ≤ (q.apply h ok move full).q.core.post.toPresentation.borderWidth j := low

theorem spare {δ : ℝ} {N : ℕ} (hd : 0 < δ) (charge : ∀ t, δ ≤ L.scale * L.charge t)
    (bound : ∀ v i, H.load v i ≤ (N : ℝ) * δ) :
    A.Sparse Y.sweep k N (q.apply h ok move full).raw :=
  q.sweep.R.sparse (q.apply h ok move full).q hd charge bound

theorem exterior (j : slots a ⊕ slots b) :
    let v := ((q.apply h ok move full).q.pres.boundary j).val
    let w := (old.pres.boundary j).val
    q.sweep.R.kept q.old v.1.1 = some w.1.1 ∧ v.1.2 = A.outer Y.sweep w.1.2 ∧ v.2.val = w.2.val :=
  h.sweep.exterior_pin ok.sweep move.sweep full j

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Query
end

/-! # Control and contraction share the same three cost scales -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open Coloring

private theorem localWidth : Short (fun i => Prepare.arity i.S i.w) := by
  have base : Short Size.T := BatchDescent.Phase.Poly.of_le Size.t_two fun _ => le_rfl
  refine ((num 64).short.mul base).mono fun i => ?_
  have h := arity_le i
  unfold arity Dictionary.arity at h
  omega

private theorem key : Short (fun i => (Prepare.key i.S).width) :=
  localWidth.mono fun _ => Nat.le_add_right ..
private theorem answer : Short (fun i => (Prepare.answer i.S i.w).width) :=
  localWidth.mono fun _ => Nat.le_add_left ..

private theorem pair {A D : Size → Format}
    (a : Work (fun i => (A i).width)) (b : Work (fun i => (D i).width)) :
    Work (fun i => ((A i).pair (D i)).width) :=
  (a.add b).mono fun _ => (Format.width_pair ..).le

private theorem grid {A : Size → Format} (h : Short (fun i => (A i).width)) :
    Work (fun i => (Format.vec i.S.m (.vec i.n (A i))).width) :=
  (Work.spans h).mono fun _ => by rw [Format.width_vec, Format.width_vec, Size.spans, mul_assoc]

private theorem bothWidths : Work (fun i => (Prepare.both i.S i.w).width) := by
  have split (A D : Format) : A.width ≤ (A.pair (A.pair D)).width ∧
      D.width ≤ (A.pair (A.pair D)).width := by simp only [Format.width_pair]; omega
  have left : Short (fun i => (SpanPlan.header i.w i.p i.n).width) :=
    answer.mono fun _ => (split _ _).1
  have right : Short (fun i => (SpanPlan.header i.w 0 i.n).width) :=
    answer.mono fun _ => (split _ _).2
  exact pair (pair names (pair (grid left) (grid left))) (pair (grid left) (grid right))

private theorem traffic : Work (fun i => linkCost i.S) := by
  have f := ((num 100).long.add (m.add links.long)).pow 24
  exact format.add ((Work.hosts f).scale (num 512))

private theorem prepare : Work (fun i => Prepare.cost i.S i.w (linkCost i.S)) := by
  have mask : Work (fun i => (Flags i.S).width) :=
    (Work.hosts neighbors.long).mono fun _ => by
      rw [Flags, Format.width_vec, Format.width_vec, Format.width_bit, mul_one]
  have src := (pair format (pair names mask)).add ((pair names (grid key)).scale (num 34))
  have q := (((format.scale (num 5)).add format).add traffic).add src
  have slot := Work.spans (((num 1).short.add key).add answer)
  refine ((q.scale (num 4)).add ((names.scale (num 4)).add slot)).mono fun i => ?_
  unfold Prepare.cost Size.spans
  rw [mul_assoc i.hosts]

theorem order : Work orderCost := by
  have stage := ((pair names (grid answer)).add (bothWidths.scale (num 2))).add (emit.add project)
  exact ((format.scale (num 20)).add (prepare.add (stage.scale (num 4)))).add header

theorem terminal : Work (fun i => 8 * i.S.format.width + orderCost i + i.price) :=
  ((format.scale (num 8)).add order).add price

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end

/-! # Checking internal and exterior wires when contracting the terminal network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj} {t V V' k' w z : ℕ}
  {peer : B (S.m + z) → B (S.m + z)} {send take : SpanPlan.Entries S.m w z S.spanRows}
  {b : SpanPlan.Entries S.m w 0 S.spanRows}

local notation "I" => PeerLayout.S S.m V (height S t) S.m V (height S t) (2 ^ z)
local notation "O" => PeerLayout.S S.m V (height S t) S.m V' k' 1
local notation "P" => Payload.Script.decode le_rfl (SpanPlan.emit peer (send, take))
local notation "Q" => Payload.Script.decode le_rfl (Outer.script (send, b))

theorem shipment (h : Fits S r V t) (hx : S.Fits r V' k') (ok : S.Proper r) (hn : Neutral S r)
    (hw : height S t < w) (hw' : k' < w) (inner : Inner S r t peer send take)
    (hb : ∀ i j, (b i j).2.1.val = S.extent r i j) (ho : ∀ i j, (b i j).2.2 = j)
    (x : S.exposed r → Bool) :
    ∑ a, ((I).kernel F (P, a) a * (O).kernel F (Q, a) (S.store r hx x)) * localValue h a = S.eval r x := by
  apply contract h hn x
  · intro a ha
    have hh : (I).Carries P a a := by
      by_contra he
      simp only [Channels.kernel, ite_eq_right he, zero_mul, ne_eq, not_true_eq_false] at ha
    exact ((inner.carries ok h hw a).mp hh).1
  · intro v
    have hi := inner.carries_store ok h hw v
    have he := Outer.correct h hx send b hw hw' inner.lengths hb ho v x
    simp only [Channels.kernel, hi, he, Scheme.Agrees]
    by_cases hext : ∀ i : S.exposed r, v i.val = x i
    · simp [hext]
    · simp only [hext, false_and, ite_false, mul_zero]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-! # Evaluating the generated command on a valid presentation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj} {V t w V' k : ℕ}

theorem value_orders (h : Fits S r V t) (hx : S.Fits r V' k)
    (hp : S.Proper r) (hr : Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) r)
    (hn : Neutral S r) (hw : height S t < w) (hk : k < w) (x : S.exposed r → Bool) :
    value S V t V' k (S.d + 1) w S.spanRows (orders S V t w r) (S.store r hx x) = S.eval r x := by
  have ht : t < w := (by unfold height at hw; omega)
  have he := shipment h hx hp hn hw hk (inner_plan S r hp hr ht) (outer_length S r h ht)
    (fun _ _ => rfl) x
  unfold value orders
  simp only [Header.correct h, Dictionary.weight_encode]
  exact he

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# Frozen station addresses in a grouping

A frozen station stays in its own colony. The old within-group block
suffix and the old seat identify the station even if its colony has
many blocks. Zero remains reserved for the new core station.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Packing Coloring History
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
    {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h} {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ}
    {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (t : D.Branch P a ha b k cost Δ C z σ hu) (M : Book D.scheme P z hz) (e cap : ℕ) (K : Template.Meter)

local notation "n" => (D.scheme.h - a)
local notation "Y" => D.after a Δ C M e cap K

def lookupSeat (g : B a) (iv : B (n + 1)) (live : Bool) (tags : B n → B (n + 1))
    (l : B (n + A.k)) : Option (B D.scheme.h × B A.k) :=
  let p := Match.rowIndex n A.k l
  if live = true ∧ tags p.1 = iv then some (D.position a ha g p.1, p.2) else none

def grouped : A.Relocation Y (n + A.k) where
  parent := D.parent a
  prev i j := A.lookupSeat (ha := ha) j (Match.rowIndex _ _ i).2 (D.childLive a t.r i)
    (D.tags a ha k cost Δ C t.r (D.parent a i) j)

def newSlot (s : t.T → B A.k) (i : t.T) : B (n + A.k) :=
  (Match.rowIndex n A.k).symm (cellIndex _ (suffix a (t.G.park i).2), s i)

theorem slot_pos (s : t.T → B A.k) (hs : ∀ i, s i ≠ 0) (i : t.T) : A.newSlot t s i ≠ 0 := by
  intro he
  have hf : (Match.rowIndex n A.k 0).2 = 0 := by apply Fin.ext; simp [Match.rowIndex]
  have hit := congrArg (fun w => (Match.rowIndex n A.k w).2) he
  rw [newSlot, Equiv.apply_symm_apply, hf] at hit
  exact hs i hit

omit [Field F] in
private theorem position_iff (i : B a) (j : B n) (t : Cell D.scheme.h) :
    D.position a ha i j = cellIndex _ t ↔
      i = cellIndex _ (ancestor ha t) ∧ j = cellIndex _ (suffix a t) := by
  unfold Template.position
  rw [(cellIndex _).injective.eq_iff, Equiv.symm_apply_eq]
  change (_, _) = (ancestor ha t, suffix a t) ↔ _
  rw [Prod.mk.injEq, Equiv.symm_apply_eq, Equiv.symm_apply_eq]

private theorem sameHost (i : t.T) :
    let w := splitAddr t.G.V a ha (t.G.park i)
    t.s.group.route t.s.matching (t.s.group.layout t.s.matching P t.i) w.1 w.2 =
      t.s.group.here w.1 w.2 := by
  intro w
  rcases t.s.group.route_cases t.s.matching (t.s.group.layout t.s.matching P t.i) w.1 w.2 with h|⟨f, h, _⟩
  · exact h
  · have hfixed : (t.G.regroup a ha).frozen w.1 := t.G.kept i
    exact (((t.G.regroup a ha).core f.val).1 (h.symm ▸ hfixed)).elim

variable (hc : Δ ≤ C)

theorem frozen_address (i : t.T) :
    let w := t.G.park i
    let g := ancestor ha w.2
    let j := suffix a w.2
    (t.layout hc).park i = ((w.1, (t.s.group.here (w.1, g) j).2), g) := by
  intro w g j
  exact congrArg (t.G.project a ha Δ C hc).place (sameHost t i)

theorem back_iff (slot : t.T → B A.k) (i : t.T) (u : B (D.size a)) (g : B a) (l : B (n + A.k)) :
    (A.grouped t M e cap K).back (u, g, l) =
      some (t.p.post.host (t.G.park i).1, t.p.post.block (t.G.park i).2, slot i) ↔
    (u, g, l) = (Child.host t.p.post.host n ((t.layout hc).park i).1,
      cellIndex a ((t.layout hc).park i).2, A.newSlot t slot i) := by
  let w := t.G.park i
  let host := t.p.post.host w.1
  let block := cellIndex _ (ancestor ha w.2)
  let suf := cellIndex _ (suffix a w.2)
  let iv := (t.s.group.here (w.1, ancestor ha w.2) (suffix a w.2)).2
  let dest := Child.host t.p.post.host n (w.1, iv)
  let s := Match.rowIndex n A.k
  let r := Match.rowIndex D.scheme.m (n + 1)
  have he : r dest = (host, intervalCode n iv) := Child.host_parts _ _
  have ht : D.tags a ha k cost Δ C t.r host block suf = intervalCode n iv := t.s.tags _ _ _
  have hv : D.childLive a t.r dest = true := (D.child_live a t.p _).mpr ⟨_, rfl⟩
  rw [frozen_address t hc i, t.p.block]
  change Option.map (Prod.mk (r u).1)
    (if D.childLive a t.r u = true ∧ D.tags a ha k cost Δ C t.r (r u).1 g (s l).1 = (r u).2
     then some (D.position a ha g (s l).1, (s l).2) else none) =
      some (host, cellIndex _ w.2, slot i) ↔ (u, g, l) = (dest, block, s.symm (suf, slot i))
  constructor
  · intro h
    split_ifs at h with hh
    · obtain ⟨hu, hg, hslot⟩ := (by simpa only [Option.map_some, Option.some.injEq, Prod.mk.injEq] using h)
      obtain ⟨hg', hs'⟩ := (position_iff g _ _).mp hg
      have hi : (r u).2 = intervalCode n iv := by rw [← hh.2, hu, hg', hs']; exact ht
      exact Prod.ext (r.injective ((Prod.ext hu hi).trans he.symm))
        (Prod.ext hg' (s.eq_symm_apply.mpr (Prod.ext hs' hslot)))
    · cases h
  · intro eq
    simp only [Prod.mk.injEq] at eq
    rw [eq.1, eq.2.1, eq.2.2, he, Equiv.apply_symm_apply]
    simp only [ht, hv, and_self, ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and, and_true]
    exact (position_iff _ _ _).mpr ⟨rfl, rfl⟩

variable (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hd : 0 < Δ)
    (rm : (t.state hb).Room e) (ready : t.Ready hb hc M rm cap) (valid : K.Valid (t.layout hc))
    {x y : Wire} {Z : Border F t.T x y t.x t.y} {labels : A.label.obj}
    (q : A.Encloses (t.r, labels) t.G Z)

theorem grouped_moves (h : q.core = t.p) :
    (A.grouped t M e cap K).Moves q (t.encodes hb hc M rm cap K hd ready valid) (A.newSlot t q.slot) where
  positive := A.slot_pos t q.slot q.positive
  iff := by
    rintro ⟨u, g, l⟩ i
    rw [q.frozen, h]
    exact A.back_iff t M e cap K hc q.slot i u g l

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Issuing the frozen predecessor and the core predecessor together -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Packing Coloring History Window State.Board
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
    {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h} {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ}
    {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (M : Book D.scheme P z hz) (cap : ℕ) (K : Template.Meter)
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C)

local notation "n" => (D.scheme.h - a)
local notation "Y" => D.after a Δ C M e cap K
local notation "I" => D.Branch P a ha b k cost Δ C z σ hu

abbrev Supplement (a e : ℕ) := (D.Pointers e).pair (.vec (D.scheme.h - a + A.k) A.pointer)

def supplement (t : I) (rm : (t.state hb).Room e) :
    (Tile.output D.scheme.m a n (A.Supplement a e)).obj :=
  fun i j => ((t.move hb hc M rm cap).commands i j, (A.grouped t M e cap K).flags i j)

private theorem tag_eq (s t : I) (v : Site (s.G.V × Cell a) n) (w : Site (t.G.V × Cell a) n)
    (he : ((s.board hb).recenter v).look = ((t.board hb).recenter w).look) :
    D.tags a ha k cost Δ C s.r (s.p.post.host v.1.1) (cellIndex a v.1.2) =
      D.tags a ha k cost Δ C t.r (t.p.post.host w.1.1) (cellIndex a w.1.2) := by
  have hh := source_eq he (related_root.widen (by decide : 0 ≤ 2))
  exact congrArg (fun z : (D.WithCount a b).obj => fun i => (z.1.2.2.2.1 i).1) hh

theorem flags_eq (s t : I) (v : Site (s.G.V × Cell a) n) (w : Site (t.G.V × Cell a) n)
    (he : ((s.board hb).recenter v).look = ((t.board hb).recenter w).look) :
    (A.grouped s M e cap K).flags (Child.host s.p.post.host n (v.1.1, v.2)) (cellIndex a v.1.2) =
      (A.grouped t M e cap K).flags (Child.host t.p.post.host n (w.1.1, w.2)) (cellIndex a w.1.2) := by
  have hv := (D.child_live a s.p _).mpr ⟨(v.1.1, v.2), rfl⟩
  have hw := (D.child_live a t.p _).mpr ⟨(w.1.1, w.2), rfl⟩
  have hblock : v.1.2 = w.1.2 := (agrees he).2
  have hiv : intervalCode n v.2 = intervalCode n w.2 := (agrees he).1.key
  funext l
  simp only [Relocation.flags, grouped, Template.parent, Child.host_parts, hv, hw]
  rw [tag_eq hb s t v w he, hblock, hiv]

theorem flags_vacant (t : I) (i : B (D.size a)) (j : B a) (hi : D.childLive a t.r i = false) :
    (A.grouped t M e cap K).flags i j = fun _ => A.tag none := by
  funext l
  simp [Relocation.flags, grouped, lookupSeat, hi]

variable {J : Type*} (ts : J → D.Branch P a ha b k cost Δ C z σ hu)
    (rm : ∀ i, ((ts i).state hb).Room e)
local notation "W" => A.Supplement a e

theorem issue (ready : ∀ i, (ts i).Ready hb hc M (rm i) cap) :
    ∃ table : Table F, wd table.1 + wd table.2.1 = D.issueWidth a b Δ C M e cap K W ∧
      ∀ {u v N l : ℕ} {L : Set (Table F)},
      3 ≤ u → table ∈ L → D.issueWidth a b Δ C M e cap K W ≤ u →
      Access F u L (D.scheme.m + D.scheme.d) v N → 2 ^ a * (Walks 8 D.scheme.d (D.WithCount a b)).width ≤ v →
      D.size a ≤ l → 2 ^ (Tile.radius D.scheme.d + ((D.scheme.h - a) + 1)) ≤ l → 2 ^ (D.degree a Δ C) ≤ l →
      Computes F u L (D.Headed a b Δ C) (D.Issued a Δ C M e cap K W)
        (fun i => (ts i).head hb)
        (fun i => ((ts i).output hb hc M (rm i) cap K, A.supplement M cap K hb hc (ts i) (rm i)))
        (fun _ => 1) (D.issueCost a b Δ C M e cap K W v N l) :=
  D.issue_net hb M cap K W hc ts rm ready (fun i => A.supplement M cap K hb hc (ts i) (rm i))
    ((fun _ _ => BatchDescent.Trail.point D.scheme none), fun _ => A.tag none)
    (fun i j v w he => Prod.ext (Template.Branch.commands_eq (ready i) (ready j) he)
      (A.flags_eq M cap K hb _ _ v w he))
    (fun i x y hi => Prod.ext ((ts i).commands_vacant hb hc M (rm i) cap x y hi)
      (A.flags_vacant M cap K (ts i) x y hi))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Preparing a grouped query from the issued labels and predecessors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Packing Coloring History Window
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
    {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h} {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ}
    {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (M : Book D.scheme P z hz) (cap : ℕ) (K : Template.Meter)
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C)

local notation "Y" => D.after a Δ C M e cap K
local notation "I" => D.Branch P a ha b k cost Δ C z σ hu
local notation "W" => A.Supplement a e
local notation "Z" => A.Requests Y (D.scheme.h - a + A.k) (D.scheme.d + 1)

def query (t : I) (rm : (t.state hb).Room e) (labels : A.label.obj) :
    Query A Y (D.scheme.h - a + A.k) (D.scheme.d + 1) where
  R := A.grouped t M e cap K
  M := t.move hb hc M rm cap
  old := (t.r, labels)
  fresh := t.output hb hc M rm cap K
  active i _ := D.childLive a t.r i

def groupedCost (a b Δ C : ℕ) (M : Book D.scheme P z hz) (e cap : ℕ)
    (K : Template.Meter) (v N l : ℕ) :=
  4 * A.format.width + D.issueCost a b Δ C M e cap K (A.Supplement a e) v N l +
    4 * ((A.format.pair (D.Issued a Δ C M e cap K (A.Supplement a e))).width +
      2 * (A.Requests (D.after a Δ C M e cap K) (D.scheme.h - a + A.k) (D.scheme.d + 1)).width)

theorem grouped_net {J : Type*} (ts : J → I) (rm : ∀ i, ((ts i).state hb).Room e) (f : J → A.label.obj)
    (ready : ∀ i, (ts i).Ready hb hc M (rm i) cap) :
    ∃ table : Table F, wd table.1 + wd table.2.1 = D.issueWidth a b Δ C M e cap K W ∧
      ∀ {u v N l : ℕ} {L : Set (Table F)},
      3 ≤ u → table ∈ L → D.issueWidth a b Δ C M e cap K W ≤ u →
      Access F u L (D.scheme.m + D.scheme.d) v N → 2 ^ a * (Walks 8 D.scheme.d (D.WithCount a b)).width ≤ v →
      D.size a ≤ l → 2 ^ (Tile.radius D.scheme.d + ((D.scheme.h - a) + 1)) ≤ l → 2 ^ (D.degree a Δ C) ≤ l →
      Computes F u L (A.format.pair (D.Headed a b Δ C)) Z
        (fun i => (((ts i).r, f i), (ts i).head hb))
        (fun i => (A.query M cap K hb hc (ts i) (rm i) (f i)).requests)
        (fun _ => 1) (A.groupedCost a b Δ C M e cap K v N l) := by
  obtain ⟨t, wt, run⟩ := A.issue M cap K hb hc ts rm ready
  refine ⟨t, wt, ?_⟩
  intro u v N l L h₃ ht hw access hv size radius degree
  have send := run h₃ ht hw access hv size radius degree
  let old (i : J) : A.format.obj := ((ts i).r, f i)
  have keep := Computes.of_map (x := old) (L := L) (Map.circuit h₃ (Circuit.id F A.format))
    (fun _ => rfl)
  let X := A.format.pair (D.Issued a Δ C M e cap K W)
  let wire (x : X.obj) : (Z).obj :=
    (x.1, x.2.1, fun i j => ((Y).live x.2.1 i, (x.2.2 i j).1 0, (x.2.2 i j).2))
  have pack : Circuit F X Z wire (X.width + 2 * (Z).width) := by
    let pin : (Z).pins → X.pins
      | .inl w => .inl w
      | .inr (.inl w) => .inr (.inl w)
      | .inr (.inr (i, _, .inl w)) => .inr (.inl (.inr (i, .inl (.inl w))))
      | .inr (.inr (i, j, .inr (.inl w))) => .inr (.inr (i, j, .inl (0, w)))
      | .inr (.inr (i, j, .inr (.inr w))) => .inr (.inr (i, j, .inr w))
    exact Circuit.project pin (by rintro x (w|w|⟨i, j, w|w|w⟩) <;> rfl)
  have h := (keep.par send).comp (Computes.of_map (Map.circuit h₃ pack)
    (y := fun i => (A.query M cap K hb hc (ts i) (rm i) (f i)).requests) (fun _ => rfl))
  simp only [one_mul] at h
  exact h

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end
