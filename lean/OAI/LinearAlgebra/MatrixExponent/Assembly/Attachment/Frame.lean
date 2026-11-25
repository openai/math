import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial

/-!
# Keeping frozen tables while the core moves

A second local record contains the full border and the tether endpoints.
Host addresses and the block number are shared with the core record. The
first station slot is reserved for the core, even if it is empty.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing

structure Attachment {F : Type} (D : Template F) where
  k : ℕ
  e : ℕ
  ℓ : ℕ
  decode : B ℓ → Pattern F D.scheme.d k e
  live : B ℓ → B k → Bool
  charge : B ℓ → B k → ℝ
  coreSpan : B D.scheme.e ↪ B e

namespace Attachment

variable {F T : Type} {D : Template F} (A : Attachment D)

abbrev scheme : Scheme F :=
  ⟨D.scheme.m, D.scheme.d, D.scheme.h, A.k, A.e, A.ℓ, A.decode⟩

abbrev label := Format.vec D.scheme.m (.vec D.scheme.h (.addr A.ℓ))

abbrev format := D.format.pair A.label

def rows (r : A.format.obj) : A.scheme.format.obj :=
  fun v => (D.nav r.1 v, r.2 v)

theorem width : A.format.width = D.format.width + 2 ^ D.scheme.m * (2 ^ D.scheme.h * A.ℓ) := by
  simp only [format, label, Format.width_pair, Format.width_vec, Format.width_addr]

variable [Field F] [Fintype T] {x y a b : Wire} {u : ℕ} {L : Fringe x y T}
variable (r : A.format.obj) (G : HostNet F L D.scheme.h u) (Z : Border F T a b x y)

/-- The core and the border records must describe the same individual
core bits, in order. A frozen table is kept on its own assigned slot. -/
structure Encloses where
  full : D.full = true
  tether : L.tensor = Z.tensor
  core : D.Encodes r.1 G
  pres : A.scheme.Presentation (A.rows r) (Z.attach G.diagram)
  directed : pres.Directed
  occupied : ∀ v : A.scheme.Vtx, A.live (r.2 v.1 v.2.1) v.2.2 = true ↔ v ∈ Set.range pres.vertex
  slot : T → B A.k
  positive : ∀ t, slot t ≠ 0
  internal : ∀ v, pres.vertex (.inl v) =
    (core.post.host (G.units.place v).1, core.post.block (G.units.place v).2, 0)
  frozen : ∀ t, pres.vertex (.inr t) =
    (core.post.host (G.park t).1, core.post.block (G.park t).2, slot t)
  charge : ∀ t, A.charge (r.2 (core.post.host (G.park t).1) (core.post.block (G.park t).2))
    (slot t) = L.charge t
  ordered : ∀ v (j : G.diagram.Port v),
    (pres.pin (.inl v) j).1 = A.coreSpan (core.post.pin v j).1 ∧
      (pres.pin (.inl v) j).2.val = (core.post.pin v j).2.val

variable {r G Z A}

theorem Encloses.distinct (q : A.Encloses r G Z) {v w : T}
    (h : G.park v = G.park w) (hs : q.slot v = q.slot w) : v = w := by
  apply Sum.inr.inj
  apply q.pres.vertex.injective
  rw [q.frozen, q.frozen, h, hs]

end Attachment
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Common stage boundary while the border is retained -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Packing Coloring

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
    (x y : Wire) (u height : ℕ)

structure Data where
  T : Type
  [finite : Fintype T]
  a : Wire
  b : Wire
  L : Fringe a b T
  G : HostNet F L D.scheme.h u
  Z : Border F T x y a b
  raw : A.format.obj
  q : A.Encloses raw G Z

attribute [instance] Data.finite

abbrev volume (m : ℕ) := 2 ^ m + wd x + wd y
abbrev payload (m : ℕ) := Fmt.payload m (volume x y m) height
abbrev port := A.format.pair (payload x y height D.scheme.m)

namespace Data
variable {A x y u height} (X : Data A x y u)

abbrev diagram := X.Z.attach X.G.diagram
abbrev Fits (height : ℕ) := A.scheme.Fits (A.rows X.raw) (volume x y D.scheme.m) height

def data (fit : X.Fits height) (i : Val x) (j : Val y) : (payload x y height D.scheme.m).obj :=
  A.scheme.store _ fit (X.q.pres.exterior i j)

def Neutral := ∀ v, X.G.diagram.arity v = 0 → ∀ t, Transcript.sample (X.G.diagram.table v) t = 1

end Data

def frame (P : Data A x y u → Prop) : Assembly.Snapshot.{1} F x y where
  state := {X : Data A x y u // P X ∧ X.Fits height}
  eval i := i.val.diagram.eval
  port := A.port x y height
  encode i a b := (i.val.raw, i.val.data i.property.2 a b)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end
