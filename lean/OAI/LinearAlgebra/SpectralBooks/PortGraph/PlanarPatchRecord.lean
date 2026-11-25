import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMap
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssembly

/-! # Canonical records of bounded, numbered old patches

A record lists the old vertex types and full certificates in name order.
An involution on the actual numbered darts represents internal mate pairs;
its fixed darts are the individually distinguished stubs. Each internal wire
is named by its outgoing dart, even at a loop.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph

/-- The numbered ports of a finite list of vertex types. -/
abbrev PatchDart {n : ℕ} (θ : Fin n → MapType) := Σ v, Fin (θ v).degree.val

def PatchDart.side {n : ℕ} {θ : Fin n → MapType} (p : PatchDart θ) : Bool :=
  (θ p.1).direction p.2

/-- The finite combinatorial part of an old patch record. Fixed darts are
stubs. Distinct darts paired by the involution must have opposite directions. -/
structure PatchShape (K : ℕ) where
  size : Fin (K+1)
  positive : 0 < size.val
  typeAt : Fin size.val → MapType
  opposite : Equiv.Perm (PatchDart typeAt)
  involutive : Function.Involutive opposite
  direction : ∀ p, opposite p ≠ p → (opposite p).side = !p.side

namespace PatchShape

variable {K : ℕ} (R : PatchShape K)
abbrev Vertex := Fin R.size.val
abbrev Dart := PatchDart R.typeAt
abbrev Stub := {p : R.Dart // R.opposite p = p}
/-- The tail of a nonfixed pair supplies a canonical internal wire name. -/
abbrev Wire := {p : R.Dart // R.opposite p ≠ p ∧ p.side = false}

def toPiece : OpenPiece R.Stub where
  Vertex := R.Vertex
  Edge := R.Wire
  graph := ⟨fun e => e.val.1, fun e => (R.opposite e.val).1⟩
  attach s := s.val.1

/-- Read a dart from its internal wire and side, or from its stub name. -/
def read : (R.Wire × Bool) ⊕ R.Stub → R.Dart
  | .inl (e,false) => e.val
  | .inl (e,true) => R.opposite e.val
  | .inr s => s.val

theorem read_bijective : Function.Bijective R.read := by
  have hn (e : R.Wire) : R.opposite (R.opposite e.val) ≠ R.opposite e.val := by
    rw [R.involutive]
    exact e.property.1.symm
  have ht (e : R.Wire) : (R.opposite e.val).side = true := by
    rw [R.direction _ e.property.1, e.property.2]
    rfl
  constructor
  · rintro (⟨e,(_|_)⟩|s) (⟨f,(_|_)⟩|t) h
    · exact congrArg (fun e : R.Wire => Sum.inl (e,false)) (Subtype.ext h)
    · exact False.elim (by have := congrArg PatchDart.side h; simp [read, ht, e.property.2] at this)
    · change e.val = t.val at h
      exact False.elim (e.property.1 (by rw [h, t.property]))
    · exact False.elim (by have := congrArg PatchDart.side h; simp [read, ht, f.property.2] at this)
    · exact congrArg (fun e : R.Wire => Sum.inl (e,true)) (Subtype.ext (R.opposite.injective h))
    · change R.opposite e.val = t.val at h
      exact False.elim (hn e (by rw [h, t.property]))
    · change s.val = f.val at h
      exact False.elim (f.property.1 (by rw [← h, s.property]))
    · change s.val = R.opposite f.val at h
      exact False.elim (hn f (by rw [← h, s.property]))
    · exact congrArg Sum.inr (Subtype.ext h)
  · intro p
    by_cases hp : R.opposite p = p
    · exact ⟨.inr ⟨p,hp⟩,rfl⟩
    cases hs : p.side with
    | false => exact ⟨.inl (⟨p,hp,hs⟩,false),rfl⟩
    | true =>
      exact ⟨.inl (⟨R.opposite p, by rw [R.involutive]; exact Ne.symm hp,
        by rw [R.direction _ hp, hs]; rfl⟩,true),R.involutive _⟩

/-- Every port used when reassembling a piece is exactly one original
numbered port; neither unused slots nor extra stub names can be read. -/
def endEquiv : (R.toPiece.Edge × Bool) ⊕ R.Stub ≃ R.Dart :=
  Equiv.ofBijective R.read R.read_bijective

@[simp] theorem read_internal_owner (e : R.Wire) (b : Bool) :
    (R.read (.inl (e,b))).1 = R.toPiece.graph.vertex e b := by cases b <;> rfl

@[simp] theorem read_stub_owner (s : R.Stub) :
    (R.read (.inr s)).1 = R.toPiece.attach s := rfl

@[simp] theorem read_internal_side (e : R.Wire) (b : Bool) :
    (R.read (.inl (e,b))).side = b := by
  cases b
  · exact e.property.2
  · exact (R.direction _ e.property.1).trans (by rw [e.property.2]; rfl)

instance : Finite (PatchShape K) :=
  Finite.of_injective (fun R : PatchShape K =>
    (⟨R.size, R.typeAt, R.opposite⟩ : Σ n : Fin (K+1), Σ θ : Fin n.val → MapType, Equiv.Perm (PatchDart θ))) (by
      rintro ⟨n,h,t,o,i,d⟩ ⟨n',h',t',o',i',d'⟩ he
      cases he
      rfl)

noncomputable instance : Fintype (PatchShape K) := Fintype.ofFinite _

end PatchShape

/-- The certificates retain their entire alphabet, including the old vertex
name. This permits one common record per labelled patch. -/
structure PatchRecord (K : ℕ) (A : Type*) where
  shape : PatchShape K
  label : shape.Vertex → A

namespace PatchRecord

variable {K : ℕ} {A : Type*} (R : PatchRecord K A)

abbrev toPiece := R.shape.toPiece

/-- Canonical format and all old tests inspectable inside a single record.
Exterior wire tests refer to the records of the two corresponding stubs. -/
structure Valid {I : Type*} (name : A → ℕ) (patch : A → I)
    (vertex : MapType → A → Prop) (edge : Fin 4 → Fin 4 → A → A → Prop) : Prop where
  sorted : StrictMono (fun i => name (R.label i))
  commonPatch : ∀ i j, patch (R.label i) = patch (R.label j)
  connected : (PlanarPatch.underlying R.toPiece.graph.tail R.toPiece.graph.head).Connected
  uniqueRoot : ∀ i j, (R.shape.typeAt i).root = true → (R.shape.typeAt j).root = true → i = j
  vertexTests : ∀ i, vertex (R.shape.typeAt i) (R.label i)
  edgeTests : ∀ e : R.shape.Wire, let p := e.val; let q := R.shape.opposite p
    edge (p.2.castLE (Nat.le_of_lt_succ (R.shape.typeAt p.1).degree.isLt))
      (q.2.castLE (Nat.le_of_lt_succ (R.shape.typeAt q.1).degree.isLt)) (R.label p.1) (R.label q.1)

private def equivSigma : PatchRecord K A ≃ Σ s : PatchShape K, s.Vertex → A where
  toFun r := ⟨r.shape, r.label⟩
  invFun r := ⟨r.1, r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [Fintype A] : Fintype (PatchRecord K A) :=
  Fintype.ofEquiv _ equivSigma.symm

/-- The only fields whose range grows with the old map are the at most `K`
full vertex certificates. The number of shapes depends on `K` alone. -/
theorem card_le [Fintype A] [Nonempty A] :
    Fintype.card (PatchRecord K A) ≤ Fintype.card (PatchShape K) * Fintype.card A ^ K := by
  rw [Fintype.card_congr equivSigma, Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : PatchShape K, Fintype.card A ^ K := by
      apply Finset.sum_le_sum
      intro s _
      simp only [Fintype.card_fun, PatchShape.Vertex, Fintype.card_fin]
      exact Nat.pow_le_pow_right Fintype.card_pos (Nat.le_of_lt_succ s.size.isLt)
    _ = _ := by simp

/-- The actual radius-`2K+2` certificate alphabet of the map-labels lemma
therefore gives a polynomial-size catalogue, with exponent depending only on `K`. -/
theorem full_card_le {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    Fintype.card (PatchRecord K (PortView (PlanarCertSize.BaseAlphabet N) (2*K+2))) ≤
      (2*N) ^ (Nat.clog 2 (Fintype.card (PatchShape K)) + (80 * 5^(2*K+2)) * K) := by
  let : Nonempty (PortView (PlanarCertSize.BaseAlphabet N) (2*K+2)) :=
    ⟨(default, fun _ => none)⟩
  have hc := PortView.card_le_pow (2*K+2) hN (PlanarCertSize.baseAlphabet_card_le hN)
  have hs := (Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card (PatchShape K))).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ 2*N) _)
  exact (card_le (K := K)).trans (by rw [pow_add, pow_mul]; exact Nat.mul_le_mul hs (Nat.pow_le_pow_left hc _))

end PatchRecord
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
