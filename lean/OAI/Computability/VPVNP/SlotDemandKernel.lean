import OAI.Computability.VPVNP.SlotDemandEnergy
import OAI.Computability.VPVNP.NetworkKernel
import Mathlib.Algebra.BigOperators.Fin

/-!
# Repartitioning wire payloads into the AB and CD demands

A thick–thick bundle is one ordered string at A and B. Each demand reads its
contiguous slice at both ends in the same order. This module identifies the
individual old bits with the repartitioned bits and proves the product of
the motif demand coefficients is exactly the original wire-network coefficient.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

/-- Enumerate all bit positions by concatenating fields in the given order. -/
def orderedBits {A : Type*} [Fintype A] {n : ℕ} (order : A ≃ Fin n) (w : A → ℕ) :
    (Σ a, Fin (w a)) ≃ Fin (∑ a, w a) :=
  (Equiv.sigmaCongr order (fun a ↦ finCongr (show w a = w (order.symm (order a)) by simp))).trans
    (finSigmaFinEquiv.trans (finCongr (order.symm.sum_comp w)))

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Old thick–thick wires whose underlying site and port identify bundle `b`. -/
abbrev ThickFiber (b : Site V Tag L × Fin d) := {a : P.ThickWire // a.1.1 = b}
/-- Shrinking motifs whose CD demand is assigned to bundle `b`. -/
abbrev MotifFiber (b : Site V Tag L × Fin d) := {m : P.Motif // P.bundle m = b}

/-- The numbering of old wires used at both packed ends. -/
abbrev ThickNumbering := ∀ b : Site V Tag L × Fin d, P.ThickFiber b ≃ Fin (2 ^ c * d / 4)

/-- Choose a bijection from the thick–thick wires in each bundle to the first `2 ^ c * d / 4`
indices when `2 ≤ c`. -/
noncomputable def thickNumbering (hc : 2 ≤ c) : P.ThickNumbering := fun b ↦
  Fintype.equivFinOfCardEq (P.card_thick_fiber hc b)

variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag L d c → ℕ)

/-- Pass from an AB slice and its local bit to an old wire and its local bit
through the common offset in the concatenated payload. -/
def demandBitEquiv (b : Site V Tag L × Fin d) :
    (Σ m : P.MotifFiber b, Fin (P.abWidth number w m.1)) ≃
      (Σ a : P.ThickFiber b, Fin (w a.1.1)) :=
  (orderedBits (number b) (fun m ↦ P.abWidth number w m.1)).trans
    ((finCongr (P.sum_abWidth hc hd number w b)).trans
      (orderedBits (order b) (fun a ↦ w a.1.1)).symm)

/-- Read the AB slice of a single motif at one packed endpoint. -/
def abWord (x : (a : Arc V H Tag L d c) → Fin (w a) → Bool) (m : P.Motif) :
    Fin (P.abWidth number w m) → Bool := fun i ↦
  let z := P.demandBitEquiv hc hd number order w (P.bundle m) ⟨⟨m,rfl⟩,i⟩
  x z.1.1.1 z.2

private theorem abWord_at (x : (a : Arc V H Tag L d c) → Fin (w a) → Bool)
    (b : Site V Tag L × Fin d) (z : Σ m : P.MotifFiber b, Fin (P.abWidth number w m.1)) :
    P.abWord hc hd number order w x z.1.1 z.2 =
      let a := P.demandBitEquiv hc hd number order w b z
      x a.1.1.1 a.2 := by
  rcases z with ⟨⟨m,hm⟩,i⟩
  subst b
  rfl

/-- All AB tests together impose precisely equality on every old thick–thick wire. -/
theorem abWords_eq_iff (x y : (a : Arc V H Tag L d c) → Fin (w a) → Bool) :
    (∀ m, P.abWord hc hd number order w x m = P.abWord hc hd number order w y m) ↔
      ∀ a : P.ThickWire, x a.1 = y a.1 := by
  constructor
  · intro h a
    funext i
    let e := P.demandBitEquiv hc hd number order w a.1.1
    let z := e.symm ⟨⟨a,rfl⟩,i⟩
    have eqn := congrFun (h z.1.1) z.2
    rw [P.abWord_at hc hd number order w x _ z, P.abWord_at hc hd number order w y _ z] at eqn
    change x (e z).1.1.1 (e z).2 = y (e z).1.1.1 (e z).2 at eqn
    rw [show e z = ⟨⟨a,rfl⟩,i⟩ from e.apply_symm_apply _] at eqn
    exact eqn
  · intro h m
    funext i
    let a := P.demandBitEquiv hc hd number order w (P.bundle m) ⟨⟨m,rfl⟩,i⟩
    exact congrFun (h a.1.1) a.2

/-- Actual input network of the shrinking step. -/
def oldWireNetwork : NetworkKernel.Network where
  Site := Position V H Tag L c
  siteFintype := inferInstance
  Edge := Arc V H Tag L d c
  edgeFintype := inferInstance
  src := sourcePosition
  dst a := sourcePosition (P.actual a)
  Payload a := Fin (w a) → Bool
  payloadFintype _ := inferInstance

/-- Old source word of a directed wire. -/
def outgoingWord (x : ∀ s, (P.oldWireNetwork w).Half s) (a : Arc V H Tag L d c) :
    Fin (w a) → Bool :=
  (x (sourcePosition a)).1 a rfl

/-- Old destination word of the same wire, using its original outgoing label. -/
def incomingWord (x : ∀ s, (P.oldWireNetwork w).Half s) (a : Arc V H Tag L d c) :
    Fin (w a) → Bool :=
  (x (sourcePosition (P.actual a))).2 a rfl

/-- CD word at its designated thin endpoint. -/
def cWord (x : ∀ s, (P.oldWireNetwork w).Half s) (m : P.Motif) : Fin (w m.1) → Bool :=
  if P.thick (sourcePosition m.1) then P.incomingWord w x m.1 else P.outgoingWord w x m.1

/-- CD word at its other old endpoint. -/
def dWord (x : ∀ s, (P.oldWireNetwork w).Half s) (m : P.Motif) : Fin (w m.1) → Bool :=
  if P.thick (sourcePosition m.1) then P.outgoingWord w x m.1 else P.incomingWord w x m.1

omit [DecidableEq V] [DecidableEq Tag] [DecidableEq L] in
private theorem cdWords_eq_iff (x : ∀ s, (P.oldWireNetwork w).Half s) (m : P.Motif) :
    P.cWord w x m = P.dWord w x m ↔ P.outgoingWord w x m.1 = P.incomingWord w x m.1 := by
  by_cases h : P.thick (sourcePosition m.1) <;> simp [cWord,dWord,h,eq_comm]

variable {k : Type*} [CommSemiring k]

/-- Coefficient of the two demand wires read from an arbitrary assignment of
independent old half-wires. -/
noncomputable def demandCoeff (m : P.Motif) (x : ∀ s, (P.oldWireNetwork w).Half s) : k :=
  if P.abWord hc hd number order w (P.outgoingWord w x) m =
    P.abWord hc hd number order w (P.incomingWord w x) m ∧
      P.cWord w x m = P.dWord w x m then 1 else 0

/-- Exact demand factorization for the shrinking step of equation (7.1). -/
theorem oldWireNetwork_coeff (x : ∀ s, (P.oldWireNetwork w).Half s) :
    (P.oldWireNetwork w).coeff (k := k) x = ∏ m, P.demandCoeff hc hd number order w m x := by
  classical
  have hcoeff : (P.oldWireNetwork w).coeff (k := k) x =
      if ∀ a, P.outgoingWord w x a = P.incomingWord w x a then (1 : k) else 0 := by
    let q := fun a : Arc V H Tag L d c ↦ P.outgoingWord w x a = P.incomingWord w x a
    apply (@Fintype.prod_boole _ k _ _ q (fun _ ↦ Classical.propDecidable _)).trans
    by_cases h : ∀ i, q i <;> simp only [q] at h ⊢ <;> simp [h]
  rw [hcoeff]
  simp only [demandCoeff, Fintype.prod_boole, forall_and,
    P.abWords_eq_iff hc hd number order w, P.cdWords_eq_iff w]
  congr 1
  apply propext
  constructor
  · exact fun h ↦ ⟨fun a ↦ h a.1, fun m ↦ h m.1⟩
  · intro ⟨h₁,h₂⟩ a
    by_cases h : P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))
    · exact h₁ ⟨a,h⟩
    · exact h₂ ⟨a,h⟩

end Compression.PackingData

end VPVNP
end Computability
end OAI
