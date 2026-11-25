import OAI.Computability.BorderVNP.DiagonalTapeBottom
import OAI.Computability.BorderVNP.DiagonalExternalSewDenseSum

/-! # The exact substituted parse row on the attained dense histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.SewnTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Packing.PhysicalEpochs Cover TeamContraction
open ExternalSew ExternalSew.GridHosts VPVNP
open scoped BigOperators Classical

set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} (U : Factory.Dense.Programs S)
    {R r pins link k axes gridDepth a regs w ec width s copies T start : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)

/-- The actual registered handoff/sorter wiring with the chosen program and site literals. -/
abbrev wiring (pins : ℕ) := tapeWiring p free
  (Wires.ownerSlots (r := r) (k := regs) (w := w) (e := ec) (W := width)) pins link (k+1) fit

/-- Row-major enumeration of the original batches after these packing stages. -/
noncomputable local instance batchFinite {j : ℕ} :
    Fintype (Port (Factory.ofDenseSchedule U).fan (Fin copies × Unit) j) :=
  Replay.batchFinite (Factory.ofDenseSchedule U).fan (Fin copies × Unit) j

variable (deep : (Factory.ofDenseSchedule U).floor+1+(Factory.ofDenseSchedule U).drop*T ≤ start) (count : (Factory.ofDenseSchedule U).fan^T*copies = R+1)
    (bottom : (Factory.ofDenseSchedule U).State (fun _ : Fin (tileCount axes gridDepth) => copies*(inputBlockWidth r (k+1) axes gridDepth)) start 0)
    (installed : bottom.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => (inputBlockWidth r (k+1) axes gridDepth)) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < (inputBlockWidth r (k+1) axes gridDepth))

/-- Cast the actual zero-literal conditioned table to the public bottom
state selected by the site compiler. -/
noncomputable def base (z : Fin copies → W.Hidden position) :
    Tracked (Fin copies × Unit) (PairedParameters k s) Gadget (Nat.clog 2 (r*(2*k+1)+1)) bottom.pack.layout :=
  (W.bundle position copies z).castLayout installed.symm

/-- The compressed physical network, sewn at its retained exterior hosts.
It depends only on the public history and the original port layout. -/
noncomputable def network (q : ((Factory.ofDenseSchedule U).histories deep bottom T).Index) :
    Network D (FreeBlock R (tileCount axes gridDepth)) (fun _ => inputBlockWidth r (k+1) axes gridDepth) :=
  let L := (flattenPack T (((Factory.ofDenseSchedule U).histories deep bottom T).term q).pack).layout
  let keep := (Retains.parallel (fun _ : Fin ((Factory.ofDenseSchedule U).fan^T) =>
    Retains.ofEq installed.symm)).trans (denseOuterHosts U deep bottom q)
  let h := blockHosts (wiring p fit free pins) axes gridDepth order position
    ((Factory.ofDenseSchedule U).fan^T) copies count L keep
  h.bundle.layout.packExternal (fun _ : FreeBlock R (tileCount axes gridDepth) =>
    inputBlockWidth r (k+1) axes gridDepth) h.groupOwner

/-- The precise tagged tables after all normalized epochs, carrying the
fine-route private choices and the matched physical exterior wires. -/
noncomputable def tags (q : ((Factory.ofDenseSchedule U).histories deep bottom T).Index)
    (z : Fin ((Factory.ofDenseSchedule U).fan^T) → Fin copies → W.Hidden position) :
    Tracked (Port (Factory.ofDenseSchedule U).fan (Fin copies × Unit) T) (PairedParameters k s) Gadget
      (Nat.clog 2 (r*(2*k+1)+1)) (network U p fit position free deep count bottom installed q) :=
  denseSewnTerm U (wiring p fit free pins) axes gridDepth order position deep count bottom installed y hy pos
    (base U p fit W position bottom installed) hg q z

/-- These fully compressed and sewn terms compute the original formal
substitution on the actual installed program literals and each actual pin.
The finite scalar specialization is applied only after the whole geometry
and original fine-route assignments have been fixed. -/
theorem substituted_eq (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (pin : Fin pins → Bool) (bank : Ports (fun _ : FreeBlock R (tileCount axes gridDepth) => (inputBlockWidth r (k+1) axes gridDepth)))
    (delivered : ∀ z, let a := freeLane hg (gridRoom (wiring p fit free pins) Fintype.card_pos) z
      bank a.1 a.2 = freeBits (wiring p fit free pins) pin z) :
    substituted E k s (wiring p fit free pins).slot pin = ∑ q : ((Factory.ofDenseSchedule U).histories deep bottom T).Index,
      ∑ z : Fin ((Factory.ofDenseSchedule U).fan^T) → Fin copies → W.Hidden position,
        ((tags U p fit W position free deep count bottom installed y hy pos hg q z).valued values).tensor bank := by
  have eqv := W.tape_bottom (Factory.ofDenseSchedule U) count p fit position values free pin
  refine eqv.trans (Eq.trans ?_ (sum_dense_sewn U (wiring p fit free pins) axes gridDepth order position deep count
    bottom installed y hy pos (base U p fit W position bottom installed) values lookup hg pin bank delivered))
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ext _
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro z _
  exact (Tracked.castLayout_tensor installed.symm (W.bundle position copies z) values _).symm

end Diagonal.CellEntries.SewnTape

end BorderVNP
end Computability
end OAI
