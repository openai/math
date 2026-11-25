import OAI.Hierarchy.TaggedWireRoutedPackets
import OAI.Hierarchy.TaggedWideTraceBits
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # Actual shared intermediate bond of the packet and its installed routing -/
noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open ThreeFlat Routing Diagonal.MotifOuterTerms
open LinearAlgebra.SpectralBooks ChordGraph
open CalendarTape AdaptiveProbe
open scoped BigOperators Classical

variable {F V : Type} [Field F] [Fintype V] {n S N H copies : ℕ}
local notation "P" => V ⊕ Fin n
local notation "Net" => BitNetwork F (Fintype.card P)

private def pair (K L : Net) : Net :=
  Tagged.WideHost.localFamily (fun i : Bool=>if i then K else L) (fun _=>Sum.inl)

private theorem pair_value (K L : Net) (x : P → Bool) :
    TypedWiring.value (pair K L) x=TypedWiring.value K x*TypedWiring.value L x := by
  rw [pair,Tagged.WideHost.localFamily_eval,Fintype.prod_bool]; rfl

omit [Field F] in
private theorem pair_fee (K L : Net) :
    (pair K L).cells+(pair K L).internal=(K.cells+K.internal)+(L.cells+L.internal) := by
  rw [pair,Tagged.WideHost.localFamily_size,Fintype.sum_bool]; rfl

def hiddenEntry (valid packet install : Net) : BitNetwork F (Fintype.card V) :=
  TypedWiring.glue («P»:=V) (H:=Fin n) (port:=fun _ : Unit=>V⊕Fin n) (fun _ : Unit=>pair valid (pair packet install)) (fun _ q=>q)

omit [Field F] in
theorem hidden_fee (valid packet install : Net) :
    (hiddenEntry valid packet install).cells+(hiddenEntry valid packet install).internal=
      n+(valid.cells+valid.internal)+(packet.cells+packet.internal)+(install.cells+install.internal) := by
  simp only [hiddenEntry,TypedWiring.glue_cells,TypedWiring.glue_internal,Fintype.sum_unique,Fintype.card_fin]
  have first := pair_fee valid (pair packet install)
  have second := pair_fee packet install
  omega

/-- Exact contraction of all three physical circuits along their shared local word. -/
theorem hiddenEntry_sum (valid packet install : Net) (v : V→Bool) :
    TypedWiring.value (hiddenEntry valid packet install) v=
      ∑d:Fin n→Bool,TypedWiring.value valid (Sum.elim v d)*
        (TypedWiring.value packet (Sum.elim v d)*TypedWiring.value install (Sum.elim v d)) := by
  rw [hiddenEntry,TypedWiring.glue_value]
  simp only [Fintype.prod_unique,pair_value]
  apply Finset.sum_congr (Finset.ext (fun _ => by simp))
  intro d _
  rfl

variable {row : Row F S H copies} {phys : Fin N → Chord S} (R : RowRouting row phys)
    (c : Histogram (Fin H) copies) (s : Fin S)

private def packState {X B : Type} (bits : X ≃ (B → Bool)) (place : B ↪ Fin n) (y : X) : Fin n → Bool :=
  Tagged.WidePadding.pad (fun i=>i∈Set.range place)
    ((Equiv.arrowCongr (Equiv.ofInjective place place.injective) (Equiv.refl Bool)) (bits y))

def packedMiddle (place : SiteBit (row.output c) s ↪ Fin n) (y : State (row.output c) s) : Fin n → Bool :=
  packState (siteBits (row.output c) s) place y

private theorem sumMasked {X : Type} [Fintype X] (used : Fin n → Prop)
    (enum : X ≃ ({i // used i} → Bool)) (weight : (Fin n → Bool) → F) :
    (∑d : Fin n → Bool, if ∀i,d i=true → used i then weight d else 0) =
      ∑y : X, weight (Tagged.WidePadding.pad used (enum y)) := by
  exact (Tagged.WidePadding.sum_padded used weight).trans
    (enum.sum_comp (fun d => weight (Tagged.WidePadding.pad used d))).symm

private def maskWeight {B : Type} (place : B ↪ Fin n) (d : Fin n → Bool) (w : F) : F :=
  if ∀i,d i=true → i∈Set.range place then w else 0

private theorem sumPackedState {X B : Type} [Fintype X] (bits : X ≃ (B → Bool)) (place : B ↪ Fin n)
    (weight : (Fin n → Bool) → F) :
    (∑d : Fin n → Bool, maskWeight place d (weight d)) =
      ∑y : X, weight (packState bits place y) := by
  exact sumMasked (fun i => i ∈ Set.range place)
    (bits.trans (Equiv.arrowCongr (Equiv.ofInjective place place.injective) (Equiv.refl Bool))) weight

set_option maxHeartbeats 1400000 in
theorem hidden_entry (valid packet install : Net) (v : V → Bool)
    (place : SiteBit (row.output c) s ↪ Fin n) (a : State row.input s) (b : State (R.post c) s)
    (occupied : ∀d,TypedWiring.value valid (Sum.elim v d)=
      if ∀i,d i=true → i∈Set.range place then (1:F) else 0)
    (signed : ∀y,TypedWiring.value packet (Sum.elim v (packedMiddle c s place y))=row.entry c s a y)
    (routed : ∀y,TypedWiring.value install (Sum.elim v (packedMiddle c s place y))=
      Installs.transport (R.shape c) rfl (R.install.operator R.order (R.bits c) R.ordinal) s y b) :
    TypedWiring.value (hiddenEntry valid packet install) v=R.entry c s a b := by
  let used := fun i=>i∈Set.range place
  let φ := fun d=>TypedWiring.value packet (Sum.elim v d)*TypedWiring.value install (Sum.elim v d)
  calc
    _ = ∑d : Fin n → Bool,maskWeight place d (φ d) := by
      rw [hiddenEntry_sum]
      apply Finset.sum_congr rfl
      intro d _
      change TypedWiring.value valid (Sum.elim v d)*φ d=_
      rw [occupied, maskWeight]
      by_cases yes : ∀i, d i=true → used i
      · rw [ite_eq_left yes, ite_eq_left yes, one_mul]
      · rw [ite_eq_right yes, ite_eq_right yes, zero_mul]
    _ = ∑y : State (row.output c) s,φ (packedMiddle c s place y) := by
      unfold packedMiddle
      exact sumPackedState (F:=F) (X:=State (row.output c) s) (B:=SiteBit (row.output c) s)
        (siteBits (row.output c) s) place φ
    _ = R.entry c s a b := by
      change _=∑y, _ * _
      apply Finset.sum_congr rfl
      intro y _
      exact (congrArg₂ (·*·) (signed y) (routed y)).trans (mul_comm _ _)

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
