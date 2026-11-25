import OAI.Hierarchy.TaggedWireChosenPackets
import OAI.Hierarchy.TaggedWireChordRouter

namespace OAI
/-! # Routed installation of the generated role and selector widths -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe
open scoped BigOperators Classical
variable {S N : ℕ} {I : Type} [Fintype I] {F : Type} [Field F]

structure Installs (source : I→Chord S) (phys : Fin N→Chord S) where
  route : I→List (Fin N)
  path : ∀i,Traverses (rowGraph phys) (source i).1.1 (route i) (source i).1.2

namespace Installs
variable {source : I→Chord S} {phys : Fin N→Chord S} (R : Installs source phys)

def load (bits : I→ℕ) (e : Fin N) := ∑i,(R.route i).count e*bits i

variable (order : Fin (Fintype.card I)≃I)
def starts := source ∘ order
def steps := R.route ∘ order
def numbered (bits : I→ℕ) := bits ∘ order

theorem packed (bits : I→ℕ) : installedWidths (starts (source:=source) order) (numbered order bits)=optionWidths source bits := by
  unfold installedWidths starts numbered optionWidths
  simp only [Function.comp_apply,unitChord,Finsupp.smul_single,smul_eq_mul,Nat.mul_one]
  exact order.sum_comp (fun i : I => (Finsupp.single (source i) (bits i) : Widths S))

theorem counted (bits : I→ℕ) : routeLoad (R.steps order) (numbered order bits)=R.load bits := by
  funext e
  exact order.sum_comp (fun i=>(R.route i).count e*bits i)

def transport {U V U' V' : Widths S} (left : U=U') (right : V=V')
    (M : SiteMatrix (State U) (State V) F) : SiteMatrix (State U') (State V') F :=
  left ▸ right ▸ M

theorem transported {U V U' V' : Widths S} (left : U=U') (right : V=V')
    (M : SiteMatrix (State U) (State V) F)
    (law : ∀x,(raw F U).coeff x=SiteMatrix.act M (raw F V).coeff x)
    (x : ∀s,State U' s) :
    (raw F U').coeff x=SiteMatrix.act (transport left right M) (raw F V').coeff x := by
  subst U' V'
  exact law x

def operator (bits : I→ℕ) {r : ℕ} (ordinal : Fin r≃Σi,Fin ((R.steps order) i).length) :
    SiteMatrix (State (optionWidths source bits)) (State (installedWidths phys (R.load bits))) F :=
  transport (packed order bits) (congrArg (installedWidths phys) (R.counted order bits))
    (chordRouter _ phys _ _ ordinal (fun i=>R.path (order i)))

theorem operator_action (bits : I→ℕ) {r : ℕ} (ordinal : Fin r≃Σi,Fin ((R.steps order) i).length)
    (x : ∀s,State (optionWidths source bits) s) :
    (raw F (optionWidths source bits)).coeff x=
      SiteMatrix.act (R.operator order bits ordinal) (raw F (installedWidths phys (R.load bits))).coeff x :=
  transported (packed order bits) (congrArg (installedWidths phys) (R.counted order bits)) _
    (chordRouter_action _ phys _ _ ordinal (fun i=>R.path (order i))) x

/-- A physical link can be occupied by several roles and several positions
of one role. The chart's archive bills every one of those occurrences. -/
theorem counts (bits : I→ℕ) (e : Fin N) (hits : I→ℕ)
    (read : ∀i,0<bits i→(R.route i).count e=hits i) :
    R.load bits e=∑i,hits i*bits i := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases pos : 0<bits i
  · rw [read _ pos]
  · simp [Nat.eq_zero_of_not_pos pos]

end Installs

theorem option_pair {A B : Type} [Fintype A] [Fintype B] (a : A→Chord S) (b : B→Chord S)
    (w : A→ℕ) (t : B→ℕ) :
    optionWidths (Sum.elim a b) (Sum.elim w t)=optionWidths a w+optionWidths b t := by
  simp [optionWidths,Fintype.sum_sum_type]

end Hierarchy.WireTelescope.ChosenPackets

end
end OAI
