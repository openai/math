import OAI.Hierarchy.TaggedWireElectionRows
import OAI.Hierarchy.TaggedWireStripTender

namespace OAI
/-! # A physically routed packet or the unique empty route at every original candidate -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open ProtocolRAM Calendar PurchaseStage ChosenPackets Probe Tagged AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing

namespace ChosenPackets.RowRouting
section Retyped
variable {F : Type} [Field F] {S N t H r : ℕ} (P : Placed F S) {phys : Fin N→Chord S}
    (letters : H=P.data.terms) (copies : r=t) (T : RowRouting (Row.packet P t) phys)

def retyped : RowRouting (Row.retype P letters r) phys := by
  subst H r
  exact T

theorem retyped_load (c : Histogram (Fin H) r) (e : Fin N) :
    let r₀:=retyped P letters copies T
    r₀.install.load (r₀.bits c) e=T.install.load (T.bits (cast (congrArg₂ (fun n t=>Histogram (Fin n) t) letters copies) c)) e := by
  subst H r
  rfl

end Retyped

variable {F : Type} [Field F] {S N r : ℕ}
def dormant (phys : Fin N→Chord S) (letters : ℕ) (mass : r=0) :
    RowRouting (Row.passive (F:=F) (S:=S) letters mass) phys := by
  subst r
  exact RowRouting.skipped (F:=F) phys letters

theorem dormant_load (phys : Fin N→Chord S) (letters : ℕ) (mass : r=0)
    (c : Histogram (Fin letters) r) (e : Fin N) :
    let r₀:=RowRouting.dormant (F:=F) phys letters mass
    r₀.install.load (r₀.bits c) e=0 := by
  subst r
  simp [dormant,skipped,Installs.load]

section Conditional
variable {H t : ℕ} {phys : Fin N → Chord S} {p : Prop} [dp : Decidable p]
    {yes : p → Row F S H t} {no : (¬p) → Row F S H t}
    (on : ∀ h, RowRouting (yes h) phys) (off : ∀ h, RowRouting (no h) phys)

private def conditionalRouting : RowRouting (if h : p then yes h else no h) phys := by
  cases dp with
  | isTrue h => exact on h
  | isFalse h => exact off h

private theorem conditionalRouting_load (c : Histogram (Fin H) t) (e : Fin N) :
    let rt := conditionalRouting on off
    rt.install.load (rt.bits c) e =
      if h : p then (on h).install.load ((on h).bits c) e
      else (off h).install.load ((off h).bits c) e := by
  cases dp <;> rfl
end Conditional

end ChosenPackets.RowRouting

namespace CalendarTape.HistogramFormat
variable {F X : Type} [Field F] {S N W q d : ℕ} {C : Chart W q d} (D : HistogramFormat C X)
    (a : Attempt) (x : X) (m : Memory W) (phys : Fin N→Chord S)
local notation "b" => enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)
local notation "snap" => HistogramShelf.snapshot C a m
local notation "I" => Fin (C.layout a).candidates
local notation "elected" => fun i:I=>(b).selected snap (i.val:Word W)

variable (view : D.observed a x m)
    (menu : ∀i : Fin (C.layout a).candidates,
      (enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).selected
        (HistogramShelf.snapshot C a m) (i.val:Word W) → Placed F S)
    (arity : ∀i hi,(menu i hi).data.terms=
      ((enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).termCount.read
        (HistogramShelf.snapshot C a m)
        ((enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).packet.eval
          (HistogramShelf.snapshot C a m) (i.val:Word W))).val)
    (route : ∀i hi,RowRouting (Row.packet (menu i hi)
      (enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)).copies) phys)

def electedTender (i : I) : RowRouting (D.electedRow a x m view menu arity i) phys :=
  RowRouting.conditionalRouting (p := elected i)
    (fun picked => RowRouting.retyped (menu i picked) ((view.1 i).trans (arity i picked).symm)
      ((view.2 i).trans (ite_eq_left picked)) (route i picked))
    (fun missed => RowRouting.dormant (F:=F) phys (D.letters a x i) ((view.2 i).trans (ite_eq_right missed)))

theorem elected_load (i : I) (c : Histogram (Fin (D.letters a x i)) (D.copies a x i)) (e : Fin N) :
    let T:=D.electedTender a x m phys view menu arity route i
    T.install.load (T.bits c) e=
      if hi:elected i then let P:=route i hi
        let letters:=(view.1 i).trans (arity i hi).symm
        let copies:=(view.2 i).trans (ite_eq_left hi)
        P.install.load (P.bits (cast (congrArg₂ (fun h r=>Histogram (Fin h) r) letters copies) c)) e
      else 0 := by
  refine (RowRouting.conditionalRouting_load (p := elected i)
    (fun picked => RowRouting.retyped (menu i picked) ((view.1 i).trans (arity i picked).symm)
      ((view.2 i).trans (ite_eq_left picked)) (route i picked))
    (fun missed => RowRouting.dormant (F:=F) phys (D.letters a x i) ((view.2 i).trans (ite_eq_right missed)))
    c e).trans ?_
  by_cases picked : elected i
  · simp only [dite_eq_left picked]
    exact RowRouting.retyped_load (menu i picked) ((view.1 i).trans (arity i picked).symm)
      ((view.2 i).trans (ite_eq_left picked)) (route i picked) c e
  · simp only [dite_eq_right picked]
    exact RowRouting.dormant_load (F:=F) phys (D.letters a x i) ((view.2 i).trans (ite_eq_right picked)) c e

end CalendarTape.HistogramFormat
end Hierarchy.WireTelescope

end
end OAI
