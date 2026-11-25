import OAI.Hierarchy.DescentPackedRectanglePins
import OAI.Hierarchy.DescentPackedWalshPasses
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Executable fixed tables for the pre-estimator site transform and rectangle -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Geometry
open DescentPackedWalsh DescentPackedRectangle DescentPackedColony.Phase DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Plan where
  hosts : ℕ
  ports : ℕ
  high : ℕ
  low : ℕ
  bits : ℕ
  origin : ℕ
  pitch : ℕ
  f : ℕ
  budget : ℕ
  classes : ℕ

variable (G : Plan) {w : ℕ}
local notation "H" => G.hosts
local notation "D" => G.ports
local notation "u" => G.high
local notation "l" => G.low
local notation "m" => u+l
local notation "axes" => List.map (@DescentPackedWalsh.axis u l) (axesList u l)
local notation "zero" => (fun _ : ℕ=>(0:Word w))
namespace Plan

def «meta» := G.origin+m*span H u l G.bits
def pointers := G.meta+words H u l D
def stop := G.pointers+H

def value (a : ℕ) : Word w :=
  if a<G.meta then mounted H G.bits G.origin axes zero a
  else if a<G.pointers then mount G.meta G.pitch G.f G.budget G.classes H u l D zero a
  else if p : a-G.pointers<H then ((DescentPackedWalsh.row (⟨a-G.pointers,p⟩:Fin H) (fun _ : Fin u=>false)).val:Word w)
  else 0

def image : Arena.Image w := ⟨G.origin,G.stop,G.value⟩

end Plan

export Plan («meta» pointers stop value image)

structure Resident (out : Memory w) : Prop where
  walsh (a : ℕ) : out a=mounted H G.bits G.origin axes out a
  sparse (a : ℕ) (lo : G.meta≤a) (hi : a<G.pointers) :
    out a=mount G.meta G.pitch G.f G.budget G.classes H u l D zero a
  keys (v : Fin H) : out (G.pointers+v.val)=((DescentPackedWalsh.row v (fun _ : Fin u=>false)).val:Word w)

abbrev Plan.Resident (G : Plan) {w : ℕ} (out : Memory w) : Prop :=
  Geometry.Resident G out

theorem run (mem : Memory w) (space : G.stop<2^w) :
    let I:=G.image (w:=w)
    I.program.Exec mem (I.output mem) (4+10*I.length) ∧ Resident G (I.output mem) ∧ CheapCode I.program ∧
    DescentStaticWordColumn.names I.program=15*(I.length+1) ∧
    ∀a,a<G.origin ∨ G.stop≤a→I.output mem a=mem a := by
  intro I
  have bounds : G.origin≤G.meta ∧ G.meta≤G.pointers ∧ G.pointers≤G.stop:=
    ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩
  obtain ⟨ran,stored,frame⟩:=I.issue mem (by change G.origin+(G.stop-G.origin)<_;omega)
  refine ⟨ran,⟨?_,?_,?_⟩,I.hardware.1,I.hardware.2,frame⟩
  · intro a
    by_cases low : G.origin ≤ a
    · cases atRow : axes[(a-G.origin)/span H u l G.bits]? with
      | none => simp only [mounted, ite_eq_left low, atRow]
      | some ax =>
        have positive : 0 < span H u l G.bits := by unfold span; positivity
        have valid : (a-G.origin)/span H u l G.bits < List.length axes := by
          by_contra! late
          rw [List.getElem?_eq_none late] at atRow
          contradiction
        have len : List.length axes = u+l := by simp [axesList]
        have delta := (Nat.div_lt_iff_lt_mul positive).mp valid
        rw [len] at delta
        have hit : a < G.meta := by
          change a < G.origin+(u+l)*span H u l G.bits
          omega
        exact (stored a low ((hit.trans_le bounds.2.1).trans_le bounds.2.2)).trans (by
          change G.value a = mounted H G.bits G.origin axes (I.output mem) a
          simp only [Plan.value, ite_eq_left hit, mounted, ite_eq_left low, atRow])
    · simp only [mounted, ite_eq_right low]
  · intro a lo hi
    exact (stored a (bounds.1.trans lo) (hi.trans_le bounds.2.2)).trans (by
      change G.value a = _
      simp only [Plan.value, ite_eq_right (Nat.not_lt_of_ge lo), ite_eq_left hi])
  · intro v
    have below : G.pointers+v.val < G.stop := Nat.add_lt_add_left v.isLt _
    have above : G.pointers ≤ G.pointers+v.val := Nat.le_add_right ..
    exact (stored _ ((bounds.1.trans bounds.2.1).trans above) below).trans (by
      change G.value (G.pointers+v.val) = _
      simp only [Plan.value, ite_eq_right (Nat.not_lt_of_ge (bounds.2.1.trans above)),
        ite_eq_right (Nat.not_lt_of_ge above), Nat.add_sub_cancel_left, dite_eq_left v.isLt])

theorem length : (G.image (w:=w)).length=(u+l)*span H u l G.bits+words H u l D+H := by
  simp [image,Arena.Image.length,stop,pointers,«meta»,Nat.add_assoc]

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Geometry

end OAI
