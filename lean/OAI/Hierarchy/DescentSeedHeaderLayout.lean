import OAI.Hierarchy.DescentSeedPublicFront
import OAI.Hierarchy.DescentSeedChosenLayoutCore
import OAI.Hierarchy.DescentRoundQuota
import OAI.Hierarchy.DescentTerminalAppendixNumbers
import OAI.Hierarchy.DescentSeedNodeChart
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentSeedHeaderFloorNumbers

namespace OAI
/-! # The original seed header, native register layout and first free address -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader
open DescentCompiler DescentSixParty DescentWideSeedFlags DescentPackedEpochShelves
open DescentTerminalEpochChart DescentInitialHost DescentExterior Catalyst
noncomputable section
variable {F : Type} [Field F]

/-- The fixed terminal portion of the input before any native code runs. -/
structure Appendix where
  bins : ℕ
  binWidth : ℕ
  arity : ℕ
  piece : ℕ
  codes : ℕ
  raw : ℕ

def Appendix.words (u : Appendix) (outer : ℕ) :=
  DescentTerminalPublicIdentity.total u.bins u.binWidth u.arity u.piece u.codes u.raw outer

structure Input (F : Type) [Field F] where
  arity : ℕ
  pins : ℕ
  circuit : Approximation F arity pins
  labels : Type
  steps : List (Source labels)
  appendix : Appendix
  schedule : AtomSchedule
  k : ℕ
  tail : ℕ
  p : ℕ
  degree : ℕ
  wire : ℕ
  hist : ℕ
  hosts : ℕ
  j : ℕ
  rest : ℕ

variable (G : PoweredGadget F) (op : RotorSpec) (t f g drift : ℕ)
namespace Input
variable (v : Input F)

def width := v.schedule.firstWidth G.b v.p

def base (h : ℕ) :=
  let lo:=selectorBase v.circuit v.schedule.copies (v.width G) h v.steps.length
  let pitch:=grain (h/2) G.C
  let work:=publicFront v.circuit v.schedule.copies (v.width G) h G.C v.steps v.j v.rest+
    v.appendix.words (ExteriorCount v.circuit*2^(v.j+v.rest))
  work+((shelves pitch lo 0 v.steps).map (stepRows pitch)).sum+2

theorem header_after_votes (h : ℕ) :
    let lo:=selectorBase v.circuit v.schedule.copies (v.width G) h v.steps.length
    let pitch:=grain (h/2) G.C
    let work:=publicFront v.circuit v.schedule.copies (v.width G) h G.C v.steps v.j v.rest+
      v.appendix.words (ExteriorCount v.circuit*2^(v.j+v.rest))
    work≤v.base G h-1 ∧ work+((shelves pitch lo 0 v.steps).map (stepRows pitch)).sum<v.base G h-1 :=by
  dsimp only [base]
  omega

def layout (h : ℕ) := selectedLayout G v.schedule h v.k v.tail g v.p drift v.degree f (quota t)
  (v.base G h) (v.schedule.censusBits v.p) v.wire v.hist

def floor (h : ℕ) :=
  let l:=v.layout G t f g drift h
  let groups:=v.schedule.groupCount 0
  let M:=Primitive.paletteLanes G op (v.width G) (v.schedule.grainAt G.b v.p 0) h v.k
  Primitive.initialEnd v.circuit v.schedule.copies (v.width G) h v.k v.hosts groups M
    ((DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts groups).seedEnd
      (endAddress v.circuit l v.hosts groups v.k))

end Input
end
end Hierarchy.DescentDatedSeedStartup.SeedHeader

end OAI
