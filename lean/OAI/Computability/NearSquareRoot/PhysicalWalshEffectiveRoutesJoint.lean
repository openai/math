import OAI.Computability.NearSquareRoot.PhysicalWalshEffectiveRoutesNative
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareStageJoint
import OAI.Computability.NearSquareRoot.PhysicalWalshFlatTotalFibres

/-! # Coarse and sharp guarantees for the same generated Walsh router -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshEffectiveRoutes
open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode
open CommonRegisters GeneratorSyntax KernelPass.ComputableSyntax
open PhysicalWalshCompileInterior (worldPrefix worldBits worldRow)

/-- A working rectangular swap and a terminating front stage suffice, even
if the stage fails the selected exponent's cost certificate. -/
def Operational (rect stage : Cmd) :=
  (∃ (ρ : ℝ) (D : ℕ), 0 ≤ ρ ∧ InterchangeROMBinary.RectPhysical rect ρ D) ∧
  XorWindow.StagesTotal PhysicalWalshCompileInteriorHeader.nativeRegime worldPrefix worldBits worldRow stage

variable {Z : Type} [Primcodable Z]

theorem compileJoint (rect stage : Z → Cmd) (er : Effective ltr rect) (es : Effective ltr stage)
    (R S : ℕ) (rr : ∀ z, Within R (rect z)) (rs : ∀ z, Within S (stage z)) :
    ∃ (route : Z × Raw → Op → Cmd) (M E : ℕ), Effective ltr (Function.uncurry route) ∧
      (∀ k op, Within M (route k op)) ∧ ∀ z a W ops d, 4 ≤ a → E ≤ d →
        (Packed.decode (a+1) ops).i = W →
        (Operational (rect z) (stage z) → ∃ b : PhysicalWalshNode.Shape → ℕ,
          PhysicalWalshCompile.Dispatch.XorRuns (fun raw => route (z,raw)) a W ops b b) ∧
        ∀ ρ, 0 ≤ ρ → ρ ≤ 1 → Native (rect z) (stage z) ρ →
          PhysicalWalshCompile.Dispatch.XorRuns (fun raw => route (z,raw)) a W ops
            (nodeScan a W d (extra a W ρ)) (nodeArena a W d) := by
  obtain ⟨high,H,h,eh,rh,upper⟩ := PhysicalWalshCompileSwapUpper.compileSquare rect er R rr
  obtain ⟨front,F,f,ef,_,_,rf,frontRun,frontTotal⟩ := FrontDispatch.compileSquareFromStageJoint
    (Prod.snd : Z × Raw → Raw) Computable.snd (stage ∘ Prod.fst) (es.comp Computable.fst) S (fun z => rs z.1)
  obtain ⟨route,M,e,em,rm,allRows⟩ := compileAt high front eh ef H F rh rf
  refine ⟨route,M,max (max h f) e,em,rm,?_⟩
  intro z a W ops d ha hd width
  have rhigh : h ≤ d := (le_max_left ..).trans ((le_max_left ..).trans hd)
  have rfront : f ≤ d := (le_max_right ..).trans ((le_max_left ..).trans hd)
  have source := allRows z a W ops d ha ((le_max_right ..).trans hd) width
  let prefixClock := ElementarySweep.prefixExtra (a+1) (PhysicalWalshCompileElementaryRelease.gradedCut (a+1))
  have low (ρ : ℝ) (s) : nodeScan a W d prefixClock s ≤ nodeScan a W d (extra a W ρ) s :=
    Nat.add_le_add_left ((Nat.le_add_right ..).trans (Nat.le_add_right ..)) _
  have wide (ρ : ℝ) (s) : nodeScan a W d (SlotSwap.wideExtra ρ (a+1)) s ≤ nodeScan a W d (extra a W ρ) s :=
    Nat.add_le_add_left ((Nat.le_add_left ..).trans (Nat.le_add_right ..)) _
  constructor
  · rintro ⟨⟨ρ,D,hρ,rectOK⟩,st⟩
    obtain ⟨b,fg⟩ := PhysicalWalshCompileXorPacket.priceByShape (frontTotal (z,a+1,ops) a W ops ha rfl width st)
    let time := nodeScan a W d (extra a W ρ)
    let budget (s : PhysicalWalshNode.Shape) := time s+b s
    have area (s) : nodeArena a W d s ≤ budget s := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
    refine ⟨budget,source budget budget area (fun _ => le_rfl) (fun s => (low ρ s).trans (Nat.le_add_right ..)) ?_ ?_⟩
    · intro u v lt
      exact (upper z a W ops width d rhigh ρ D hρ rectOK u v lt).mono
        (fun t => (wide ρ t.shape).trans (Nat.le_add_right ..)) (fun t => area t.shape)
    · exact fg.mono (fun _ => Nat.le_add_left ..) (fun _ => Nat.le_add_left ..)
  · rintro ρ hρ le ⟨⟨D,rectOK⟩,st⟩
    apply source _ _ (fun _ => le_rfl) (fun _ => Nat.le_add_right ..) (low ρ)
    · intro u v lt
      exact (upper z a W ops width d rhigh ρ D hρ rectOK u v lt).mono
        (fun t => wide ρ t.shape) (fun _ => le_rfl)
    · exact (frontRun (z,a+1,ops) ρ a W ops ha rfl width le st d rfront).mono
        (fun _ => Nat.add_le_add_left (Nat.le_add_left ..) _) (fun _ => le_rfl)

end PhysicalWalshEffectiveRoutes

end NearSquareRoot
end Computability
end OAI
