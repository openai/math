import OAI.Computability.NearSquareRoot.PhysicalWalshEffectiveRoutes
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapUpper
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareStage
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeRouted

/-! # Emitting the midpoint Walsh pieces from named native stages -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshEffectiveRoutes
open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode
open CommonRegisters GeneratorSyntax KernelPass KernelPass.ComputableSyntax
open PhysicalWalshCompile.Dispatch (Selected dimensions)
open PhysicalWalshCompileInterior (worldPrefix worldBits worldRow)

/-- The two statements required of the native rectangle and XOR-stage files at
a chosen exponent. Their descriptor polynomial degrees need not agree. -/
def Native (rect stage : Cmd) (ρ : ℝ) : Prop :=
  (∃ D, InterchangeROMBinary.RectPhysical rect ρ D) ∧
  ∃ D, XorWindow.StagesAt PhysicalWalshCompileInteriorHeader.nativeRegime worldPrefix worldBits worldRow ρ D stage

variable {Z : Type} [Primcodable Z]

/-- Generate a complete router for every opcode first. A native rate for a
particular calibration certifies every off-diagonal gate at that rate. -/
theorem compileNative (rect stage : Z → Cmd) (er : Effective ltr rect) (es : Effective ltr stage)
    (R S : ℕ) (rr : ∀ z, Within R (rect z)) (rs : ∀ z, Within S (stage z)) :
    ∃ (route : Z × Raw → Op → Cmd) (M E : ℕ), Effective ltr (Function.uncurry route) ∧
      (∀ k op, Within M (route k op)) ∧ ∀ z a W ops d ρ, 4 ≤ a → E ≤ d →
        (Packed.decode (a+1) ops).i = W → 0 ≤ ρ → ρ ≤ 1 → Native (rect z) (stage z) ρ →
        PhysicalWalshCompile.Dispatch.XorRuns (fun raw => route (z,raw)) a W ops
          (nodeScan a W d (extra a W ρ)) (nodeArena a W d) := by
  obtain ⟨high,H,h,eh,rh,upper⟩ := PhysicalWalshCompileSwapUpper.compileSquare rect er R rr
  obtain ⟨front,F,f,ef,_,_,rf,frontRun⟩ := FrontDispatch.compileSquareFromStage
    (Prod.snd : Z × Raw → Raw) Computable.snd (stage ∘ Prod.fst) (es.comp Computable.fst)
    S (fun z => rs z.1)
  obtain ⟨route,M,e,em,rm,allRows⟩ := compile high front eh ef H F rh rf
  refine ⟨route,M,max (max h f) e,em,rm,?_⟩
  intro z a W ops d ρ ha hd width pos le cert
  obtain ⟨⟨D,rd⟩,st⟩ := cert
  exact allRows z a W ops d ρ ha ((le_max_right ..).trans hd) width
    (upper z a W ops width d ((le_max_left ..).trans ((le_max_left ..).trans hd)) ρ D pos rd)
    (frontRun (z,a+1,ops) ρ a W ops ha rfl width le st d ((le_max_right ..).trans ((le_max_left ..).trans hd)))

/-- Exponent selected by the midpoint templates. -/
noncomputable def midpointRate (j : ℕ) : ℝ := ((j+3 : ℕ) : ℝ)/(2*(j+2) : ℕ)

theorem midpoint_range (j : ℕ) : 1/2 < midpointRate j ∧ midpointRate j ≤ 1 := by
  unfold midpointRate
  push_cast
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ (by positivity)]
    linarith [Nat.cast_nonneg (α:=ℝ) j]

noncomputable def localConstant (j : ℕ) : ℝ := 74*(4+(2:ℝ)^(midpointRate j)+5505)

/-- A single computable family of recursive Walsh pieces uses one register
bound and one descriptor degree, through every chosen prime or native file.
Its state packets are the actual midpoint plan input and output. -/
theorem midpoint (rect stage : Z → Cmd) (er : Effective ltr rect) (es : Effective ltr stage)
    (R S : ℕ) (rr : ∀ z, Within R (rect z)) (rs : ∀ z, Within S (stage z)) :
    ∃ (s : ℕ → Raw) (cmd : Z × ℕ → Cmd) (M D : ℕ), Computable s ∧
      Computable (dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧ Effective ltr cmd ∧
      0 < M ∧ 1 ≤ D ∧ (∀ k, Within M (cmd k)) ∧
      ∃ sel : (j : ℕ) → Selected (j+3) (2*(j+2)) (s j), ∀ j d, D ≤ d →
        let a := (dimensions (s j)).1
        let W := (dimensions (s j)).2
        let p := (sel j).plan
        let hw : 0 < W := by have := (sel j).wide; dsimp [W]; omega
        ∃ K : ℕ, 1 ≤ K ∧ ∀ z, Native (rect z) (stage z) (midpointRate j) →
          ∃ B : ℝ, 0 ≤ B ∧ EffectiveBoundedTask.Runs (cmd (z,j))
            (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls (midpointRate j) B RouterClock.logWidth
              (envelopeSetup K d (fun _ => 0)) v.val.shape)
            (fun v => pieceSpaceBound (a+1) (4*K+localConstant j)
              (envelopeSetup K d (fun _ => 0)) v.val.shape)
            (rawInput hw p) (rawOutput hw p) := by
  obtain ⟨route,N,E,hc,rc,runs⟩ := compileNative rect stage er es R S rr rs
  obtain ⟨s,cmd,M,D,hs,hd,hcut,he,hM,hD,reg,sel,body⟩ :=
    PhysicalWalshCompile.Node.compileRoutedWith route hc N rc
  refine ⟨s,cmd,M,max D E,hs,hd,hcut,he,hM,hD.trans (le_max_left ..),reg,sel,?_⟩
  intro j d bound a W p hw
  obtain ⟨K,hK,calls⟩ := body j d ((le_max_left ..).trans bound)
  have large : 4 ≤ a := by have := (sel j).large; dsimp [a]; omega
  have width : (Packed.decode (a+1) (s j).2).i = W := congrArg Packed.i (sel j).decode
  have rate := midpoint_range j
  refine ⟨K,hK,fun z native => ?_⟩
  have routes := runs z a W (s j).2 d (midpointRate j) large ((le_max_right ..).trans bound)
    width (by linarith only [rate.1]) rate.2 native
  exact calls z _ routes (localConstant j) RouterClock.logWidth (fun _ => 0)
    (by unfold localConstant; positivity) RouterClock.one_le_logWidth (fun _ => le_rfl)
    (fun t ok => extra_bound (by omega) rate.1.le rate.2 t ok)

end PhysicalWalshEffectiveRoutes

end NearSquareRoot
end Computability
end OAI
