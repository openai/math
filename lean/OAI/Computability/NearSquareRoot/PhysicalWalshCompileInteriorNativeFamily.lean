import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorNative
import OAI.Computability.NearSquareRoot.PhysicalWalshXorSquare
import OAI.Computability.NearSquareRoot.PhysicalWalshXorGateCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorDuskCommand

/-! # Compiling a family of named native gates for the large Walsh interior -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code Space Strip PhysicalWalsh PhysicalWalshNode Interior SwapPrefix
open PhysicalWalshCompileSwapRulers (World)
open PhysicalWalshCompileInteriorHeader (nativeRegime native_scale_le)
open Controlled.PositionProgram PhysicalWalsh.XorThreshold CommonRegisters GeneratorSyntax

def worldPrefix (t : World) := P (t.a+1) t.W t.shape
def worldSlot (t : World) := L (t.a+1) t.shape
def worldBits (t : World) := 3*worldSlot t
def worldCells (t : World) := S t.a t.shape*(2*(t.shape.w+1))
def worldRow (t : World) := Series.natural (worldCells t)

/-- Execution contract at the native interpreter boundary, jointly in all
template arities, layout parameters, and record widths. -/
abbrev WorldGate (ρ : ℝ) (D : ℕ) (cmd : Cmd) :=
  XorWindow.GateAt nativeRegime worldPrefix worldBits worldRow ρ D cmd

/-- Execute on a shape class satisfying the two native capacity inequalities.
The extra cost width is a constant of the named program. The row, the native
header and the enclosing time and space functions use their actual widths. -/
theorem nativeOfGateOn {ρ : ℝ} {D : ℕ} {c : Cmd} (gate : WorldGate ρ D c)
    (a W e : ℕ) (ha : 4 ≤ a) (pred : Shape → Prop)
    (reserve : ∀ s, pred s → Controlled.payloadBits D (Header.scale (a+1) s) ≤ B a s + e)
    (prefixSize : ∀ s, pred s → factor ρ (L (a+1) s) ≤ 2^P (a+1) W s) :
    NativeOn a W ρ pred (XorWindow.duskCmd c) := by
  let I := {u : XorInput W // pred u.shape}
  let s (i : I) := i.val.shape
  let pick (i : I) : World := ⟨a,W,0,0,D,s i⟩
  let p (i : I) := P (a+1) W (s i)
  let l (i : I) := L (a+1) (s i)
  let stride (i : I) := S a (s i)
  let width (i : I) := (s i).w
  let x (i : I) := extend (a+1) W (s i) i.val.row
  let bits (i : I) := B a (s i)
  let m (i : I) := (s i).suff*(2*(width i+1))
  let q (i : I) := Header.scale (a+1) (s i)
  let price (i : I) := factor ρ (l i)
  let v (i : I) := XorReserve.volume (p i) (3*l i) (bits i) (m i)
  let time (i : I) := gateClock ρ (l i) (v i)
  have vg (i : I) : v i = volume a W (s i) := volume_eq a W ha (s i) i.val.positive
  have shape (i : I) : 2^(p i+3*l i)*stride i = paddedSize (a+1) W (s i) :=
    rows_mul_S (W:=W) ha i.val.positive
  have positive (i : I) : 0 < stride i := Nat.mul_pos (s i).suff_pos (Nat.two_pow_pos _)
  have cost (i : I) : v i ≤ time i := (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans
    ((Nat.le_mul_of_pos_left _ (by omega : 0 < 4+3*Controlled.guardWidth (3*l i))).trans (Nat.le_succ _))
  have io (i : I) : (2^(p i+3*l i)*stride i+1)*(width i+1) ≤ v i := by
    rw [shape,vg]
    have pos := Nat.mul_pos (Nat.two_pow_pos (p i+3*l i)) (positive i)
    rw [shape] at pos
    have b := Nat.mul_le_mul_right (width i+1)
      (show paddedSize (a+1) W (s i)+1 ≤ paddedSize (a+1) W (s i)*2 by omega)
    simpa only [Interior.volume,width,Nat.mul_assoc] using b
  have stage := gate pick (fun i => bits i+e) m q price
    (fun i => by
      rw [worldRow,Series.count_natural]
      apply le_trans (b:=XorReserve.pack (bits i) (m i)) _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right ..)))
      apply le_of_eq
      change ((s i).suff*2^(bits i))*(2*((s i).w+1)) = 2^(bits i)*m i
      dsimp only [m,width]; ring)
    (fun i => native_scale_le (pick i) ha i.val.positive) (fun i => Nat.mul_pos (s i).suff_pos (by omega))
    (fun i => reserve (s i) i.property)
    (fun i => factor_pays ρ worldSlot (pick i))
    (fun i => prefixSize (s i) i.property)
  let selectRow (i : I) : (j:I) × XorWindow.Input (worldPrefix (pick j)) (worldBits (pick j)) (Fin (worldCells (pick j))) :=
    ⟨i,XorWindow.duskRow (P:=p i) (L:=l i) (S:=stride i) (x i)⟩
  have body := stage.on selectRow
  have pass := XorWindow.duskOfGateNamed p l stride width positive (fun i => nativeRegime.header (pick i))
    time v cost x io (c:=c) (by
      apply XorSquare.actual_runs ρ p (fun i => 3*l i) bits m l e
      obtain ⟨C,body⟩ := body
      refine ⟨C,fun i env park base room => ?_⟩
      have fit := body i env park base room
      dsimp only [Function.comp_apply,selectRow,worldBits] at fit
      rw [Nat.mul_div_cancel_left _ (by decide : 0 < 3)] at fit
      exact fit)
  have tEq (i : I) : time i = extra a W ρ (s i) := congrArg (gateClock ρ (l i)) (vg i)
  obtain ⟨C,pass⟩ := pass
  refine ⟨C,fun i env park base room => ?_⟩
  have run := pass i env park base room
  dsimp only at run
  rw [tEq,vg,shape] at run
  exact run

/-- The original native reserve is the special case with no extra cost width. -/
theorem nativeOfGate {ρ : ℝ} (upper : ρ ≤ 1) {D : ℕ} {c : Cmd} (gate : WorldGate ρ D c) :
    Native ρ D (XorWindow.duskCmd c) := by
  intro a W ha
  apply nativeOfGateOn gate a W 0 ha
  · intro s h
    simpa only [B,Nat.add_zero,show a+1-4=a-3 by omega] using
      payload_le_suffix (A:=a+1) (by omega) h
  · intro s h
    exact factor_le_prefix upper h (Nat.le_add_left ..)

/-- The register bound is raised by one fixed tuple of codec commands for
the entire parameterized family, independently of the exponents and degrees. -/
theorem nativeFamily {J : Type} [Primcodable J] {ρ : J → ℝ} {D : J → ℕ} (le : ∀ j, ρ j ≤ 1)
    {gate : J → Cmd} (effective : Effective ltr gate) (R : ℕ) (regs : ∀ j, Within R (gate j))
    (ok : ∀ j, WorldGate (ρ j) (D j) (gate j)) :
    Effective ltr (fun j => XorWindow.duskCmd (gate j)) ∧ ∃ K, 0 < K ∧
      ∀ j, Within K (XorWindow.duskCmd (gate j)) ∧ Native (ρ j) (D j) (XorWindow.duskCmd (gate j)) := by
  obtain ⟨K,hK,w⟩ := XorWindow.duskCmd_within R
  exact ⟨XorWindow.duskCmd_effective effective,K,hK,fun j => ⟨w _ (regs j),nativeOfGate (le j) (ok j)⟩⟩

theorem nativeWidth : Staff.Realizes nativeRegime worldBits :=
  (Staff.Realizes.fix 3).times PhysicalWalshCompileInteriorHeader.nativeL

/-- The forest builder has a fixed degree for the two-width universal
descriptor, so effective opcode reserve degrees remain effective. -/
noncomputable def forestReserve := XorWindow.forestDegree nativeRegime worldBits nativeWidth

/-- A variable-rate family of native opcode implementations extends through
both the instruction forest and the Dusk codecs to complete physical gates. -/
theorem nativeStageFamily {J : Type} [Primcodable J] {ρ : J → ℝ} {D : J → ℕ} (le : ∀ j, ρ j ≤ 1)
    {c : J → Cmd} (effective : Effective ltr c) (degree : Computable D)
    (R : ℕ) (regs : ∀ j, Within R (c j))
    (ok : ∀ j, XorWindow.StagesAt nativeRegime worldPrefix worldBits worldRow (ρ j) (D j) (c j)) :
    let cmd j := XorWindow.duskCmd (XorWindow.gateCmd nativeRegime worldBits nativeWidth (c j))
    let depth j := max (D j) forestReserve
    Effective ltr cmd ∧ Computable depth ∧ ∃ K, 0 < K ∧
      ∀ j, Within K (cmd j) ∧ Native (ρ j) (depth j) (cmd j) := by
  obtain ⟨S,_,hS⟩ := XorWindow.gateCmd_within nativeRegime worldBits nativeWidth R
  obtain ⟨eff,K,hK,run⟩ := nativeFamily le
    (XorWindow.gateCmd_effective nativeRegime worldBits nativeWidth effective) S
    (fun j => hS _ (regs j)) (fun j => XorWindow.boundedGateOnNamed worldPrefix worldBits nativeWidth worldRow (ok j))
  exact ⟨eff,Primrec.nat_max.to_comp.comp degree (Computable.const forestReserve),K,hK,run⟩

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
