import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowData
import OAI.Computability.NearSquareRoot.CRTPositionRowCommandScan

/-! # Effective bounded iteration of a native address opcode on the spectator rows

The actual native command is the sole varying argument of the row interpreter.
The header/gather and collection commands are chosen on the joint input type.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Controlled Controlled.PositionProgram XorReserve NamedPacked
open CommonRegisters GeneratorSyntax Filter PositionRows

def opcodeCmd (pre post native : Cmd) : Cmd := (pre.join (RowCommandScan.scanCmd native)).join post

theorem opcodeCmd_effective (pre post : Cmd) {I : Type} [Primcodable I] {native : I → Cmd}
    (hn : Effective ltr native) : Effective ltr (fun i => opcodeCmd pre post (native i)) :=
  ((effective_const _ pre).join (RowCommandScan.effective hn)).join (effective_const _ post)

theorem opcodeCmd_within (pre post : Cmd) : ∀ᶠ R : ℕ in atTop, ∀ n, Within R n → Within R (opcodeCmd pre post n) := by
  filter_upwards [RegisterSelect.within_eventually pre,RegisterSelect.within_eventually post,RowCommandScan.within]
    with R hp hq hn
  exact fun n h => ⟨⟨hp,hn n h⟩,hq⟩

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P)
    {U : X → Type} (u : (x:X) → Series (U x)) (op : X → Op) (f : (x:X) → Input (P x) (k x) (U x))

/-- Preparation and collection specialize a joint world only after their
source files and metadata exponent have been fixed. -/
def RowEndsAt (pre post : Cmd) (e : ℕ) (g : (x:X) → Input (P x) (k x) (U x)) := ∀{Y:Type}
    (s : Y→X) (B m Q : Y→ℕ), (∀y, (u (s y)).count ≤ pack (B y) (m y)) →
    (∀y, r.scale (s y) ≤ Q y) → (∀y, 0 < m y) → (∀y, payloadBits e (Q y) ≤ B y) →
    let V y := volume (P (s y)) (k (s y)) (B y) (m y)
    EffectiveBoundedTask.Runs pre V V (fun y => .fork (r.header (s y)) (store (u (s y)) (f (s y))))
      (beforeRows r P k hP u f ∘ s) ∧
    EffectiveBoundedTask.Runs post V V (afterRows P k u g ∘ s) (fun y => store (u (s y)) (g (s y)))

/-- A named local program with an arbitrary address action and scan factor. -/
def LocalRowsAt (g : (x:X) → Input (P x) (k x) (U x)) (l : X → ℕ) (speed : X → ℝ) (native : Cmd) :=
  let rr := fixedRowRegime r P hP
  BreezeAt native (fun z : (x:X) × Block 2 (P x) => speed z.1) rr
    (fun z => (line 2 (k z.1)).count) (fun z => l z.1)
    (fun z => Tree.fork (rr.header z) (stripe (line 2 (k z.1)) (fun b => strip (u z.1) (f z.1 (prefixBit b) z.2))))
    (fun z => stripe (line 2 (k z.1)) (fun b => strip (u z.1) (g z.1 (prefixBit b) z.2)))

def WindowAt (g : (x:X) → Input (P x) (k x) (U x)) (l : X → ℕ) (speed : X → ℝ) (D : ℕ) (cmd : Cmd) := ∀{Y:Type}
    (s : Y→X) (B m Q factor : Y→ℕ), (∀y, l (s y) ≤ pack (B y) (m y)) →
    (∀y, r.scale (s y) ≤ Q y) → (∀y, 0 < m y) → (∀y, payloadBits D (Q y) ≤ B y) →
    (∀y, 2*speed (s y) ≤ factor y) → (∀y, factor y ≤ 2^P (s y)) →
    let V y := volume (P (s y)) (k (s y)) (B y) (m y)
    EffectiveBoundedTask.Runs cmd (fun y => V y*(factor y+1)) V
      (fun y => .fork (r.header (s y)) (store (u (s y)) (f (s y))))
      (fun y => store (u (s y)) (g (s y)))

/-- Use the same named native command on every full high-prefix row.
The fixed setup and collection programs also apply to arbitrary data actions. -/
theorem rowsOnNamedWith {pre post native : Cmd} {e : ℕ} (g : (x:X) → Input (P x) (k x) (U x))
    {l : X → ℕ} {speed : X → ℝ} (fits : ∀ x, (u x).count ≤ l x)
    (ends : RowEndsAt r P k hP u f pre post e g)
    (row : LocalRowsAt r P k hP u f g l speed native) :
    ∃ D, WindowAt r P k u f g l speed D (opcodeCmd pre post native) := by
  obtain ⟨hmode,d,work⟩ := row
  refine ⟨max d e,fun {Y} s B m Q factor lengths scale pos low rate high => ?_⟩
  intro V
  have room (j : ℕ) (hj : j ≤ max d e) y : payloadBits j (Q y) ≤ B y :=
    (Nat.mul_le_mul_right _ hj).trans (low y)
  obtain ⟨before,after⟩ := ends s B m Q (fun y => (fits (s y)).trans (lengths y)) scale pos (room e (le_max_right ..))
  let A y := Block 2 (P (s y))
  let cells y := line 2 (P (s y))
  let w y := rowWidth (k (s y)) (B y) (m y)
  let src y (a:A y) := Tree.fork ((fixedRowRegime r P hP).header ⟨s y,a⟩)
    (stripe (line 2 (k (s y))) fun z => strip (u (s y)) (f (s y) (prefixBit z) a))
  let dst y (a:A y) := stripe (line 2 (k (s y))) fun z =>
    strip (u (s y)) (g (s y) (prefixBit z) a)
  let atRow (z : Sigma A) : (x:X) × Block 2 (P x) := ⟨s z.1,z.2⟩
  have charge (z : Sigma A) :
      runrate (fun z : (x:X) × Block 2 (P x) => speed z.1)
        (fixedRowRegime r P hP) (fun z => (line 2 (k z.1)).count) (fun z => l z.1) d
        (atRow z) ≤ (w z.1 * factor z.1 : ℕ) := by
    let y := z.1
    have cap := polynomial_le_pack (scale y) (pos y) (room d (le_max_left ..) y)
    have span : l (s y) + (r.scale (s y)+1)^d ≤ 2*pack (B y) (m y) := by have := lengths y; omega
    have mode : 0 ≤ speed (s y) := zero_le_one.trans (hmode (atRow z))
    have le := mul_le_mul_of_nonneg_left (rate y) (show 0 ≤ (rowWidth (k (s y)) (B y) (m y):ℝ) by positivity)
    have left := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.mul_le_mul_left (2^k (s y)) span) :
        (((2^k (s y))*(l (s y)+(r.scale (s y)+1)^d):ℕ):ℝ) ≤
          ((2^k (s y)*(2*pack (B y) (m y)):ℕ):ℝ)) mode
    change ((line 2 (k (s y))).count:ℝ)*(l (s y)+(r.scale (s y)+1:ℝ)^d)*speed (s y) ≤ _
    rw [lineSize]
    dsimp only [w,y,rowWidth] at le ⊢
    push_cast at left le ⊢
    nlinarith only [left,le]
  have run := (work.on atRow).bounds (fun z => w z.1 * factor z.1) charge
  have localRun : EffectiveTask.Runs native (fun z : Sigma A => w z.1*factor z.1)
      (fun z => src z.1 z.2) (fun z => dst z.1 z.2) := run
  obtain ⟨J,heads⟩ := before.task.endpointSize
  obtain ⟨H,tails⟩ := after.task.endpointSize
  have positive y : 0 < V y := Nat.mul_pos (Nat.two_pow_pos _) (pos y)
  have cap (n v : ℕ) (hv : 0<v) : n*(v+1) ≤ (2*n)*v :=
    (Nat.mul_le_mul_left _ (by omega : v+1 ≤ 2*v)).trans_eq (by ring)
  have full := RowCommandScan.seriesRows native cells src dst w V factor localRun (2*(J+H)) (fun y =>
    ((le_max_right ..).trans (heads y)).trans ((cap J _ (positive y)).trans (Nat.mul_le_mul_right _ (by omega))))
    (fun y => ((le_max_left ..).trans (tails y)).trans ((cap H _ (positive y)).trans (Nat.mul_le_mul_right _ (by omega))))
    (fun y => by dsimp [cells,w,V]; rw [lineSize,rows_volume]) (fun y => by simpa only [cells,lineSize] using high y)
  let t y := V y*(factor y+1)
  have inc y : V y ≤ t y := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  exact ((before.mono inc (fun _ => le_rfl)).sequence full).sequence (after.mono inc (fun _ => le_rfl))


/-- Physical gate instruction on the original high-spectator/active-bit layout. -/
def OpcodeAt (ρ : ℝ) (D : ℕ) (cmd : Cmd) := ∀{Y:Type}
    (s : Y→X) (B m Q factor : Y→ℕ), (∀y, (u (s y)).count ≤ pack (B y) (m y)) →
    (∀y, r.scale (s y) ≤ Q y) → (∀y, 0 < m y) → (∀y, payloadBits D (Q y) ≤ B y) →
    (∀y, 2*Spindle.modes k (τ:=ρ) (s y) ≤ factor y) → (∀y, factor y ≤ 2^P (s y)) →
    let V y := volume (P (s y)) (k (s y)) (B y) (m y)
    EffectiveBoundedTask.Runs cmd (fun y => V y*(factor y+1)) V
      (fun y => .fork (r.header (s y)) (store (u (s y)) (f (s y))))
      (fun y => store (u (s y)) (rewired P k op f (s y)))

/-- Use the native command on each complete high-prefix row; its own real
time pays for the temporary workspace while the other rows stay parked. -/
theorem opcodeOnNamedWith {pre post native : Cmd} {ρ : ℝ} {e : ℕ}
    (ends : RowEndsAt r P k hP u f pre post e (rewired P k op f))
    (row : NativeRowAt r P k hP u native ρ op f) :
    ∃ D, OpcodeAt r P k u op f ρ D (opcodeCmd pre post native) := by
  apply rowsOnNamedWith r P k hP u f (rewired P k op f) (fun _ => le_rfl) ends
  obtain ⟨hr,d,exec⟩ := row
  refine ⟨hr,d,?_⟩
  convert exec using 1 <;> first | rfl | skip
  apply funext
  intro z
  change stripe _ (fun b => strip _ (rewired P k op f _ (prefixBit b) _)) = _
  simp only [cloth,stackRun,rewired,Function.comp_apply,nativeOp_bits]

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
