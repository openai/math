import OAI.Computability.NearSquareRoot.InterchangeROMBinaryBudget
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryFamily
import OAI.Computability.NearSquareRoot.InterchangeROMRecursionThick
import OAI.Computability.NearSquareRoot.InterchangePackedRequest
import OAI.Computability.NearSquareRoot.InterchangeROMTableArithmetic

/-! # Native thick requests in a selected family of binary rectangle programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Selected

open IntegerMultiplication Code Strip
open InterchangeAddress Request PhysicalWalsh CommonRegisters GeneratorSyntax

/-- Native certificate on every packed request with the common thickness
degree. The alphabet characteristic and the native radix can vary separately. -/
def Native (b p k : ℕ) (ρ : ℝ) (c : Cmd) :=
  InterchangeROMRecursion.Certified c
    (fun x : ThickRequest (b:=b) (Packed (fun z : ZMod p => InterchangeROMTable.numeral z.val)) k =>
      ⌈(x.val.recordVolume:ℝ)*(x.val.width:ℝ)^ρ⌉₊)
    (fun x => x.val.recordVolume) (fun x => (job b).issue x.val) (fun x => (job b).reply x.val)

noncomputable abbrev adapterMass (t : ℕ) (x : Ticket) := ⌈mass Ticket.regime Ticket.total (fun y => y.w) t x⌉₊

private theorem relax {I : Type} {time space T S : I → ℕ} {u v : I → Tree} {c : Cmd}
    (h : ClosedRuns c time space u v) (K : ℕ)
    (ht : ∀ i, time i ≤ K*T i) (hs : ∀ i, space i ≤ K*S i) : ClosedRuns c T S u v := by
  apply EffectiveBoundedTask.Runs.bound h (K+1) (K+1) <;>
    intro i <;> rw [Nat.succ_mul,Nat.mul_succ] <;> have := ht i <;> have := hs i <;> omega

/-- Attach a computed radix, pad, invoke the named native command and crop.
The exponent of the header allocation is common to the entire command family. -/
theorem compile {J : Type} [Primcodable J] (k : ℕ)
    (req : (x : Ticket) → Request x.b)
    (valid : ∀ p, 2 ≤ p → ∀ x : Ticket, Packed (fun z : ZMod p => InterchangeROMTable.numeral z.val) (req x) ∧ Thick k (req x))
    (volume : ∀ x, (req x).recordVolume = x.total*(Ticket.pad k x + x.w+1))
    (width : ∀ x, (req x).width = x.e)
    (t : ℕ) (pre post : Cmd)
    (decode : ClosedRuns pre (adapterMass t) (adapterMass t)
      (fun x => .fork (send x.compact) (stripe x.rows (send ∘ x.bits)))
      (fun x => .fork (send x.compact) ((job x.b).issue (req x))))
    (encode : ClosedRuns post (adapterMass t) (adapterMass t)
      (fun x => .fork (send x.compact) ((job x.b).reply (req x))) (fun x => x.toPacket.output))
    (b p : J → ℕ) (hb : Computable b) (large : ∀ j, Net.Shuttle.base ≤ b j) (primeSize : ∀ j, 2 ≤ p j)
    (ρ : J → ℝ) (rate : ∀ j, 0 ≤ ρ j) (c : J → Cmd) (eff : Effective ltr c)
    (R : ℕ) (reg : ∀ j, Within R (c j)) (native : ∀ j, Native (b j) (p j) k (ρ j) (c j)) :
    ∃ (D H : ℕ) (cmd : J → Cmd), Effective ltr cmd ∧
      ∀ j, Within H (cmd j) ∧ RectPhysical (cmd j) (ρ j) D := by
  let D := max t k
  let x (j : J) (a : Packet) : Ticket := ⟨a,b j,large j⟩
  let count (j : J) := Ticket.coefficient (b j) D
  let S := Packet.mass D
  let T (j : J) (a : Packet) := time (ρ j) (S a) a.n
  let save (j : J) (a : Packet) := send (x j a).compact
  let issue (j : J) (a : Packet) := (job (b j)).issue (req (x j a))
  let reply (j : J) (a : Packet) := (job (b j)).reply (req (x j a))
  have adapt (j : J) (a : Packet) : adapterMass t (x j a) ≤ count j*S a :=
    Ticket.adapter_budget t D (le_max_left ..) _
  have st (j : J) (a : Packet) : S a ≤ T j a := Ticket.mass_le_time D _ (rate j) (x j a)
  have grow (j : J) (a : Packet) : adapterMass t (x j a) ≤ count j*T j a :=
    (adapt j a).trans (Nat.mul_le_mul_left _ (st j a))
  have core (j : J) : ClosedRuns (c j) (T j) S (issue j) (reply j) := by
    let q (a : Packet) : ThickRequest (b:=b j)
        (Packed (fun z : ZMod (p j) => InterchangeROMTable.numeral z.val)) k :=
      ⟨req (x j a),valid _ (primeSize j) _⟩
    apply relax ((native j).on q) (count j)
    · intro a
      change ⌈((req (x j a)).recordVolume:ℝ)*((req (x j a)).width:ℝ)^(ρ j)⌉₊ ≤ _
      rw [volume,width]
      exact Ticket.native_time k D (le_max_right ..) _ (rate j) _
    · intro a
      change (req (x j a)).recordVolume ≤ _
      rw [volume]
      exact Ticket.native_budget k D (le_max_right ..) _
  obtain ⟨H,hc,good⟩ := Family.compile b hb c eff R reg pre post ρ (fun _ => D) rate save issue reply
    (fun j => relax (decode.on (x j)) (count j) (grow j) (adapt j)) core
    (fun j => relax (encode.on (x j)) (count j) (grow j) (adapt j))
  exact ⟨D,H,_,hc,good⟩

end InterchangeROMBinary.Selected

end NearSquareRoot
end Computability
end OAI
