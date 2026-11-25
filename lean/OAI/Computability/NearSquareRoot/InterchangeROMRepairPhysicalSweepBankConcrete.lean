import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankNative
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepConcrete

/-! # Compiled packed bank sweeps from the recursive interchange callback -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROM InterchangeROMAddress InterchangeAddress
  GeneratorSyntax InterchangeSpectralFibre
open Physical (Positions directions Allowance Bank sweep)

def command (a m l s b p half : ℕ) (inv : Bool) : Cmd :=
  compile a m l s inv (fun j => Sweep.nativeCommand b (a+m+a) j p half inv)

theorem command_within (a m l s b p half : ℕ) (inv : Bool) :
    Within (max 3 Sweep.nativeRegs) (command a m l s b p half inv) :=
  compile_within (le_max_left ..) a m l s inv _
    (fun j => RegisterSelect.within_mono (le_max_right ..) _ (Sweep.native_within b (a+m+a) j p half inv))

theorem effective_command {T : Type} [Primcodable T] {a m l s b p half : T → ℕ} {inv : T → Bool}
    (ha : Computable a) (hm : Computable m) (hl : Computable l) (hs : Computable s)
    (hb : Computable b) (hp : Computable p) (hh : Computable half) (hi : Computable inv) :
    Effective ltr (fun t => command (a t) (m t) (l t) (s t) (b t) (p t) (half t) (inv t)) :=
  effective_compile ha hm hl hs hi <| Sweep.effective_native (hb.comp Computable.fst)
    ((Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp ha hm) ha).comp Computable.fst)
    Computable.snd (hp.comp Computable.fst) (hh.comp Computable.fst) (hi.comp Computable.fst)

variable {P G S : Dims.Tape} {p a m l s b f w : ℕ} {D : Type}
local notation "X" => Positions P G S a m b f
local notation "R" => ZMod (p+1)
local notation "J" => Fin (a+m+a)
local notation "ord" => Equiv.refl J

abbrev layout (P G S : Dims.Tape) (a m b f : ℕ) :=
  layoutRows (b:=b) (Equiv.refl (Fin (a+m+a))) (fun _ : Unit => P) (fun _ => G) (fun _ => S)
    (fun _ => f) ()

abbrev request (w : ℕ) (pay : Series D) (j : J) (g : X → D → R) : Request b :=
  Sweep.request ord (fun _ : Unit => P) (fun _ => G) (fun _ => S) (fun _ => f) (fun _ => w)
    (fun _ => pay) j p (fun _ => g) ()

def rowCost (w half : ℕ) (inv : Bool) (pay : Series D) (child : Request b → Allowance) (j : J)
    (g : X → D → R) : Allowance :=
  Sweep.nativeCost ord (fun _ : Unit => P) (fun _ => G) (fun _ => S) (fun _ => f) (fun _ => w)
    (fun _ => pay) j p half inv (fun _ => g) () (child (request w pay j g))

/-- Execution on two packed check banks. The environment supplies precisely the ordinary
recursive job on the same field-width and payload-width descriptor. -/
theorem command_bounded [Fact (p+1).Prime] (hb : 2 ≤ b) (hp : solid P) (hg : solid G) (hs : solid S)
    (pay : Series D) (hw : pay.count ≤ w) (parent : Cmd) (env : Env)
    (child : Request b → Allowance)
    (hc : ∀ (j : J) (g : X → D → R), let q := request w pay j g
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) (child q))
    (half : ℕ) (inv : Bool) (x y : Bank R (Fin l) (X × D) (Fin s)) :
    let h := send (header f P G S)
    let rows := layout P G S a m b f
    Run (parent::env) (command a m l s b p half inv) (packet h (packed rows pay x ++ packed rows pay y))
      (packet h (packed rows pay (sweep (lift (directions inv (half:R))) x) ++
        packed rows pay (sweep (lift (directions inv (half:R))) y)))
      (fieldCost (banks l s) h (fun _ => Sweep.row rows pay) (fun j _ => update inv (half:R) j)
        (fun j _ => rowCost w half inv pay child j) (order a m inv) (streams x y)) := by
  apply native_bounded
  intro j g
  exact Sweep.native_bounded ord (fun _ : Unit => P) (fun _ => G) (fun _ => S) (fun _ => f)
    (fun _ => w) (fun _ => pay) j p half inv (fun _ => g) () parent env _ hb hp hg hs hw (hc j g)

end InterchangeROMRepair.SweepBank

end

end NearSquareRoot
end Computability
end OAI
