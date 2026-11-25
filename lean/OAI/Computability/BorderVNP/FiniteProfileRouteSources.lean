import OAI.Computability.BorderVNP.FiniteProfileTeamFront
import OAI.Computability.BorderVNP.CubeRouteProfileInputs

/-! # Routing sources at the end of the finite processor's actual profile prefix

The copied positive header and the public geometry do not alter the original processor
inputs or broadcast fields. The finite pin initializer writes the prescribed substituted
bank. All 112 ordinary and extended frame fields are read back on this same return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction PackedHistoryCircuit
open private PinClear.read from OAI.Computability.BorderVNP.PackedHistoryPreparedInput

variable {R r lit link inner n w o nt ng : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
variable (G : Wiring R r lit 0 link inner n Edge) (u : Fin (R+1)) (ext : Exterior R r link → Bool)
variable (ib hb sb header dst : ℕ) (pub : Arg → Word w) (bank : Bank w)
variable (lib : Fin 8 → TeamSite.Macro Q Γ nt ng) (ret : FieldProcessor.Returns Q Γ K nt 8) (fuel : ℕ)
local notation "mac" => TeamSiteEvents.macros lib fuel
local notation "loc" => Wiring.pinLayout G u ib hb sb
local notation "f" => Wiring.transferFrame G u header dst
local notation "fields" => Wiring.processorFields G u (Fin.elim0 : Fin 0 → Bool) ext ib hb sb
local notation "guess" => Pins.extendGuess (noPin G u ib hb sb)

set_option maxRecDepth 4000 in
/-- Obtain the public input tape, actual substitution, broadcast pointer tuple and all
112 scalar fields from the real wide-copy execution and its returning geometry memory. -/
theorem FrontReceipt.route_sources {count pinClock fresh origin : ℕ} {extension : Fin 81 → Word w}
    {bits : List Bool} {words : Fin o → ℕ} {z : Returns profileFront pub mac bank (processorMemory fields w)}
    (receipt : FrontReceipt G u ext ib hb sb header dst pub bank lib ret fuel z count extension bits pinClock fresh origin words)
    (frameEnd : (pub 0).val+112 ≤ dst) (indexStart : dst ≤ ib) (liveStart : dst ≤ hb)
    (endBank : ib+(loc).count ≤ fresh) :
    ProfileRouteInputs fields f pub guess z.val.2.2 ∧
    (∀ i : Fin 31, z.val.2.2 ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
    (∀ i : Fin 81, z.val.2.2 ((pub 0).val+31+i.val) = extension i) := by
  obtain ⟨snap,hs,ready,saved,step,read,_,_,_,core,extended,_,low⟩ := receipt.source
  have binary := (G.broadcast_input u Fin.elim0 ext ib hb sb header dst snap.mem snap.input snap.fit).1
  have copy := ((readBroadcast_test f pub mac _ _ snap.frame snap.fit binary).sound read).2.2
  change readings saved = (f).copied (readings snap.mem) (f).header at copy
  have start : (fields).header.length ≤ (pub 0).val := by
    rw [Pins.ProcessorFields.header_length]
    have stride : (loc).stride = (f).stride := by
      dsimp [Pins.Layout.stride,Pins.Layout.offset,BroadcastFrame.stride,Wiring.pinLayout,Wiring.transferFrame]; omega
    rw [stride]; exact snap.fit.input
  have physical : (fields).ContainsInput saved := by
    intro i hi
    have before : i < (f).dst := by change i < dst; omega
    exact (Fin.ext ((congrFun copy i).trans ((f).copied_before _ _ i before))).trans (snap.input i hi)
  have frame : (f).At (readings pub) (readings saved) := copy.symm ▸ (f).copied_image snap.fit snap.frame _
  have separated : Pins.Separated loc := by
    constructor <;> intro x hx y hy <;> simp_all [Pins.Layout.active,Wiring.pinLayout]
  have inClear : PinClear loc 0 (fields).header.length := ⟨Or.inl (by change 0+_ ≤ ib; omega),Or.inl (by change 0+_ ≤ hb; omega)⟩
  have clear : PinClear loc (pub 0).val 112 := ⟨Or.inl (frameEnd.trans indexStart),Or.inl (frameEnd.trans liveStart)⟩
  have endAddr : (pub 0).val+112 ≤ fresh := frameEnd.trans (indexStart.trans ((Nat.le_add_right ..).trans endBank))
  have input := profileRouteInputs_of_prepared physical frame separated inClear clear
    (start.trans ((Nat.le_add_right ..).trans endAddr)) endAddr endBank low
  have keep (i : ℕ) (hi : i<112) : z.val.2.2 ((pub 0).val+i) = saved ((pub 0).val+i) :=
    (low _ ((Nat.add_lt_add_left hi _).trans_le endAddr)).trans (PinClear.read clear guess saved i hi)
  exact ⟨input,fun i => (keep i.val (by have := i.isLt; omega)).trans (core i),fun i => by
    simpa only [Nat.add_assoc] using (keep (31+i.val) (by have := i.isLt; omega)).trans
      (by simpa only [Nat.add_assoc] using extended i)⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
