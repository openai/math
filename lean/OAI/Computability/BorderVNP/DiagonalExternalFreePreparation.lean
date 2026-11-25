import OAI.Computability.BorderVNP.DiagonalExternalFreeReceived
import OAI.Computability.BorderVNP.PackedDirectoryProgram
import OAI.Computability.BorderVNP.PrivatePlacementImage
import OAI.Computability.BorderVNP.TransmissionRouteBank
import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute

/-! # Recovering the one substituted index across all native team routes

The first team supplies the substitution choices. Every other team's
returned setup clamps its whole second field. The protected input range
survives geometry, directory compilation, data and pair writers, and
the native scheduler before being sent to its final grouped locations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing TeamContraction RoutingISA RoutingISA.Transmission RoutingISA.Pins
open VPVNP.BurstRAM
open scoped Classical

variable {R r t pins link inner n w : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (ib hb sb : Fin (R+1) → ℕ)
local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)

/-- Every actual returning family of pin initializers has one common
substitution, read from the lead team's true private choices. -/
theorem returned_substitution (pub : Fin (R+1) → Arg → Word w)
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (m : Fin (R+1) → Memory w)
    (s : Fin (R+1) → Bank w)
    (frame : ∀ u, Pins.Frame (PL u) (readings (pub u)) (readings (m u)))
    (frameFit : ∀ u, (pub u 0).val+24 < 2^w)
    (strideFit : ∀ u, (PL u).stride < 2^w) (countFit : ∀ u, (PL u).count < 2^w)
    (indexFit : pins ≤ r*(G.program.length+t)) (fits : ∀ u, LoopFits w (PL u))
    (separated : ∀ u, Separated (PL u)) (z : ∀ u, Pins.Return (pub u) (mac u) (s u) (m u)) :
    ∃ bits : Fin pins → Bool, (z 0).val.1.flatMap TeamRAM.Event.choices = List.ofFn bits ∧
      ∀ u, SubstitutionAt (PL u) (extendGuess bits) (z u).val.2.2 := by
  choose chosen choices image using fun u => substitution_of_return (PL u) (pub u) (mac u) (m u)
    (s u) (frame u) (frameFit u) (Nat.succ_pos _) (strideFit u) (countFit u) indexFit
    (fits u) (separated u) (z u) (z u).val.2.2 (fun _ _ => rfl)
  refine ⟨chosen 0,choices 0,?_⟩
  intro u
  by_cases hu : u = 0
  · subst u
    exact image 0
  · intro x hx
    have ha : ¬ (PL u).active x := fun ha => hu (Fin.ext ha.1)
    simpa only [ite_eq_right ha] using image u x hx

/-- Compiling the seven-word delivery directory protects the frozen index
strictly above the frame count and below the first emitted raw row. -/
theorem substitution_directory {P : Pins.Layout} {guess : ℕ → Bool} {m : Memory w}
    (h : SubstitutionAt P guess m) (frame base : ℕ) (rows : List Packing.Directory.Row)
    (low : frame+9 < P.ibase) (high : P.ibase+P.count ≤ base) :
    SubstitutionAt P guess (Packing.Directory.ISA.publish m frame base rows) := by
  intro x hx
  have start : P.ibase+x < base := by omega
  rw [Packing.Directory.ISA.publish,Function.update_of_ne (by omega : P.ibase+x ≠ frame+9)]
  rw [Packing.Directory.ISA.putWords_outside _ _ _ _ (Or.inl start)]
  exact h x hx

/-- The physical geometry interpreter also leaves the entire frozen pin
array in place when its allocated scratch starts above the pin frame. -/
theorem substitution_geometry {P : Pins.Layout} {guess : ℕ → Bool} {m after : Memory w}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s final : Bank w}
    {fresh dest clock o : ℕ} {out : Fin o → ℕ} {trace : List (TeamRAM.Event w)}
    (h : SubstitutionAt P guess m)
    (run : PackedHistoryCircuit.GeometryReturn pub mac s m fresh dest clock out trace final after)
    (upper : P.ibase+P.count ≤ fresh) : SubstitutionAt P guess after := by
  intro x hx
  rw [run.preserved _ (by omega)]
  exact h x hx

/-- Rewriting the private original-site placement changes only the slot
columns and per-cell counters. Frozen pins below both arrays survive. -/
theorem substitution_privatePlacement {P : Pins.Layout} {guess : ℕ → Bool} {m after : Memory w}
    (h : SubstitutionAt P guess m) (l : PrivatePlacement.Layout) {j : ℕ}
    (image : l.Image (readings m) j (readings after))
    (raw : P.ibase+P.count ≤ l.raw) (scratch : P.ibase+P.count ≤ l.scratch) :
    SubstitutionAt P guess after := by
  intro x hx
  apply Fin.ext
  have keep := image.outside (P.ibase+x) (fun k _ => by omega) (Or.inl (by omega))
  exact keep.trans (congrArg Fin.val (h x hx))

variable {G ib hb sb}
    {inputPin : Fin pins → Bool} {ext : Exterior R r link → Bool} {wire : Routing.WireLayout (R+1) r link}
    {V g entries desc : ℕ} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w}
local notation "dir" => freeDirectory R r (G.program.length+t) link V g entries desc
local notation "Delivery" => ReturnedDelivery G inputPin ext wire dir pp lp owner origin stride H PL

/-- Actual shared-table emission and the scheduler image in the received
histories transport the frozen index to the memories used by the senders.
No byte equality at the receiving cell enters the numbered row formula. -/
theorem delivered_after_writers {I : Type*} (codec : PinCodec I pins) (delivery : Delivery)
    (hg : 0 < g) (room : r*(2*(G.program.length+t)+R*link) ≤ V*g)
    {bits : Fin pins → Bool} {i : I} (decoded : codec.decode bits = some i)
    (m : Fin (R+1) → Memory w) (sub : ∀ u, SubstitutionAt (PL u) (extendGuess bits) (m u))
    (emit : Fin (R+1) → DataWriter.Layout) (group : Fin (R+1) → Cube.SharedRows.Layout)
    (pub : Fin (R+1) → Arg → Word w)
    (shared : ∀ u, (group u).Emitted (readings (DataWriter.publish (emit u) (pub u) (m u))) (delivery.before u))
    (frame : ∀ u, (group u).frame = (pub u 0).val) (records : ∀ u, (group u).records = (emit u).output)
    (ordered : delivery.table.Ordered) (output : ∀ u, delivery.table.records = (emit u).output)
    (low : ∀ u, (pub u 0).val+13 < ib u) (high : ∀ u, ib u+(PL u).count ≤ (emit u).output)
    (z : FreePort R r (G.program.length+t)) :
    let a := freeLane hg room z
    receivedBank lp owner origin stride H a.1 a.2 = freeBits G (codec.encode i) z := by
  apply received_free_bank codec delivery hg room decoded _ z
  intro u
  exact (sub u).through_writers (emit u) (pub u) (shared u) (frame u) (records u)
    (delivery.image u) ordered (output u) (low u) (high u)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
