import OAI.Computability.BorderVNP.DiagonalIssuedPostCharges

/-! # The three measured families on the same issued route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube RoutingISA.Evaluator.ScheduleClock RoutingISA.SignedTaskArena

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)

variable {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
  {routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
    (Σ c : Physical.Broadcast axes groups cap,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code q,c,claim⟩) ≃
        Σ v : Route q,Report i q v}

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}
variable {task : SignedTaskArena.Layout} {A : StartupArena} {cost : PhaseCharges}
    {entryWords indexBits tallyDim subt P L₀ F H : ℕ}

attribute [local irreducible] PinStart.ChargedPost PinStart.ChargedVisit routedBareTuple

local notation3 (prettyPrint := false) "Issued" =>
  PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report

set_option cleanup.letToHave false

variable (B id cost routed)

/-- The real public boot, pin, profile and routing traces at every field
and team of one issued family. -/
def AllIssuedFront : Prop :=
  ∀ f : Issued, let z := routedBareTuple routed f
    let U := fun v => (B z.1 v).start
    ∀ u, let v := PinStart.visits id U (z.2 u)
      (B z.1 u).used + traceCost ((U u).pins (z.2 u).1).val.1 +
        traceCost v.profile.val.1 + traceCost v.routing.val.1 ≤ cost.core + cost.before

variable (task A entryWords indexBits tallyDim subt P L₀ F H)

/-- The per-team private and terminal receipts on the same full original
tuple recovered from its issued field. -/
def AllIssuedPost : Prop :=
  ∀ f : Issued, let z := routedBareTuple routed f
    let U := fun v => (B z.1 v).start
    ∀ u, PinStart.ChargedPost id U cost.argumentsCalls task A
      entryWords indexBits tallyDim subt P L₀ F H z.2 u

/-- Every issued field carries the combined physical charge at each team
of its recovered start and original register bank. -/
def AllIssuedChargedVisits : Prop :=
  ∀ f : Issued, let z := routedBareTuple routed f
    ∀ u, PinStart.ChargedVisit id (fun v => (B z.1 v).start) (fun v => (B z.1 v).used)
      cost task A entryWords indexBits tallyDim subt P L₀ F H z.2 u

variable {B id cost routed task A entryWords indexBits tallyDim subt P L₀ F H}

set_option maxHeartbeats 1400000 in
/-- Join the two charged families at the original routed fields, preserving
the entire phase clock and physical boot and reader inputs. -/
theorem AllIssuedPost.withFront
    (post : AllIssuedPost (B:=B) (id:=id) (routed:=routed) (cost:=cost) (task:=task) (A:=A)
      (entryWords:=entryWords) (indexBits:=indexBits) (tallyDim:=tallyDim) (subt:=subt)
      (P:=P) (L₀:=L₀) (F:=F) (H:=H))
    (front : AllIssuedFront (B:=B) (id:=id) (routed:=routed) (cost:=cost)) :
    AllIssuedChargedVisits (B:=B) (id:=id) (routed:=routed) (cost:=cost) (task:=task) (A:=A)
      (entryWords:=entryWords) (indexBits:=indexBits) (tallyDim:=tallyDim) (subt:=subt)
      (P:=P) (L₀:=L₀) (F:=F) (H:=H) := by
  unfold AllIssuedFront at front
  unfold AllIssuedPost at post
  unfold AllIssuedChargedVisits
  exact routedBareTuple.chargedVisitsOfPost (B:=B) (id:=id) (cost:=cost) (routed:=routed) front post

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
