import OAI.Hierarchy.TaggedWideCalendarAssemblyCore

namespace OAI
/-! # Actual rejection flags annihilate the assembled terminal tensor -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open TaggedShorterBudget ProtocolStackContraction WideStack WideCalendarSites WideControlJoin
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type*} [Field F] {X : Type} {z d k w R M den L : ℕ}
    {slots : Event→Slot X} {es : List Event} {state : Equiv.Perm (Row z)→X}
    (Z : CalendarTerms F z d k w R M den slots es state)
    {H Q : Type} [Fintype H] [Fintype Q] (key : Fin L ↪ ℕ×ℕ)
    (cap : Q→ℕ) (historyCap : H→ℕ) (groups ports lanes dates view : ℕ)
local notation "D" => CalendarTerms.Shared key cap historyCap groups ports lanes dates view w
local notation "rout" => Z.nativeRouting D
local notation "E₀" => OpenPins z w (rout).catalyst
local notation "sels" => Fin (rout).selectors
private abbrev assemblyInput := (E₀ ⊕ sels) ⊕ Bool
private abbrev assemblyPins (paid : Gate) := SitePins E₀ sels D paid

variable (A B : Gate)
    (prefixPins : A.Head → assemblyInput Z key cap historyCap groups ports lanes dates view)
    (paidPins : B.Head → assemblyInput Z key cap historyCap groups ports lanes dates view)
    (flag : Fin A.u)
    (keep pad privateGate plane timeline :
      Net F (assemblyPins Z key cap historyCap groups ports lanes dates view B))
    (start finish : Fin (siteLast z d k+1) →
      Net F (assemblyPins Z key cap historyCap groups ports lanes dates view B))
    (row : Fin (siteLast z d k+1) → Fin es.length →
      Net F (assemblyPins Z key cap historyCap groups ports lanes dates view B))
local notation "fr" => Z.frame key cap historyCap groups ports lanes dates view A B prefixPins paidPins
    flag keep pad privateGate plane timeline start finish row
variable (cut : Fin L → CutFormat F (assemblyPins Z key cap historyCap groups ports lanes dates view B))
    (saturated : Fin L→ℕ)

local notation "c" => Z.assembled key cap historyCap groups ports lanes dates view A B prefixPins paidPins
    flag keep pad privateGate plane timeline start finish row cut saturated

/-- Geometry and cut pricing are used only on retained histories. On a rejection,
every summand contains the observed zero gate as its first local factor. -/
def assembled_run_kept (m n : ℕ) (hw : 0<w)
    («prefix» : (E₀→Bool)→(sels→Bool)→ℕ→Word A.W)
    (paid : (E₀→Bool)→(sels→Bool)→ℕ→Word B.W)
    (prefixRead : ∀e s,headerRead prefixPins e s=A.headBits («prefix» e s))
    (paidRead : ∀e s,headerRead paidPins e s=B.headBits (paid e s))
    (adm : (E₀→Bool)→(sels→Bool)→Prop)
    (accept : ∀e s,authentic (parentTag rout) e s→A.observed («prefix» e s) (A.zeroFlag flag)=
      if adm e s then (1:F) else 0)
    (language : ∀e s,authentic (parentTag rout) e s→∀p : Equiv.Perm (Row z),
      (p : Row z→Row z)=Tagged.tag (fun i=>e (.inl i))→(adm e s ↔ ∃!i : Fin ((rout).count p),(rout).encoding p i=s))
    (out : (E₀→Bool)→(sels→Bool)→Memory B.W)
    (run : ∀e s,authentic (parentTag rout) e s→adm e s→B.Ran (paid e s) (out e s))
    (room : B.W+1≤4*B.m)
    (localRead : ∀e s p i,reads (rout).encoding e s ⟨p,i⟩ → ((rout).links ⟨p,i⟩).Keep (2^z) →
      Z.Receipt key B cut keep pad privateGate plane timeline start finish row p i e s
        (B.terminal (out e s)) groups ports lanes view m n)
    (flagZero : ∀e s p i,reads (rout).encoding e s ⟨p,i⟩ →
      ¬((rout).links ⟨p,i⟩).Keep (2^z) → ∀a : D→Bool,
        TypedWiring.value keep (Sum.elim e (Sum.elim s (Sum.elim a (B.terminal (out e s)))))=0) :
    (c).Run where
  prefixHeader := «prefix»
  paidHeader := paid
  prefixRead := prefixRead
  paidRead := paidRead
  admitted := adm
  accept := accept
  tape e s ok := Z.tape_iff key cap historyCap groups ports lanes dates view e s ok (adm e s) (language e s ok)
  out := out
  ran := run
  room := room
  terminal e s j matched := by
    obtain ⟨p,i⟩ := j
    by_cases retained : ((rout).links ⟨p,i⟩).Keep (2^z)
    · exact Receipt.terminal Z key B cut keep pad privateGate plane timeline start finish row p i e s
        (B.terminal (out e s)) (localRead e s p i matched retained) hw
    · let seen:=B.terminal (out e s)
      change (∑ a : D→Bool,(∏t,(cut t).closed (Sum.elim e (Sum.elim s (Sum.elim a seen))))*
        localSite B (reportedSite keep pad privateGate plane timeline (network start finish row)) e s a seen)=
        (if ((rout).links ⟨p,i⟩).Keep (2^z) then (rout).route ⟨p,i⟩ e else 0)
      rw [ite_eq_right retained]
      apply Finset.sum_eq_zero
      intro a _
      unfold localSite reportedSite
      rw [attach_value,flagZero e s p i matched retained a,zero_mul,mul_zero]

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
end

end OAI
