import OAI.Computability.VPVNP.RAMTapeSiteMachine
import OAI.Computability.VPVNP.RAMTapeLinkedClock
import OAI.Computability.VPVNP.RAMTapeInputOperandStartup

/-!
# A literal universal coefficient for the live RAM transcript

Given a fixed private instruction table and its finite list of public operand
formulas, compile the actual raw-input processor into a two-tape program.
At every sufficiently large fitted length, each site's coefficient is the
exact cardinal of its private incident paths. The program reads its own
literal prefix to obtain operands that refer to that prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts
set_option synthInstance.maxSize 10000

open BurstRAM PrivateRAM LiveProgram ProcessorInput RAMLayout Filter
variable {p r k : ℕ}

/-- Literal two-tape program combining the fixed private template with the startup that
evaluates its operands from the physical site and the program’s own prefix. -/
noncomputable def machine (T : Template p r k) (args : Fin k → InputOperand)
    (B a b u lit : ℕ) (hb : 0 < b) : UniversalMachine.Program :=
  table (InputOperandStartup.Expr args) T (InputOperandStartup.program r args B a b u lit hb)

theorem machine_count (T : Template p r k) (args : Fin k → InputOperand)
    (B a b u lit : ℕ) (hB : 1 ≤ B) (hb : 0 < b) (hab : a ≤ b) (hu : 1 ≤ u)
    (n : ℕ) (hn : 1 ≤ n) :
    let d := addressWidth B n
    let e := roundedUp a b n
    let w := CursorBounds.wordBits B n
    let g : Geometry := ⟨n,d,2^e,w⟩
    let D := machine T args B a b u lit hb
    ∀ (x : SiteCutBank.Input d e w), x.prog = D → x.n = n → x.u = u → x.lit = lit →
      ∀ (fit : Fits D n d (2^e) w), (UniversalMachine.programPrefix D).length ≤ w →
      (∀ i, (InputOperandStartup.Expr args i).Fits g (2^w)) →
      let ticks := linkedTicks r (InputOperandStartup.clockCoefficient args B a b u) x
      ticks*(6*(n+(Fintype.card (InputOperandStartup.Target r args)+1)+ticks)+4) ≤ n^clockExponent →
      acceptingCount (encode D n x.v x.hdr (RAMLayout.incidentBits x.sends x.v) fit) =
        x.pathCard T (fun i => Pieces.word g (CounterPublic.actualPrefix D) (args i)) := by
  intro d e w g D x hx hxn hxu hxl fit hprefix hg ticks hclock
  obtain ⟨t, ht, s, run, frame, blank⟩ := InputOperandStartup.frame_runs r args B a b u lit
    hB hb hab hu n hn x hxn hxu hxl (hx ▸ fit) (hx ▸ hprefix) hg
  rw [hx] at run frame
  have hbound : coreSteps r x + t ≤ ticks := by
    dsimp only [ticks, linkedTicks]
    rw [hxn, hxu, Nat.add_comm]
    exact Nat.add_le_add_right ht _
  have eqn := table_coefficient (InputOperandStartup.Expr args) T (InputOperandStartup.program r args B a b u lit hb)
    x (fun i => Pieces.word g (CounterPublic.actualPrefix D) (args i)) s t ticks
  rw [hxn] at eqn
  exact eqn fit run frame blank hbound hclock

/-- All group headers and compatible incident words at one live geometry. -/
def CountsAt (T : Template p r k) (args : Fin k → InputOperand)
    (D : UniversalMachine.Program) (n d e w lit : ℕ) (hw : 4 ≤ w) : Prop :=
  let g : Geometry := ⟨n,d,2^e,w⟩
  ∃ fit : Fits D n d (2^e) w,
    (∀ i, (InputOperandStartup.Expr args i).Fits g (2^w)) →
    ∀ (v : Word d) (hdr : Header) (sends : SendArrays d (2^e) w),
      ∃ hc : 2^d*2^e < 2^w,
        acceptingCount (encode D n v hdr (RAMLayout.incidentBits sends v) fit) =
          Nat.card ((T.instantiate w (fun i => Pieces.word g (CounterPublic.actualPrefix D) (args i))).IncidentPaths
            (n^10000) (Fin.ofNat (2^w) lit) (headerWord hw hdr) ((by decide : 2 ≤ 4).trans hw)
            hc v (RAMLayout.incidentBits sends v))

set_option exponentiation.threshold 10000 in
/-- At the live exponent the explicit physical clock and the literal-prefix
fit are simultaneous for every site, header and shared-bit assignment. -/
theorem eventually_machine_count (T : Template p r k) (args : Fin k → InputOperand)
    (B a b lit : ℕ) (hB : 1 ≤ B) (hb : 0 < b) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, CountsAt T args (machine T args B a b 10000 lit hb) n (addressWidth B n)
      (roundedUp a b n) (CursorBounds.wordBits B n) lit (ProcessorPublic.recordWidth_ge_four _) := by
  let D := machine T args B a b 10000 lit hb
  let coef := InputOperandStartup.clockCoefficient args B a b 10000
  let ports := Fintype.card (InputOperandStartup.Target r args)
  filter_upwards [eventually_live_clock D r coef ports B a b hB hab, eventually_ge_atTop 1] with n h hn
  obtain ⟨fit, hprefix, clock⟩ := h
  refine ⟨fit, fun hg v hdr sends => ?_⟩
  let x : SiteCutBank.Input (addressWidth B n) (roundedUp a b n) (CursorBounds.wordBits B n) :=
    ⟨D,n,10000,lit,v,hdr,sends,ProcessorPublic.capFits B a b n hB hb hab.le hn,
      ProcessorPublic.recordWidth_ge_four _,rfl⟩
  exact ⟨x.cap_lt, machine_count T args B a b 10000 lit hB hb hab.le (by decide)
    n hn x rfl rfl rfl rfl fit hprefix hg (clock x rfl rfl).2⟩

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
