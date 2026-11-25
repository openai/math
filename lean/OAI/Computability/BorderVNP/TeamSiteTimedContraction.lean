import OAI.Computability.BorderVNP.TeamSiteTimedScalar
import OAI.Computability.BorderVNP.TeamSiteTimedRowLaw
import OAI.Computability.BorderVNP.TeamSiteTimedGeometry

/-! # The sewn physical signed contraction on trusted-clock RAM teams

The source timer is reset on every burst using the measured length of the whole
processor word. Consequently arbitrary malformed bursts are covered by the same
row dictionary as the intended generated packets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM UniversalMachine Filter TeamTapeHandoff TeamSiteEvents
open TeamContraction TeamContraction.ProcessorSlots TeamSiteConsistency TeamSiteTraversal
open scoped BigOperators Classical
variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) (mark : Fin routines → Γ)
local notation "physical" => machine P lib mark
local notation "body" => code P lib mark
local notation "input" => Layout.input (r:=reg) (k:=k) (d:=(m+1)*g)

/-- The physically accepted and unmasked checked timed rows coincide with the exact
native events, links and signs. The statement also counts valid zero-return paths. -/
theorem eventually_installed_rows (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : fitsWith physical reg k r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      ∀ (u : Fin (R+1)) pin ext (ibase hbase starbase : ℕ),
        let G := wiringWith physical P S d link n e fit
        let F := G.processorFields u pin ext ibase hbase starbase
        ∀ own : ∀ j, (F.row j).length ≤ 3*S.block.val,
          let M := geo.setup hr P (S.publicWords u) (fun j => (lib j).timedEval (mark j) (n^25))
            ⟨P.base.entry,S.registers u⟩ (n^25) F.row own
          ∀ links j f, Reads (Wires.edgeEquiv links).1 M.first j f → ∀ (bits : List Bool) (sg : Option Bool),
            let raw := List.ofFn (G.word pin ext links u j)
            let observed := ∃ es out, EndpointRow M.program M.pub M.lib M.block M.limit M.cap f es out ∧
              Writes (Wires.edgeEquiv links).1 j out ∧ sorted M.width M.sorter M.input links j f es ∧
              bits = chunkBits es ∧ chunkSign (some false) es = sg
            ((∃ t < n^36-TeamClocked.prepSteps 25 n, ∃ q bank, StackRuns (TeamPrivateFragment.replay body) t
                (.site Processor.start,bits) (TrustedClock.installed input raw) (q,[]) bank ∧ Row.Checked q sg) ↔ observed) ∧
              (∀ z, sg = some z → ((bits,z) ∈ installedLeaves P lib mark n raw ↔ observed)) :=
  eventually_installed_rows_of_models P lib mark (fun X => Row.models X distinct)

/-- Fixing the external links and summing the true internal bits of a team gives
the original bounded RAM computation on its actual initialized memory image. -/
theorem eventually_installed_value (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : fitsWith physical reg k r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      ∀ (u : Fin (R+1)) pin ext (ibase hbase starbase : ℕ),
        let G := wiringWith physical P S d link n e fit
        let F := G.processorFields u pin ext ibase hbase starbase
        ∀ own : ∀ j, (F.row j).length ≤ 3*S.block.val,
          let M := geo.setup hr P (S.publicWords u) (macros lib (n^25+1))
            ⟨P.base.entry,S.registers u⟩ (n^25) F.row own
          G.value pin ext u = nativeValue M.machine M.limit.val M.cap.val M.privateClock :=
  eventually_installed_value_of_models P lib mark distinct (fun X => Row.models X distinct)

/-- At the true universal clock the complete physical contraction is the exterior
sum of products of original RAM values. The common threshold is chosen before
all word geometries, public tables, free pin values and exterior inputs. -/
theorem eventually_installed_contraction (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : fitsWith physical reg k r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      ∀ (pin : Fin d → Bool) (ibase hbase starbase : Fin (R+1) → ℕ),
        let G := wiringWith physical P S d link n e fit
        let F := fun (ext : Exterior R r link → Bool) (u : Fin (R+1)) =>
          G.processorFields u pin ext (ibase u) (hbase u) (starbase u)
        ∀ own : ∀ ext u j, ((F ext u).row j).length ≤ 3*S.block.val,
          Diagonal.signedContraction G.slot pin = ∑ ext, ∏ u,
            let M := geo.setup hr P (S.publicWords u) (macros lib (n^25+1)) ⟨P.base.entry,S.registers u⟩
              (n^25) (F ext u).row (own ext u)
            nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  filter_upwards [eventually_installed_value P lib mark distinct] with n value
  intro R r w a d link e S fit hr geo hw hd hL hH pin ibase hbase starbase G F own
  rw [G.contraction_eq]
  apply Finset.sum_congr rfl
  intro ext _
  exact Finset.prod_congr rfl fun u _ =>
    value R r w a d link e S fit hr geo hw hd hL hH u pin ext (ibase u) (hbase u) (starbase u) (own ext u)

/-- The explicit sewn-tape specialization at the paper's paired row of positive
length. The true per-processor literal determines its global source address and
the private macro clock is measured from that entire word. -/
theorem eventually_sewn_contraction (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j) :
    ∀ᶠ t : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : fitsWith physical reg k r w a R link (t+1) e) (hr : 0 < r)
      (geo : Geometry r (t+1) pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ t+1 → 2+e+Nat.clog 2 r ≤ t+1 →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ t+1 → S.block.val ≤ t+1 →
      ∀ (pin : Fin d → Bool) (ibase hbase starbase : Fin (R+1) → ℕ),
        let G := Diagonal.CellEntries.SewnTape.wiring (R:=R) (r:=r) (regs:=reg) (w:=w) (ec:=e)
          (width:=w+1) (k:=t) (link:=link) physical fit
          (fun u j => entryTail (w+1) (t+1)
            (j.val*entryStride physical (w+1) (t+1) (prefixCapacity r k reg w (t+1)+1+a) R link)
            (2^e) (S.siteBits P (t+1) e u j)) d
        let F := fun (ext : Exterior R r link → Bool) (u : Fin (R+1)) =>
          G.processorFields u pin ext (ibase u) (hbase u) (starbase u)
        ∀ own : ∀ ext u j, ((F ext u).row j).length ≤ 3*S.block.val,
          Diagonal.signedContraction G.slot pin = ∑ ext, ∏ u,
            let M := geo.setup hr P (S.publicWords u) (macros lib ((t+1)^25+1)) ⟨P.base.entry,S.registers u⟩
              ((t+1)^25) (F ext u).row (own ext u)
            nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (eventually_installed_contraction P lib mark distinct)] with t ht
  exact ht

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
