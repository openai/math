import OAI.Computability.BorderVNP.TeamContractionSignedSum
import OAI.Computability.BorderVNP.TeamContractionAllPaths
import OAI.Computability.BorderVNP.TransmissionSiteRowChecks
import OAI.Computability.BorderVNP.TeamSiteProcessorRowIff
import OAI.Computability.BorderVNP.TeamSiteProcessorRowClock
import OAI.Computability.BorderVNP.TeamSiteConsistencyScale

/-! # The signed RAM value in a physically installed team

The fixed site-program literal is interpreted on its actual input wires. At every
sufficiently large length all accepted physical leaves correspond to the genuine
signed bounded executions on the same initialized memory. The inclusive native
private transition cap uses one extra interpreter tick to observe its halt.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RAMTape UniversalMachine TeamSite TeamSite.Processor TeamSiteEvents
open TeamSiteConsistency TeamTapeHandoff TeamSiteTraversal Filter
open scoped BigOperators Classical

variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]

/-- The concrete raw wire words realize both finite physical row dictionaries.
They retain the true accepting signs and also detect a checked zero contribution. -/
theorem eventually_installed_rows (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : Fits P lib r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      (∀ j vs, vs.length ≤ S.burst.val → (lib j).bounded (n^25+1) (vs : List (Word w))) →
      ∀ (u : Fin (R+1)) pin ext (ibase hbase starbase : ℕ),
        let G := wiring P lib S d link n e fit
        let F := G.processorFields u pin ext ibase hbase starbase
        ∀ own : ∀ j, (F.row j).length ≤ 3*S.block.val,
          let M := geo.setup hr P (S.publicWords u) (macros lib (n^25+1)) ⟨P.base.entry,S.registers u⟩ (n^25) F.row own
          RowDictionary M G lib pin ext u ∧ CheckedDictionary M G lib pin u ext := by
  filter_upwards [Row.eventually_row_clock P lib] with n rowClock
  intro R r w a d link e S fit hr geo hw hd hL hH bounded u pin ext ibase hbase starbase G F own M
  let stride := entryStride (machine P lib) (w+1) n (prefixCapacity r k reg w n+1+a) R link
  have offset (j : Fin r) : j.val*stride = TeamTapeInputEmit.rowStart F.row j := by
    apply Eq.trans _ (processor_rowStart F j).symm
    apply congrArg (j.val * ·)
    let lit := entryLiteral (machine P lib) (w+1) n (prefixCapacity r k reg w n+1+a)
    change 2*lit + R*link = (lit + ((R+1)-1)*link)+lit
    rw [Nat.add_sub_cancel,Nat.two_mul]
    ac_rfl
  have lookup (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) (f : Frame w reg)
      (received : Reads (Wires.edgeEquiv int).1 M.first j f) :
      ∃ X : Row.Context P lib n (Nat.clog 2 r) e w, RowInstalled S u j int f (List.ofFn (G.word pin ext int u j))
        (F.row j) (j.val*stride) X := by
    have ingressEq := (ingress_eq_iff (S.start P u) f int j).mpr received
    have room := row_input_size F.row M.header j
    rw [← offset j] at room
    have space : 2*(F.row j).length+2*S.block.val ≤ 4*2^e := by
      have hh := own j
      have hs := geo.rowCapacity
      omega
    exact siteRowContext P lib S d link n e fit (by have := geo.width; omega)
      geo.localSort (by omega) hw hL geo.sorter geo.pcs u j pin ext int ibase hbase starbase f ingressEq room space
  have localRows (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) (f : Frame w reg)
      (received : Reads (Wires.edgeEquiv int).1 M.first j f) (bits : List Bool) (sg : Option Bool) :
      let observed := ∃ es out, EndpointRow M.program M.pub M.lib M.block M.limit M.cap f es out ∧
        Writes (Wires.edgeEquiv int).1 j out ∧ sorted M.width M.sorter M.input int j f es ∧
        bits = chunkBits es ∧ chunkSign (some false) es = sg
      (checkedSite M G lib pin u ext int j bits sg ↔ observed) ∧
      (∀ neg, sg = some neg →
        ((bits,neg) ∈ physicalLeaves G Layout.input (Processor.code P lib) Processor.negative Processor.start
          36 pin ext int u j ↔ observed)) := by
    intro observed
    obtain ⟨X,installed⟩ := lookup int j f received
    have raw : X.raw = G.input pin ext int u j := installed.rawEq.trans (G.read_bits pin ext (fun _ => int) u j)
    have bound (j : Fin routines) (vs : List (Word w)) (len : vs.length ≤ X.cap.val) :
        (lib j).bounded (n^25+1) vs := bounded j vs (installed.capEq ▸ len)
    have time := rowClock X (n^25+1) (F.row j).length (installed.blockEq ▸ hH) hd installed.dataWithin le_rfl installed.prefix_le
    have rhs : X.certified (n^25+1) bits sg ↔ observed := by
      unfold Row.Context.certified
      simp only [installed.pubEq,installed.blockEq,installed.limitEq,installed.capEq,installed.frameEq,
        installed.guard_iff,installed.sorted_iff F.row rfl (offset j)]
      rfl
    constructor
    · have law := X.checked_row_iff (n^25+1) (n^36) bound time bits sg
      unfold Row.Context.checkedRun at law
      rw [raw] at law
      exact law.trans rhs
    · rintro neg rfl
      have law := X.row_iff (n^25+1) (n^36) bound time bits neg
      rw [raw] at law
      exact law.trans rhs
  exact ⟨fun int j f received bits neg => (localRows int j f received bits (some neg)).2 neg rfl,
    fun int j f received bits sg => (localRows int j f received bits sg).1⟩

/-- The signed contraction on a physically installed team equals the sum of its genuine
native RAM executions on the initialized header, with the original inclusive private
transition cutoff. The common threshold precedes all choices of dimensions and fields. -/
theorem eventually_installed_value (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : Fits P lib r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      (∀ j vs, vs.length ≤ S.burst.val → (lib j).bounded (n^25+1) (vs : List (Word w))) →
      ∀ (u : Fin (R+1)) pin ext (ibase hbase starbase : ℕ),
        let G := wiring P lib S d link n e fit
        let F := G.processorFields u pin ext ibase hbase starbase
        ∀ own : ∀ j, (F.row j).length ≤ 3*S.block.val,
          let M := geo.setup hr P (S.publicWords u) (macros lib (n^25+1)) ⟨P.base.entry,S.registers u⟩ (n^25) F.row own
          G.value pin ext u = nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  filter_upwards [eventually_installed_rows P lib,eventually_value_of_rows P lib,eventually_ge_atTop 1]
    with n actual signed positive
  intro R r w a d link e S fit hr geo hw hd hL hH bounded u pin ext ibase hbase starbase G F own M
  have law := (actual R r w a d link e S fit hr geo hw hd hL hH bounded u pin ext ibase hbase starbase own).1
  apply signed R r _ d link _ e w M G rfl rfl pin ext u (n^25+1) rfl _ law
  change max 1 (n^25+1-1) ≤ n^25
  rw [Nat.add_sub_cancel]
  exact max_le (Nat.pow_pos positive) le_rfl

/-- Every exterior transmission is summed once, with independent native paths on each
team and true initialization of the corresponding local header. The equality concerns
the actual contraction on the installed universal processor input slots. -/
theorem eventually_installed_contraction (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : Fits P lib r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      (∀ j vs, vs.length ≤ S.burst.val → (lib j).bounded (n^25+1) (vs : List (Word w))) →
      ∀ (pin : Fin d → Bool) (ibase hbase starbase : Fin (R+1) → ℕ),
        let G := wiring P lib S d link n e fit
        let F := fun (ext : Exterior R r link → Bool) (u : Fin (R+1)) =>
          G.processorFields u pin ext (ibase u) (hbase u) (starbase u)
        ∀ own : ∀ ext u j, ((F ext u).row j).length ≤ 3*S.block.val,
          Diagonal.signedContraction G.slot pin = ∑ ext, ∏ u,
            let M := geo.setup hr P (S.publicWords u) (macros lib (n^25+1)) ⟨P.base.entry,S.registers u⟩
              (n^25) (F ext u).row (own ext u)
            nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  filter_upwards [eventually_installed_value P lib] with n value
  intro R r w a d link e S fit hr geo hw hd hL hH bounded pin ibase hbase starbase G F own
  rw [G.contraction_eq]
  apply Finset.sum_congr rfl
  intro ext _
  apply Finset.prod_congr rfl
  intro u _
  exact value R r w a d link e S fit hr geo hw hd hL hH bounded u pin ext (ibase u) (hbase u) (starbase u) (own ext u)

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
