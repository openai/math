import OAI.Computability.BorderVNP.TeamSiteTimedRowBudget
import OAI.Computability.BorderVNP.TeamSiteTimedCoefficient
import OAI.Computability.BorderVNP.TeamContractionInstalled

/-! # Installing the timed row dictionary on the sewn physical words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM UniversalMachine Filter TeamTapeHandoff
open TeamContraction TeamContraction.ProcessorSlots TeamSiteConsistency TeamSiteTraversal
open scoped Classical

variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) (mark : Fin routines → Γ)
local notation "body" => code P lib mark
local notation "input" => Layout.input (r:=reg) (k:=k) (d:=(m+1)*g)

/-- The actual signed leaf set after the independent trusted startup has been
charged against the fixed source site clock. -/
noncomputable def installedLeaves (n : ℕ) (raw : List Bool) :=
  TeamContraction.Replay.leaves body (negative P) (n^36-TeamClocked.prepSteps 25 n)
    (.site Processor.start) (TrustedClock.installed input raw)

omit [Fintype Q] in
/-- A true processor row for any fixed interpreter on the RAM site geometry.
Its time-zero record base is the chronological address in the flattened input. -/
theorem installedContext (physical : UniversalMachine.Program) {R r w a d link e n : ℕ}
    (S : SiteData R r reg k w a) (fit : fitsWith physical reg k r w a R link n e) (hr : 0 < r)
    (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e) (hw : w+1 ≤ n)
    (hd : 2+e+Nat.clog 2 r ≤ n) (hL : TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n)
    (u : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (links : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) (f : Frame w reg) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    ∀ own : ∀ j, (F.row j).length ≤ 3*S.block.val,
      let M := geo.setup hr P (S.publicWords u) (fun j => (lib j).timedEval (mark j) (n^25))
        ⟨P.base.entry,S.registers u⟩ (n^25) F.row own
      Reads (Wires.edgeEquiv links).1 M.first j f →
      ∃ X : Row.Site P lib mark n (Nat.clog 2 r) e w,
        RowInstalled S u j links f (List.ofFn (G.word pin ext links u j)) (F.row j)
          (TeamTapeInputEmit.rowStart F.row j) X := by
  intro G F own M received
  let stride := entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link
  have offset (j : Fin r) : j.val*stride = TeamTapeInputEmit.rowStart F.row j := by
    apply Eq.trans _ (processor_rowStart F j).symm
    apply congrArg (j.val * ·)
    let lit := entryLiteral physical (w+1) n (prefixCapacity r k reg w n+1+a)
    change 2*lit + R*link = (lit + ((R+1)-1)*link)+lit
    rw [Nat.add_sub_cancel,Nat.two_mul]; ac_rfl
  have ingressEq := (ingress_eq_iff (S.start P u) f links j).mpr received
  have room := row_input_size F.row M.header j
  rw [← offset j] at room
  have space : 2*(F.row j).length+2*S.block.val ≤ 4*2^e := by
    have := own j; have := geo.rowCapacity; omega
  obtain ⟨X,installed⟩ := siteRowContextWith physical P (fun j => extend (lib j) (mark j)) S d link n e fit
    (by have := geo.width; omega) geo.localSort (by omega) hw hL geo.sorter geo.pcs u j pin ext links
    ibase hbase starbase f ingressEq room space
  exact ⟨X,offset j ▸ installed⟩

/-- Installing the two complete physical row models supplies the timed local
dictionary on the same true wiring used by the integer contraction. -/
theorem eventually_installed_rows_of_models
    (allModels : ∀ {n d e w} (X : Row.Site P lib mark n d e w),
      Row.forward X (X.raw.length^25) ∧ Row.supplied X (X.raw.length^25))
    (physical : UniversalMachine.Program := machine P lib mark) :
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
              (∀ z, sg = some z → ((bits,z) ∈ installedLeaves P lib mark n raw ↔ observed)) := by
  filter_upwards [Row.eventually_budget P lib mark] with n costs
  intro R r w a d link e S fit hr geo hw hd hL hH u pin ext ibase hbase starbase G F own M links j f received bits sg raw observed
  obtain ⟨X,installed⟩ := installedContext P lib mark physical S fit hr geo hw hd hL u pin ext
    ibase hbase starbase links j f own received
  have len : X.raw.length = n := installed.rawEq ▸ List.length_ofFn
  obtain ⟨emit,coverage⟩ := allModels X
  rw [len] at emit coverage
  have clock := costs X (F.row j).length (installed.blockEq ▸ hH) hd installed.dataWithin installed.prefix_le
  have rhs : Row.certified X (n^25) bits sg ↔ observed := by
    unfold Row.certified Row.Endpoint
    simp only [installed.pubEq,installed.blockEq,installed.limitEq,installed.capEq,installed.frameEq,
      installed.guard_iff,installed.sorted_iff F.row rfl rfl]
    rfl
  constructor
  · have h := Row.checked_iff X emit coverage clock bits sg
    unfold Row.checkedRun at h
    rw [installed.rawEq] at h
    exact h.trans rhs
  · rintro z rfl
    have h := Row.leaf_iff X emit coverage clock bits z
    rw [installed.rawEq] at h
    exact h.trans rhs

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
