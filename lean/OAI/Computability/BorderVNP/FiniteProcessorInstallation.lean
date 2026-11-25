import OAI.Computability.BorderVNP.FiniteProcessorTeamValue
import OAI.Computability.BorderVNP.TeamContractionInstalled

/-! # Field-valued team simulation on its genuine physical site geometry

The universal program in every site word is the actual field-instrumented
processor. Its raw prefix length also determines every literal, pin and memory
offset used by the concrete parser and handoff/sort network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP BurstRAM RAMTape TeamSite TeamSiteEvents TeamContraction TeamSiteConsistency
open TeamContraction.ProcessorSlots TeamSiteTraversal TeamTapeHandoff Filter
open scoped BigOperators Classical

variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q] {F : Type*} [Field F] [Fintype F]

set_option maxHeartbeats 1000000 in
/-- For every bounded native routine and valid physical dimensions, the actual
field team sum equals its adaptive finite-field RAM execution on the initialized
header. The native private bound is n²⁵ transitions plus one halt check. -/
theorem eventually_installed (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g)
    (weights : Returns Q Γ F m routines) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : fitsWith (machine P lib weights) reg k r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      (∀ j vs, vs.length ≤ S.burst.val → (lib j).bounded (n^25+1) (vs : List (Word w))) →
      ∀ (u : Fin (R+1)) pin ext (ibase hbase starbase : ℕ),
        let G := wiringWith (machine P lib weights) P S d link n e fit
        let fields := G.processorFields u pin ext ibase hbase starbase
        ∀ own : ∀ j, (fields.row j).length ≤ 3*S.block.val,
          let M := geo.setup hr P (S.publicWords u) (macros lib (n^25+1)) ⟨P.base.entry,S.registers u⟩ (n^25) fields.row own
          FieldTeam.fieldValue G F pin ext u = nativeSum M lib weights (n^25+1) ∧
          SpellingBijection M G lib pin ext u ∧ CheckedDictionary M G lib pin u ext ∧ RowValues M lib weights G pin ext u (n^25+1) := by
  filter_upwards [Processor.Row.eventually_row_clock P lib, eventually_witnesses P lib weights, eventually_ge_atTop 1] with n rowClock readout hn
  intro R r w a d link e S fit hr geo hw hd hL hH bounded u pin ext ibase hbase starbase G fields own M
  let physical := machine P lib weights
  let fuel := n^25+1
  let stride := entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link
  have offset (j : Fin r) : j.val*stride = TeamTapeInputEmit.rowStart fields.row j := by
    apply Eq.trans _ (processor_rowStart fields j).symm
    apply congrArg (j.val * ·)
    let lit := entryLiteral physical (w+1) n (prefixCapacity r k reg w n+1+a)
    change 2*lit+R*link = (lit+((R+1)-1)*link)+lit
    rw [Nat.add_sub_cancel,Nat.two_mul]
    ac_rfl
  have lookup (int : Wires.Edge r reg w e (w+1) → Bool) (j : Fin r) (f : Frame w reg)
      (received : Reads (Wires.edgeEquiv int).1 M.first j f) :
      ∃ X : Processor.Row.Context P lib n (Nat.clog 2 r) e w,
        RowInstalled S u j int f (List.ofFn (G.word pin ext int u j)) (fields.row j) (j.val*stride) X ∧
        X.raw = G.input pin ext int u j ∧
        X.coversClock fuel (n^36) (fun es => X.cost (Processor.Row.nativeCost w m g fuel es) es) := by
    have incoming := (ingress_eq_iff (S.start P u) f int j).mpr received
    have room := row_input_size fields.row M.header j
    rw [← offset j] at room
    have space : 2*(fields.row j).length+2*S.block.val ≤ 4*2^e := by
      have h := own j
      have r := geo.rowCapacity
      omega
    obtain ⟨X,hX⟩ := siteRowContextWith physical P lib S d link n e fit (by have := geo.width; omega)
      geo.localSort (by omega) hw hL geo.sorter geo.pcs u j pin ext int ibase hbase starbase f incoming room space
    exact ⟨X,hX,hX.rawEq.trans (G.read_bits pin ext (fun _ => int) u j),rowClock X fuel (fields.row j).length
      (hX.blockEq ▸ hH) hd hX.dataWithin le_rfl hX.prefix_le⟩
  have dict : RowDictionary M G lib pin ext u := by
    intro int j f recv bits neg
    obtain ⟨X,hX,raw,clock⟩ := lookup int j f recv
    have bound (j : Fin routines) (vs : List (Word w)) (len : vs.length ≤ X.cap.val) : (lib j).bounded fuel vs := bounded j vs (hX.capEq ▸ len)
    have row := X.row_iff fuel (n^36) bound clock bits neg
    rw [raw] at row
    refine row.trans ?_
    unfold Processor.Row.Context.certified
    simp only [hX.pubEq,hX.blockEq,hX.limitEq,hX.capEq,hX.frameEq,hX.guard_iff,hX.sorted_iff fields.row rfl (offset j)]
    rfl
  have checked : CheckedDictionary M G lib pin u ext := by
    intro int j f recv bits sg
    obtain ⟨X,hX,raw,clock⟩ := lookup int j f recv
    have bound (j : Fin routines) (vs : List (Word w)) (len : vs.length ≤ X.cap.val) : (lib j).bounded fuel vs := bounded j vs (hX.capEq ▸ len)
    have row := X.checked_row_iff fuel (n^36) bound clock bits sg
    unfold Processor.Row.Context.checkedRun at row
    rw [raw] at row
    refine row.trans ?_
    unfold Processor.Row.Context.certified
    simp only [hX.pubEq,hX.blockEq,hX.limitEq,hX.capEq,hX.frameEq,hX.guard_iff,hX.sorted_iff fields.row rfl (offset j)]
    rfl
  have values : RowValues M lib weights G pin ext u fuel := by
    intro int j f recv es out cert write sort nonzero
    obtain ⟨X,hX,raw,clock⟩ := lookup int j f recv
    have pm : M.program = P := rfl
    have pubM : M.pub = S.publicWords u := rfl
    have libM : M.lib = macros lib fuel := rfl
    have hb : M.block = S.block := rfl
    have hl : M.limit = S.limit := rfl
    have hcap : M.cap = S.burst := rfl
    rw [pm,pubM,libM,hb,hl,hcap] at cert
    rw [pm,pubM]
    have hc : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out := by
      simpa only [hX.pubEq,hX.blockEq,hX.limitEq,hX.capEq,hX.frameEq] using cert
    have run := row_leaf P lib weights X fuel (n^36) es out hc ((hX.guard_iff out).mpr write)
      ((hX.sorted_iff fields.row rfl (offset j) es).mpr sort) nonzero (clock es out hc)
    simpa only [raw,hX.pubEq,hX.frameEq] using run
  have limit : max 1 (fuel-1) ≤ M.privateClock := by
    change max 1 (n^25+1-1) ≤ n^25
    have := Nat.pow_pos (by omega : 0 < n) (n := 25)
    omega
  refine ⟨?_,dict.bijection fuel rfl limit,checked,values⟩
  have sum := witnesses_sum M lib weights G pin ext u fuel rfl limit dict values
  have hm : M.program = P := rfl
  rw [hm] at sum
  have evaluated := readout R r _ d link _ (Wires.Edge r reg w e (w+1)) G rfl pin ext u
  refine evaluated.trans (Eq.trans ?_ sum)
  apply Finset.sum_congr
  · ext s; simp only [Finset.mem_univ]
  · intro s _; rfl

/-- For every bounded native routine and valid physical dimensions, the actual
field team sum equals its adaptive finite-field RAM execution on the initialized
header. The native private bound is n²⁵ transitions plus one halt check. -/
theorem eventually_installed_value (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g)
    (weights : Returns Q Γ F m routines) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d link e : ℕ) (S : SiteData R r reg k w a)
      (fit : fitsWith (machine P lib weights) reg k r w a R link n e) (hr : 0 < r)
      (geo : Geometry r n pc w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ n → 2+e+Nat.clog 2 r ≤ n →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ n → S.block.val ≤ n →
      (∀ j vs, vs.length ≤ S.burst.val → (lib j).bounded (n^25+1) (vs : List (Word w))) →
      ∀ (u : Fin (R+1)) pin ext (ibase hbase starbase : ℕ),
        let G := wiringWith (machine P lib weights) P S d link n e fit
        let fields := G.processorFields u pin ext ibase hbase starbase
        ∀ own : ∀ j, (fields.row j).length ≤ 3*S.block.val,
          let M := geo.setup hr P (S.publicWords u) (macros lib (n^25+1)) ⟨P.base.entry,S.registers u⟩ (n^25) fields.row own
          FieldTeam.fieldValue G F pin ext u = nativeSum M lib weights (n^25+1) := by
  filter_upwards [eventually_installed P lib weights] with n h
  intro R r w a d link e S fit hr geo hw hd hL hH bounded u pin ext ib hb sb G fields own M
  exact (h R r w a d link e S fit hr geo hw hd hL hH bounded u pin ext ib hb sb own).1

end FieldProcessor

end BorderVNP
end Computability
end OAI
