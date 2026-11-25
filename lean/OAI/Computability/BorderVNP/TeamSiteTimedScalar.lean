import OAI.Computability.BorderVNP.TeamSiteTimedDictionary
import OAI.Computability.BorderVNP.TeamContractionGeneralLeaves
import OAI.Computability.BorderVNP.TeamSiteTimedNativeValue

/-! # Integer contraction of physical timed teams from their local row laws -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM UniversalMachine Filter TeamTapeHandoff
open TeamContraction TeamContraction.ProcessorSlots TeamSiteConsistency TeamSiteTraversal TeamSiteEvents
open scoped Classical BigOperators

variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) (mark : Fin routines → Γ)
local notation "physical" => machine P lib mark

/-- The concrete local coefficient expansion and link dictionary yield the original
bounded RAM's exact signed value. At no point must the original private table halt
on an arbitrary string. -/
theorem eventually_installed_value_of_models (hm : ∀ j, (lib j).alphabet.blank ≠ mark j)
    (models : ∀ {n d e w} (X : Row.Site P lib mark n d e w),
      Row.forward X (X.raw.length^25) ∧ Row.supplied X (X.raw.length^25)) :
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
          G.value pin ext u = nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  filter_upwards [eventually_installed_rows_of_models P lib mark models,eventually_wired_value P lib mark,
    eventually_ge_atTop 1] with n rows word positive
  intro R r w a d link e S fit hr geo hw hd hL hH u pin ext ibase hbase starbase G F own M
  let E := Wires.Edge r reg w e (w+1)
  let L := fun (int : E → Bool) (j : Fin r) => installedLeaves P lib mark n (List.ofFn (G.word pin ext int u j))
  let T := geo.setup hr P (S.publicWords u) (fun j => (lib j).timedEval (mark j) (n^25))
    ⟨P.base.entry,S.registers u⟩ (n^25) F.row own
  have dict : LeafDictionary T L := by
    intro int j f reads bs neg
    exact (rows R r w a d link e S fit hr geo hw hd hL hH u pin ext ibase hbase starbase own
      int j f reads bs (some neg)).2 neg rfl
  have hlib : T.lib = macros (fun j => TimedSupply.shadow (n^25) (lib j)) (n^25+1) :=
    (TimedSupply.macros_eq lib mark hm (n^25)).symm
  have budget : max 1 (n^25+1-1) ≤ T.privateClock := by
    change max 1 (n^25+1-1) ≤ n^25
    rw [Nat.add_sub_cancel]
    exact max_le (Nat.pow_pos positive) le_rfl
  have signed := nativeValue_of_leaf_dictionary T L (fun j => TimedSupply.shadow (n^25) (lib j)) (n^25+1) hlib budget dict
  have transfer := Macro.nativeValue_setup_timed T lib mark hm (n^25) rfl
  apply Eq.trans _ (signed.trans transfer)
  unfold Wiring.value
  apply Finset.sum_congr (by ext; simp)
  intro int _
  apply Finset.prod_congr rfl
  intro j _
  have val := word S fit u j pin ext int
  apply val.trans
  rw [TeamContraction.Replay.paths_eq_sum]
  change ∑ z ∈ L int j, TeamTape.haltWeight true z.2 = _
  exact (Finset.sum_attach (L int j) (fun z => TeamTape.haltWeight true z.2)).symm

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
