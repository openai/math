import OAI.Computability.BorderVNP.ShortenEnrichedSiteExecution

/-!
# Uniform calibrated geometry on the complete public state

One fixed site schedule works on any public representation of the actual
input and successor networks. The inequalities and final tensor sum use
the same histogram as the representation's program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Epoch.Round Cover Cover.Frame Shortening Packing Catalog Adaptive Filter
open scoped Classical Topology BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u v

variable {D m : ℕ} [NeZero D] {K : Type v} [Field K]

set_option maxHeartbeats 1600000 in
/-- One calibrated schedule for every admissible enriched-state program,
at every deep enough level, with its actual public terminal motions. -/
theorem exists_enriched_executions (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ S : SiteSchedule e, ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{u,v} d := by
  let I := Cube D
  obtain ⟨C,hC,setup⟩ := terminal_catalog_minimum
  obtain ⟨L,hL,hgen,final⟩ := setup I (1/4) (by norm_num)
  let A : ℝ := Fintype.card I*C
  obtain ⟨ν,hν,H,hH,cal⟩ := site_calibration (I := I) e hm
  obtain ⟨b,hb,coeff⟩ := cal L A hL.le (mul_nonneg (Nat.cast_nonneg _) hC)
  obtain ⟨h,hh,hs,prepare⟩ := exists_source_path e hm hH hν
  obtain ⟨source,hinit⟩ := prepare b (SiteRoutes.startingSites I L h)
  let path := source.asPath
  obtain ⟨V,hV,segment⟩ := finite_segments (path.catalog b).finite_toSet (2*h)
  obtain ⟨a,t,cap,Cout,u,clears,hout,ht,finish⟩ := final V hV
  obtain ⟨weight,hw,E,hE,k0⟩ := coeff hh (fun i => (source.pattern i).bins.Bin)
    (fun i => (source.pattern i).mean) (fun i => ((source.pattern i).motion : ℝ)) Cout
    (fun i => (source.pattern i).mean_nonneg) (fun i => Nat.cast_nonneg _) hout
  obtain ⟨k,⟨hk,round⟩,hk2⟩ := (k0.and (eventually_ge_atTop 2)).exists
  obtain ⟨startFloor,leaves⟩ := path.initial_leaves (L := L) hh
  let floor := max startFloor (∑ i, (source.pattern i).floor)
  let S : SiteSchedule e := ⟨L,hL,hgen,h,hh,hs,H,ν,b,hb,k,hk2,source,hinit,a,t,u,clears,ht,cap,A,Cout,
    floor,weight,hw,E,hE⟩
  refine ⟨S,?_⟩
  intro d hd
  let high := S.high d
  have hhigh : path.threshold a 1 ≤ high := by
    change S.drop + (1 + ∑ i, (source.pattern i).floor) ≤ d+1+S.drop
    have hf : (∑ i, (source.pattern i).floor) ≤ d := (le_max_right ..).trans hd
    omega
  obtain ⟨hstart,_,floors,vol⟩ := path.levels_at_start a high 1 hhigh
  refine ⟨⟨hstart,floors⟩,?_,?_⟩
  · intro P bits input route
    exact leaves (k := k) (bits := bits) weight a high hstart
      (by change startFloor ≤ d+1+S.drop+1; have := (le_max_left startFloor _).trans hd; omega)
      hinit input route
  · intro P fp bits states view F valid measured names flat initial σ hmin
    have canon (i : F.Hist flat) : (F.terminal flat i).canonical :=
      F.terminal_canonical hb (F.saved_canonical (fun j c q => ⟨names.capacity j c q,names.number j c q⟩)
        names.stored) flat i
    have fits (i : F.Hist flat) : FitsCatalog (F.terminal flat i) V (1/4) := by
      let state := (F.system.layer b).state ((F.system.histories b le_rfl (leavesEquiv k (states 0) b flat)).term i)
      change FitsCatalog (view b state) V (1/4)
      intro c
      obtain ⟨act,distinct⟩ := ((view b state).active_iff c.val).mp c.property
      have short := (valid state).short _ act
      exact ⟨short.trans (by change 2*h ≤ 1/4; linarith),
        segment _ _ _ ((valid state).sites _) ((valid state).sites _) distinct short⟩
    have finalData (i : F.Hist flat) :=
      finish (S.finish_level d) (F.terminal flat i) (canon i) (fits i) (σ i) (hmin i)
    choose out origins charges first using finalData
    let depth := path.depth a high
    have maxTile (i : Fin b) : (Fintype.card (I → Deck (depth (i.val+1)+1)) : ℝ) ≤ Fintype.card (I → Deck (high+1)) := by
      exact_mod_cast vol (i.val+1)
    obtain ⟨bound,tensor⟩ := round depth view F (Fintype.card (I → Deck (high+1))) (Nat.cast_nonneg _)
      maxTile measured flat initial out
    exact ⟨⟨out,origins,charges,first,bound,tensor⟩⟩

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
