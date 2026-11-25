import OAI.ThreeFlat.RAM.HistoryStageLeafResources
import OAI.ThreeFlat.RAM.HistoryStageGuardFee

namespace OAI
/-! # Resource bound for the complete list of selected family procedures -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- Address fields may move within the selected-stage archive without changing the program type. -/
def Family.schema (f : Family) := {f with kinds:=0,ports:=0}

private theorem folded_budget {W : ℕ} (leaf : Procedure W) (leafBound : ℕ) (hLeaf : resources leaf ≤ leafBound)
    (branch : Family → Procedure W) (gate : Family → Formula 1) (work charge : Family → ℕ)
    (gateWork : ∀ f g, (gate g).work = work f) (fs : List Family)
    (paid : ∀ f ∈ fs, ∀ g : Family, g.schema = f.schema → resources (branch g) ≤ charge f) :
    ∀ gs : List Family, gs.map Family.schema = fs.map Family.schema →
      resources (gs.foldr (fun g next => ifValue (gate g) (branch g) next) leaf) ≤
        leafBound + (fs.map (fun f => 6+4*work f+charge f)).sum := by
  induction fs with
  | nil =>
    intro gs same
    cases gs with
    | nil => simpa only [List.foldr_nil, List.map_nil, List.sum_nil, Nat.add_zero] using hLeaf
    | cons g gs => cases same
  | cons f fs ih =>
    intro gs same
    cases gs with
    | nil => cases same
    | cons g gs =>
      simp only [List.map_cons, List.cons.injEq] at same
      have first := paid f (List.mem_cons_self ..) g same.1
      have rest := ih (fun x hx => paid x (List.mem_cons_of_mem _ hx)) gs same.2
      simp only [List.foldr_cons, resources_if, List.map_cons, List.sum_cons, gateWork f g]
      omega


attribute [local irreducible] leafResources HistoryInitialSeed.procedure HistoryStageBody.procedure
  enabled HistoryNodeDirectory.Selected.procedure

/-- A finite family supremum can now be charged once per stage arm; the final 49 words
are the true selected-owner loop, including its six public parameters. -/
theorem selected_resources_of_arms (fs : List Family) (charge : Family→ℕ)
    (arms : ∀ f∈fs,∀ (W u : ℕ) (a : Archive) (g : Family),g.schema=f.schema →
      resources (HistoryStageBody.procedure (layout u a g) g.childBound W)≤charge f) :
    ∀ (W u : ℕ) (a : Archive) (s : TraceBucketAtom.Layout) (pub : Fin TraceEndpointROM.params→Word W) (gs : List Family),
      gs.map Family.schema = fs.map Family.schema →
      resources (selected W u a s pub gs) ≤ 49+leafResources+(fs.map (fun f=>6+4*(enabled 0 f).work+charge f)).sum := by
  intro W u a s pub gs same
  have folded : resources (body W u a s pub gs) ≤
      leafResources+(fs.map (fun f=>6+4*(enabled 0 f).work+charge f)).sum :=
    folded_budget (HistoryInitialSeed.procedure W (initial u s) pub) leafResources
      (leaf_resources (initial u s) pub) (fun g=>HistoryStageBody.procedure (layout u a g) g.childBound W)
      (enabled u) (fun f=>(enabled 0 f).work) charge (fun f g=>enabled_work u 0 g f) fs
      (fun f hf g eqv => arms f hf W u a g eqv) gs same
  calc
    resources (selected W u a s pub gs) = 49+resources (body W u a s pub gs) :=
      resources_guard (ownerData W u) (body W u a s pub gs)
    _ ≤ 49+(leafResources+_) := Nat.add_le_add_left folded 49
    _ = _ := (Nat.add_assoc ..).symm


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
