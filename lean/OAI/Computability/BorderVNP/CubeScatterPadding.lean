import OAI.Computability.BorderVNP.CubeScatterPaddingBits
import OAI.Computability.BorderVNP.CubeScatterPaddingLoop
import OAI.Computability.BorderVNP.CubeScatterPaddingSetup
import OAI.Computability.BorderVNP.CubeScatterPaddingStage

/-! # Exact native check of all padding owned by the executing team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA VPVNP.BurstRAM HostScatter Finset

/-- A single owned endpoint stages the actual metadata and verifies its unused interval. -/
def endpoint (side : Bool) : Code :=
  .seq (ownerStep side) (.ifEq 33 29 (.seq (cacheStep side) bits) .nop)

/-- Complete finite instruction fragment from the published frame. -/
def verify : Code := .seq setup (forPairs endpoint)

/-- This fixed constant covers the two metadata stages, owner branch and bit-loop initialization. -/
def overhead := 64

/-- The physical time is linear in the number of candidate pairs plus actual assigned slots. -/
def Layout.budget (l : Layout) (m : ℕ → ℕ) :=
  setup.slots+2+l.count*(2*overhead+2)+bitCost*∑ i ∈ range l.count, (l.assigned m i false+l.assigned m i true)

private theorem keptReady {l : Layout} {a b : NatState} (h : l.Ready a) (keep : Kept a.reg b.reg) : l.Ready b := by
  unfold Layout.Ready at *
  repeat' apply And.intro
  all_goals exact (keep _ (by decide) (by decide)).trans (by tauto)

private theorem branch {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {x y : Reg} {s : Bank w} {m : Memory w} {a b : Code} {cost ok post}
    (test : TestRun pub mac (if s x=s y then a else b) s m cost ok post) :
    TestRun pub mac (.ifEq x y a b) s m (1+cost) ok post := by
  constructor
  · intro good
    obtain ⟨es,t,mt,run,bound,after⟩ := test.complete good
    exact ⟨_,t,mt,Runs.ifEq run,Nat.add_le_add_left bound _,after⟩
  · intro es t mt run
    obtain ⟨_,_,ht⟩ := CellDispatch.eq_split run
    exact test.sound ht

private def good (l : Layout) (before : ℕ → ℕ) (i : ℕ) (side : Bool) :=
  l.owner before i side = l.team → ∀ j < (l.fields before i side).width, before ((l.fields before i side).source j)=0

/-- Nonowned endpoints pay only the owner lookup. Owned endpoints read precisely
their own unused physical slots. All original RAM words survive each test. -/
theorem test_endpoint {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) {i : ℕ} (hi : i<l.count) (side : Bool) (s : Bank w) (m : Memory w)
    (fit : l.Fits w (readings m)) (ready : l.Ready (.ofWords s m)) (idx : (s 13).val=i) :
    TestRun pub mac (endpoint side) s m (overhead+bitCost*l.assigned (readings m) i side)
      (good l (readings m) i side) (fun z => l.Ready z ∧ z.reg 13=i ∧ z.mem=readings m) := by
  let owned := l.owner (readings m) i side = l.team
  let f := l.fields (readings m) i side
  let charge := if owned then (cacheStep side).slots+(2+f.width*bitCost) else 1
  have read := (run_ownerStep pub mac l hi side s m fit ready idx).asTest (by cases side <;> decide)
  apply (read.seq (cb := 1+charge) (ob := good l (readings m) i side) ?_).mono ?_ (by simp) (fun _ => id)
  · intro t mt h
    obtain ⟨rd,ix,who,mem⟩ := h
    have team : (t 29).val=l.team := by unfold Layout.Ready at rd; tauto
    change (t 33).val = l.owner (readings m) i side at who
    change readings mt = readings m at mem
    have actual : t 33=t 29 ↔ owned := by change _ ↔ _ = _; rw [Fin.ext_iff,who,team]
    apply branch
    by_cases yes : owned
    · rw [ite_eq_left (actual.mpr yes)]
      change TestRun _ _ _ _ _ (if owned then _ else _) _ _
      rw [ite_eq_left yes]
      have fit' : l.Fits w (readings mt) := mem.symm ▸ fit
      have load := (run_cacheStep pub mac l hi side t mt fit' rd ix).asTest (by cases side <;> decide)
      apply (load.seq (cb := 2+f.width*bitCost) (ob := ∀ j < f.width, readings m (f.source j)=0) ?_).mono le_rfl ?_ (fun _ => id)
      · intro u mu h
        obtain ⟨rd',ix',cached,same⟩ := h
        have fm : readings mu=readings m := same.trans mem
        rw [mem] at cached
        have cached' : f.Ready (.ofWords u mu) := cached
        have checked := run_bits pub mac f (fit.bits _ hi _ yes) u mu cached'
        refine checked.mono le_rfl (by rw [fm]) ?_
        rintro z ⟨keep,hmem⟩
        exact ⟨keptReady rd' keep,(keep 13 (by decide) (by decide)).trans ix',hmem.trans fm⟩
      · simp [good,f,show l.owner (readings m) i side = l.team from yes]
    · rw [ite_eq_right (fun h => yes (actual.mp h))]
      change TestRun _ _ _ _ _ (if owned then _ else _) _ _
      rw [ite_eq_right yes]
      have pass := ((Code.nop.runFixed pub mac t mt trivial).asTest (by decide))
      refine pass.mono le_rfl (by simp [good,show l.owner (readings m) i side ≠ l.team from yes]) ?_
      rintro z rfl
      exact ⟨rd,ix,mem⟩
  · by_cases yes : owned
    · simp only [charge,yes,ite_true,Layout.assigned,show l.owner (readings m) i side = l.team from yes,f]
      rw [Nat.mul_comm bitCost]
      cases side <;> change _ ≤ 64+_ <;> norm_num [ownerStep,cacheStep,Code.block,Code.slots] <;> omega
    · simp [charge,yes,Layout.assigned,show l.owner (readings m) i side ≠ l.team from yes]
      cases side <;> decide

/-- The complete instruction table accepts exactly when both ends of every owned
padding slot are zero, within the explicit candidate-and-assigned-slot time. -/
theorem test_verify {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame : ℕ) (atFrame : readings pub 0=frame)
    (header : HeaderFits w frame (readings m))
    (fit : (Layout.fromFrame frame (readings m)).Fits w (readings m)) :
    let l := Layout.fromFrame frame (readings m)
    TestRun pub mac verify s m (l.budget (readings m)) (l.Valid (readings m)) (fun z => z.mem=readings m) := by
  intro l
  let stable (z : NatState) := l.Ready z ∧ z.mem=readings m
  let costs i side := overhead+bitCost*l.assigned (readings m) i side
  have init := (run_setup pub mac s m frame atFrame header).asTest (by decide)
  apply (init.seq (cb := pairBudget l.count costs) (ob := l.Valid (readings m)) (Q := fun z => z.mem=readings m) ?_).mono ?_ (by simp) (fun _ => id)
  · intro t mt h
    refine (test_forPairs pub mac endpoint l.count costs (good l (readings m)) stable ?_ ?_ ?_ t mt h).mono le_rfl Iff.rfl (fun _ hz => hz.1.2)
    · intro z hz; exact ⟨hz.1.1,hz.1.2.1,hz.1.2.2.2.2.2.1⟩
    · intro z v hz; refine ⟨?_,hz.2⟩
      simpa (config := {decide := true}) [Layout.Ready] using hz.1
    · intro i hi side u mu h ix
      have mem := h.2
      change readings mu = readings m at mem
      have pass := test_endpoint pub mac l hi side u mu (mem.symm ▸ fit) h.1 ix
      rw [mem] at pass
      exact pass.mono le_rfl Iff.rfl (fun _ z => ⟨⟨z.1,z.2.2⟩,z.2.1⟩)
  · exact (Nat.add_le_add_left (pairBudget_le l.count overhead bitCost costs (l.assigned (readings m)) (fun _ _ _ => le_rfl)) _).trans_eq (by simp [Layout.budget,Nat.add_assoc])

/-- The verifier has no branching instructions that introduce choices or signed factors. -/
theorem verify_unsigned : verify.unsigned = true := by decide

/-- Its native rows have at most one complete return trace, including all guard events. -/
theorem verify_deterministic : verify.deterministic = true := by decide

/-- A complete successful physical scan has a unique positive trace. Every event
consumes the empty choice string. The returned memory is exactly its original image. -/
theorem verify_iff_unique {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame : ℕ) (atFrame : readings pub 0=frame)
    (header : HeaderFits w frame (readings m))
    (fit : (Layout.fromFrame frame (readings m)).Fits w (readings m)) :
    let l := Layout.fromFrame frame (readings m)
    l.Valid (readings m) ↔ ∃! es, ∃ t mt, Runs pub mac verify s m es t mt ∧
      traceCost es ≤ l.budget (readings m) ∧ readings mt = readings m ∧
      ∀ v ∈ es, v.choices = [] ∧ v.sign = .plus := by
  intro l
  have test := test_verify pub mac s m frame atFrame header fit
  constructor
  · intro good
    obtain ⟨es,t,mt,run,time,mem⟩ := test.complete good
    refine ⟨es,⟨t,mt,run,time,mem,?_⟩,?_⟩
    · exact run.unsigned_events verify_unsigned
    · rintro other ⟨u,mu,h,_,_,_⟩
      exact (h.unique_of_deterministic verify_deterministic run).1
  · rintro ⟨es,⟨t,mt,run,_,_,_⟩,_⟩
    exact (test.sound run).1

end Cube.Padding

end BorderVNP
end Computability
end OAI
