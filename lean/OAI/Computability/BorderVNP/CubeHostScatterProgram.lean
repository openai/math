import OAI.Computability.BorderVNP.CubeHostScatterVisit
import OAI.Computability.BorderVNP.CubeHostScatterSetup
import OAI.Computability.BorderVNP.CubeHostScatterReadback
import OAI.Computability.BorderVNP.TransmissionCost
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Running the physical host-cable scatter across the whole compressed directory

The outer scan charges a constant per cable and per owned incident bit. The
complete memory image includes both endpoint visits and all skipped cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Visit the two endpoints of each descriptor in its public order. -/
def traversal : Code := .seq (.copy 13 0) (.whileLt 13 5 rowStep)

/-- Load the shared public frame and scatter all owned host inputs. -/
def program : Code := setup.seq traversal

/-- Upper bound charging the bit loop only on the team's owned crossing endpoints. -/
def traversalTicks (l : Layout) (before : ℕ → ℕ) : ℕ :=
  2+l.count*(rowOverhead+1)+l.incident before*(scatterStep.slots+1)

/-- Numerical clock of the native code: 68 setup and terminating ticks,
82 per cable, and 22 per copied incident bit. -/
theorem program_ticks (l : Layout) (before : ℕ → ℕ) :
    setup.slots + traversalTicks l before = 68 + 82*l.count + 22*l.incident before := by
  rw [traversalTicks,setup_slots,show rowOverhead = 81 by decide,show scatterStep.slots = 21 by decide]
  omega

/-- The outer loop visits the actual compressed table, and the visited prefix
retains the input words needed to execute every later row. -/
theorem run_traversal {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) (s : Bank w) (m : Memory w)
    (ready : l.Ready (.ofWords s m)) (initial : readings m = before) :
    BoundedRun pub macros traversal s m (traversalTicks l before) (fun z =>
      l.Ready z ∧ z.reg 13 = l.count ∧ z.mem = l.prefix before l.count) := by
  let I (i : ℕ) (u : Bank w) (mu : Memory w) := l.Ready (.ofWords u mu) ∧ (u 13).val = i ∧
    readings mu = l.prefix before i ∧ l.Frozen before (readings mu)
  have fields (i : ℕ) (u : Bank w) (mu : Memory w) (h : I i u mu) :
      (u 13).val = i ∧ (u 5).val = l.count := ⟨h.2.1,h.1 5 (by decide)⟩
  have step (i : ℕ) (hi : i < l.count) (u : Bank w) (mu : Memory w) (h : I i u mu) :
      ∃ es t mt, Runs pub macros rowStep u mu es t mt ∧ I (i+1) t mt ∧ traceCost es ≤ rowTicks l before i := by
    obtain ⟨es,t,mt,run,cost,ready',idx,mem⟩ := run_rowStep pub macros l before fit hi u mu h.1 h.2.1 h.2.2.2
    have both := ((h.2.2.2.copyEnd fit hi false).copyEnd fit hi true)
    change readings mt = _ at mem
    refine ⟨es,t,mt,run,⟨ready',idx,?_,mem ▸ both⟩,cost⟩
    simpa only [Layout.prefix,← h.2.2.1] using mem
  have init := (Code.copy 13 0).runFixed pub macros s m trivial
  obtain ⟨es,u,mu,load,loadCost,img⟩ := init
  have initI : I 0 u mu := by
    change l.Ready (.ofWords u mu) ∧ (NatState.ofWords u mu).reg 13 = 0 ∧
      (NatState.ofWords u mu).mem = l.prefix before 0 ∧ l.Frozen before (NatState.ofWords u mu).mem
    rw [img]
    refine ⟨fun r hr => ?_,ready 0 (by decide),initial,?_⟩
    · have ne : r ≠ 13 := by rintro rfl; norm_num at hr
      change Function.update _ 13 _ r = _
      rw [Function.update_of_ne ne]
      exact ready r hr
    · change l.Frozen before (readings m)
      rw [initial]
      exact fun _ _ => rfl
  obtain ⟨fs,t,mt,loop,done,cost⟩ := Transmission.loop_runs 13 5 rowStep l.count (rowTicks l before)
    I fields step 0 (Nat.zero_le _) u mu initI
  have sum : (∑ j ∈ Finset.Ico 0 l.count, (rowTicks l before j + 1)) =
      l.count*(rowOverhead+1) + l.incident before*(scatterStep.slots+1) := by
    rw [Nat.Ico_zero_eq_range]
    simp_rw [rowTicks,show ∀ x, rowOverhead+x+1 = (rowOverhead+1)+x by omega]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,← Finset.sum_mul,
      Layout.incident,Nat.cast_id,Nat.mul_add]
  rw [sum] at cost
  refine ⟨es++fs,t,mt,.seq load loop,?_,done.1,done.2.1,done.2.2.1⟩
  change traceCost es ≤ 1 at loadCost
  rw [Transmission.cost_append]
  dsimp only [traversalTicks]
  omega

/-- The fixed native program starts on the real physical frame and produces
the complete host-cable image, with time linear in descriptor and owned bit counts. -/
theorem run_program {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (hf : readings pub 0 = l.frame) (frame : l.Frame (readings m))
    (frameFit : l.frame+94 < 2^w) (headerFit : readings m (l.frame+63)+8 < 2^w) :
    BoundedRun pub macros program s m (setup.slots+traversalTicks l (readings m)) (fun z =>
      l.Ready z ∧ z.reg 13 = l.count ∧ z.mem = l.prefix (readings m) l.count) := by
  apply (run_setup pub macros l s m hf frame frameFit headerFit).seq
  intro u mu hu
  exact run_traversal pub macros l (readings m) fit u mu hu.1 hu.2

/-- Every completed native run on the physical frame has the stated clock and
output image. This uses uniqueness of the trace of the deterministic program. -/
theorem program_all_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (hf : readings pub 0 = l.frame) (frame : l.Frame (readings m))
    (frameFit : l.frame+94 < 2^w) (headerFit : readings m (l.frame+63)+8 < 2^w)
    {es : List (TeamRAM.Event w)} {t : Bank w} {mt : Memory w} (run : Runs pub macros program s m es t mt) :
    traceCost es ≤ setup.slots+traversalTicks l (readings m) ∧ l.Ready (.ofWords t mt) ∧
      (t 13).val = l.count ∧ readings mt = l.prefix (readings m) l.count := by
  obtain ⟨fs,u,mu,ok,cost,done⟩ := run_program pub macros l s m fit hf frame frameFit headerFit
  obtain ⟨rfl,rfl,rfl⟩ := run.unique_of_deterministic (by decide) ok
  exact ⟨cost,done⟩

/-- Starting from just the public frame, the actual word arrays determine the
layout, final image, and numerical clock of the scatter. -/
theorem run_fromFrame {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    let before := readings m
    let base := readings pub 0
    let l := Layout.fromFrame base before
    l.Fits w before → base+94 < 2^w → before (base+63)+8 < 2^w →
    BoundedRun pub macros program s m (68+82*l.count+22*l.incident before) (fun z =>
      l.Ready z ∧ z.reg 13 = l.count ∧ z.mem = l.prefix before l.count) := by
  intro before base l fit frameFit headerFit
  rw [← program_ticks]
  exact run_program pub macros l s m fit rfl (Layout.fromFrame_frame ..) frameFit headerFit

/-- Each successful native traversal reads back every owned cable bit at its
actual bank destination and leaves the exterior complement untouched. -/
theorem program_readback {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {es : List (TeamRAM.Event w)} {t : Bank w} {mt : Memory w}
    (run : Runs pub macros program s m es t mt) :
    let before := readings m
    let base := readings pub 0
    let l := Layout.fromFrame base before
    l.Fits w before → base+94 < 2^w → before (base+63)+8 < 2^w → l.SeparateDestinations before →
    traceCost es ≤ 68+82*l.count+22*l.incident before ∧
      (∀ i < l.count, ∀ side, l.Owned before i side → ∀ j < l.width before i,
        readings mt (l.dest before i side+j) = before (l.source before i side j)) ∧
      ∀ a, (∀ i < l.count, ∀ side, l.Owned before i side →
        a < l.dest before i side ∨ l.dest before i side+l.width before i ≤ a) → readings mt a = before a := by
  intro before base l fit frameFit headerFit apart
  obtain ⟨cost,_,_,mem⟩ := program_all_runs pub macros l s m fit rfl (Layout.fromFrame_frame ..) frameFit headerFit run
  rw [mem]
  exact ⟨(program_ticks l before) ▸ cost,l.prefix_readback before apart⟩


end Cube.HostScatter

end BorderVNP
end Computability
end OAI
