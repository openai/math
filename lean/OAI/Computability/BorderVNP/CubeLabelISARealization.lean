import OAI.Computability.BorderVNP.CubeLabelISAChooser
import OAI.Computability.BorderVNP.CubeLabelISATicks

/-! # Physical execution of the complete sparse label scan

The hypotheses refer only to the decoded frame, incidence lists, and the unbounded
natural memory images. The conclusion runs the single fixed instruction table with
arbitrary initial registers and reads back every chosen label and final bin word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM

/-- Natural-word room for the reachable label and mean tables, including separation
of the output label array from all cache writes. -/
structure Frame.Fitted (p : Frame) (w z : ℕ) (rows : ℕ → List Incident) (m : ℕ → ℕ) : Prop where
  /-- Number of legal labels. -/
  alphabet : p.Z = z+1
  /-- Last counted bin ordinal fits in a word. -/
  count : p.Z^2+p.Z < 2^w
  /-- Addresses of the final chosen labels. -/
  labels : ∀ c < p.cells, p.labels+c < 2^w
  /-- The label array is disjoint from the conditional-mean cache. -/
  distinct : ∀ c < p.cells, ∀ i < p.Z^2+p.Z, p.labels+c ≠ p.cacheAddr i
  /-- All candidate queries are safe on the natural prefix image. -/
  trials : ∀ c < p.cells, ∀ v : Fin (z+1),
    PassRoom p w c v.val (p.prefix z rows m c) (rows c) false
  /-- Updating the winning cache preserves its own incident input arrays. -/
  commits : ∀ c < p.cells, let t := p.prefix z rows m c
    PassRoom p w c (p.winner z c t (rows c)).val t (rows c) true

private theorem commit_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (p : Frame) (c v : ℕ) (s : Bank w) (m : Memory w) (rows : List Incident)
    (h : p.registers s) (hc : (s 1).val = c) (hv : (s 2).val = v)
    (room : PassRoom p w c v (readings m) rows true) :
    ∃ tr t mt, Runs pub macros commit s m tr t mt ∧ traceCost tr ≤ p.passTicks rows ∧
      p.registers t ∧ readings mt = (p.bins c v (readings m) rows).image (readings m) (p.Z^2+p.Z) := by
  obtain ⟨tr,t,mt,run,cost,_,_,mem⟩ := framePass_run pub macros true p c v s m rows h hc hv
    room.room room.same room.fit
  exact ⟨_,_,_,run,cost,p.registers_run h run (by decide),mem⟩

private theorem readings_update {w : ℕ} (m : Memory w) (k : ℕ) (v : Word w) :
    readings (Function.update m k v) = Function.update (readings m) k v.val := by
  funext j
  by_cases eq : j = k <;> simp [readings,eq]

private theorem assignment {w z : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (p : Frame) (rows : ℕ → List Incident) (m₀ : ℕ → ℕ) (fit : p.Fitted w z rows m₀) :
    let pref := p.prefix z rows m₀
    let score := fun c (v : Fin (z+1)) => p.score c (pref c) (rows c) v.val
    AssignmentPass pub macros candidate commit p.cells p.labels
      (fun c => p.passTicks (rows c)+1) (fun c => p.passTicks (rows c)) score p.registers
      (fun c m => readings m = pref c) (fun c m => readings m = p.updated z c (pref c) (rows c)) := by
  intro pref score
  refine ⟨fun s h => ⟨h 19 (by decide), h 20 (by decide), h 21 (by decide)⟩,?_,fit.labels,?_,
    by decide,?_,?_⟩
  · intro s h k hk u
    apply p.registers_update h
    rcases hk with rfl|rfl|rfl <;> decide
  · intro c hc m image
    refine ⟨fun s h => ⟨(h.1 0 (by decide)).trans fit.alphabet, h.1 20 (by decide),h.1 23 (by decide)⟩,
      ?_,?_,?_⟩
    · intro s hs k hk u
      have off : k ∉ params := by rcases hk with rfl|rfl|rfl <;> decide
      have ne : (1 : Reg) ≠ k := by rcases hk with rfl|rfl|rfl <;> decide
      exact ⟨p.registers_update hs.1 off u,by rw [Function.update_of_ne ne]; exact hs.2⟩
    · intro k hk
      rcases hk with rfl|rfl|rfl <;> decide
    · intro v s hs hv
      obtain ⟨tr,t,run,cost,ht,cell,result⟩ := candidate_run pub macros p c v s m (rows c)
        hs.1 hs.2 hv (image ▸ fit.trials c hc v)
      rw [image] at result
      exact ⟨_,_,run,cost,⟨ht,cell⟩,result⟩
  · intro c hc s m hs cell image hv
    let v := p.winner z c (pref c) (rows c)
    change (s 2).val = v.val at hv
    obtain ⟨tr,t,mt,run,cost,ht,mem⟩ := commit_run pub macros p c v s m (rows c) hs cell hv
      (image ▸ fit.commits c hc)
    refine ⟨_,_,_,run,cost,ht,by simpa only [image,Frame.updated,v] using mem,?_⟩
    intro j hj
    apply Fin.ext
    change readings mt (p.labels+j) = readings m (p.labels+j)
    rw [mem]
    exact PassBins.image_off _ _ _ _ (fun i hi => fit.distinct j (hj.trans hc) i hi)
  · intro c _ m after v hv
    rw [readings_update,after,hv]
    rfl

/-- The actual native table returns the complete memory image, including the same first
minimizer as the unbounded natural calculation for each visited cell. The upper bound
counts the linked visits, arithmetic, all trials and commits, and frame reads. -/
theorem program_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (z : ℕ) (rows : ℕ → List Incident) (s : Bank w) (m : Memory w)
    (hf : (pub 0).val+56 < 2^w)
    (fit : (Frame.decode (pub 0).val (readings m)).Fitted w z rows (readings m)) :
    let p := Frame.decode (pub 0).val (readings m)
    let pref := p.prefix z rows (readings m)
    ∃ tr t mt, Runs pub macros program s m tr t mt ∧
      traceCost tr ≤ assignmentTicks setup.slots z p.cells (fun c => (rows c).length) ∧
      (t 1).val = p.cells ∧ readings mt = pref p.cells ∧
      ∀ c < p.cells, (mt (p.labels+c)).val = (p.winner z c (pref c) (rows c)).val := by
  intro p pref
  obtain ⟨gs,b,load,setupCost,params,zero⟩ := setup_run pub macros s m hf fit.count
  have ctx := assignment pub macros p rows (readings m) fit
  obtain ⟨fs,t,mt,run,cost,_,cells,mem,labels⟩ := assign_run ctx (c := 0) (Nat.zero_le _)
    b m params zero rfl (fun _ hj => (Nat.not_lt_zero _ hj).elim)
  refine ⟨_,t,mt,load.seq run,?_,cells,mem,labels⟩
  unfold assignmentTicks
  apply (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add setupCost ?_)
  have hz : p.Z = z+1 := fit.alphabet
  simpa only [Frame.passTicks,hz,scoreTicks,commitTicks,Nat.add_assoc] using cost

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
