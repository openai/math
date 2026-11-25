import OAI.Hierarchy.DescentRosterLayers

namespace OAI
/-! # Running one multiplier candidate against the physical adjacency table -/

namespace Hierarchy.DescentColonies.RosterCandidate
open DescentGL NativeBatch ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {G ℓ Δ k w : ℕ}

def inner (w ℓ Δ k adj q D cap : ℕ) (mapped : Fin (2^ℓ)→ℕ) : Code w :=
  let ps := RosterLayers.passes ℓ Δ k adj q mapped D cap
  let stop := PhysicalCensus.output (2^ℓ) k q
  let banks := LayerRAM.address (H:=(2^ℓ)) k q
  ⟨(ProtocolRAM.program w ps).seq (CensusRAM.program w k stop banks),
   CensusRAM.after k stop banks ∘ ProtocolRAM.result ps,
   ProtocolRAM.clock ps+(4+1*(2*(CensusRAM.expression k banks).work+4))⟩

def group (w ℓ Δ k adj base D cap : ℕ) (p : Fin (2^ℓ)→ℕ) (a μ : Bits k) : Code w :=
  (SiteRAM.rearrange w k base p a μ).thenDo
    (inner w ℓ Δ k adj (SiteRAM.bank k base (2^ℓ)) D cap (fun v=>SiteRAM.bank k base v.val))

def code (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) (μ : Nonzero k) : Code w :=
  (Code.seq (fun g : Fin G=>group w ℓ Δ k adj (CandidateRAM.output g.val (2^ℓ) k base) D cap (ptr g) a μ.val)
    G le_rfl).thenDo (CandidateRAM.summary w G (2^ℓ) k base)

private theorem group_exec (ℓ Δ adj base D cap : ℕ) (p : Fin (2^ℓ)→ℕ) (a μ : Bits k)
    (old : ∀v,p v+2^k≤base) (sep : adj+(2^ℓ)*Δ≤base) (wide : 2^(ℓ+k)<2^w)
    (room : SiteRAM.scoreAt (2^ℓ) k base+1<2^w) :
    (group w ℓ Δ k adj base D cap p a μ).exec := by
  let q := SiteRAM.bank k base (2^ℓ)
  let ptr := fun v : Fin (2^ℓ)=>SiteRAM.bank k base v.val
  let ps := RosterLayers.passes ℓ Δ k adj q ptr D cap
  have front : base≤q := Nat.le_add_right ..
  have qfit := (SiteRAM.score_ge (2^ℓ) k base).trans_lt (show SiteRAM.scoreAt (2^ℓ) k base<2^w by omega)
  have fit := RosterLayers.fits (k:=k) adj q D cap ptr (SiteRAM.transfer_bound k base)
    (sep.trans front) wide (show q+k*(2^ℓ)*2^k<2^w from (Nat.lt_succ_self _).trans room)
  apply Code.exec_seq (SiteRAM.rearrange_exec base p a μ old qfit)
  intro m labels registers slots machine
  exact Procedure.Exec.then (program_exec ps m fit)
    (CensusRAM.run _ _ _ room (PhysicalCensus.bank_before q)) machine

private theorem group_same (ℓ Δ adj base D cap : ℕ) (rs : DynamicSplit.Roster ℓ Δ)
    (p : Fin (2^ℓ)→ℕ) (a μ : Bits k) (m : Memory w) (data : DynamicSplit.Stored adj rs m)
    (sep : adj+(2^ℓ)*Δ≤base) (wide : 2^(ℓ+k)<2^w) :
    (group w ℓ Δ k adj base D cap p a μ).after m=
    (SiteRAM.groupCode w k base (DynamicSplit.incoming rs) p D cap a μ).after m := by
  let mid := (SiteRAM.rearrange w k base p a μ).after m
  let q := SiteRAM.bank k base (2^ℓ)
  let ptr := fun v : Fin (2^ℓ)=>SiteRAM.bank k base v.val
  have atMid : DynamicSplit.Stored adj rs mid := RosterLayers.saved data sep
    (fun z mZ=>SiteRAM.rearrange_below base p a μ m z mZ)
  exact congrArg (CensusRAM.after k (PhysicalCensus.output (2^ℓ) k q) (LayerRAM.address (H:=(2^ℓ)) k q))
    (RosterLayers.same adj q D cap rs ptr mid atMid (sep.trans (Nat.le_add_right ..)) wide)

/-- The two chronological executions agree after every group, so the native
winner-gather and each later read see exactly the old physical score ledger. -/
theorem seq_same {w N : ℕ} (new old : Fin N → Code w) (P : Memory w→Prop)
    (one : ∀i m,P m→(new i).after m=(old i).after m) (preserves : ∀i m,P m→P ((old i).after m))
    (m : Memory w) (valid : P m) (n : ℕ) (hn : n≤N) :
    (Code.seq new n hn).after m=(Code.seq old n hn).after m ∧ P ((Code.seq old n hn).after m) := by
  induction n with
  | zero=>exact ⟨rfl,valid⟩
  | succ n ih=>
    obtain ⟨same,saved⟩ := ih (show n≤N by omega)
    let i : Fin N := ⟨n,hn⟩
    change (new i).after ((Code.seq new n _).after m)=(old i).after ((Code.seq old n _).after m) ∧ _
    rw [same]
    exact ⟨one i _ saved,preserves i _ saved⟩

theorem same (ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ)
    (μ : Nonzero k) (rs : DynamicSplit.Roster ℓ Δ) (m : Memory w) (data : DynamicSplit.Stored adj rs m)
    (sep : adj+(2^ℓ)*Δ≤base) (wide : 2^(ℓ+k)<2^w) :
    (code w ℓ Δ adj base D cap a ptr μ).after m=
    CandidateRAM.after base (DynamicSplit.incoming rs) ptr D cap a μ m := by
  let jobs := fun g : Fin G=>group w ℓ Δ k adj (CandidateRAM.output g.val (2^ℓ) k base) D cap (ptr g) a μ.val
  let old := CandidateRAM.steps w base (DynamicSplit.incoming rs) ptr D cap a μ
  have forward := seq_same jobs old (DynamicSplit.Stored adj rs)
    (fun g prior read=>group_same ℓ Δ adj _ D cap rs (ptr g) a μ.val prior read
      (sep.trans (CandidateRAM.start ..)) wide)
    (fun g prior read=>RosterLayers.saved read sep (fun z lo=>SiteRAM.below _ _ _ _ _ _ _ prior z
      (lo.trans_le (CandidateRAM.start ..)))) m data G le_rfl
  exact congrArg (CandidateRAM.summary w G (2^ℓ) k base).after forward.1

theorem execute (ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) (μ : Nonzero k)
    (old : ∀g v,ptr g v+2^k≤base) (sep : adj+(2^ℓ)*Δ≤base) (wide : 2^(ℓ+k)<2^w)
    (room : CandidateRAM.output G (2^ℓ) k base+1<2^w) :
    (code w ℓ Δ adj base D cap a ptr μ).exec := by
  apply Code.exec_seq
  · apply Code.exec_seqAll
    intro g
    apply group_exec _ _ _ _ _ _ _ _ _ (fun v=>(old g v).trans (CandidateRAM.start ..))
      (sep.trans (CandidateRAM.start ..)) wide
    rw [CandidateRAM.next]
    exact (CandidateRAM.mono (2^ℓ) k base g.isLt).trans_lt (by omega)
  · intro m labels registers slots machine
    exact scan_exec (CandidateRAM.output G (2^ℓ) k base) 1
      (CandidateRAM.tally G (CandidateRAM.receipt (2^ℓ) k base)) m
      (CandidateRAM.tally_fits G _ _ (by omega) (CandidateRAM.live (2^ℓ) k base)) room machine

theorem exec_eq (ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) (μ : Nonzero k)
    (rs : DynamicSplit.Roster ℓ Δ) (m : Memory w) (data : DynamicSplit.Stored adj rs m)
    (old : ∀g v,ptr g v+2^k≤base) (sep : adj+(2^ℓ)*Δ≤base) (wide : 2^(ℓ+k)<2^w)
    (room : CandidateRAM.output G (2^ℓ) k base+1<2^w) :
    let job := code w ℓ Δ adj base D cap a ptr μ
    job.text.Exec m (CandidateRAM.after base (DynamicSplit.incoming rs) ptr D cap a μ m) job.ticks := by
  rw [←same ℓ Δ adj base D cap a ptr μ rs m data sep wide]
  exact execute ℓ Δ adj base D cap a ptr μ old sep wide room m

theorem bounded (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) (μ : Nonzero k) :
    let job := code w ℓ Δ adj base D cap a ptr μ
    CandidateRAM.Bounded job.text job.ticks := by
  apply CandidateRAM.seq_bound
  · apply CandidateRAM.batch_bound
    intro g
    apply CandidateRAM.seq_bound
    · exact CandidateRAM.batch_bound
        (SiteRAM.transfer w k (CandidateRAM.output g.val (2^ℓ) k base) (ptr g) a μ.val)
        (fun _=>CandidateRAM.scan_bound _ _ _ _ (Nat.two_pow_pos k)) _ _
    · exact CandidateRAM.seq_bound (RosterLayers.bounded ..) (CandidateRAM.scan_bound _ _ 1 _ (by decide))
  · exact CandidateRAM.scan_bound _ _ 1 _ (by decide)

private def groupBudget (ℓ k Δ : ℕ) :=
  (4+(2^ℓ)*(4+2^k*(2*(10*2^k+10)+4))) +
   ((4+k*(2^ℓ)*(4+2^k*(2*DynamicSplit.workBound k Δ+4)))+(4+1*(2*CensusRAM.workBound (2^ℓ) k+4)))

theorem ticks_bound (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) (μ : Nonzero k) :
    (code w ℓ Δ adj base D cap a ptr μ).ticks≤1000*(G+1)*((2^ℓ)+1)*(k+1)*(Δ+1)*(2^k+1)^4 := by
  have perGroup (g : Fin G) :
      (group w ℓ Δ k adj (CandidateRAM.output g.val (2^ℓ) k base) D cap (ptr g) a μ.val).ticks≤groupBudget ℓ k Δ := by
    apply Nat.add_le_add
    · apply Code.clock_seq
      intro i
      simp [SiteRAM.transfer,PermutationRAM.work]
    · apply Nat.add_le_add (RosterLayers.clock_le ..)
      gcongr
      exact CensusRAM.work ..
  have all := Code.clock_seq _ _ perGroup G le_rfl
  change (Code.seq _ G le_rfl).ticks+(4+1*(2*(CandidateRAM.tally G _).work+4))≤_
  rw [CandidateRAM.tally_work]
  apply (Nat.add_le_add_right all _).trans
  unfold groupBudget DynamicSplit.workBound DynamicSplit.laneWork DynamicSplit.neighborWork DynamicSplit.cellWork CensusRAM.workBound
  generalize 2^ℓ=h
  generalize 2^k=r
  zify
  apply sub_nonneg.mp
  ring_nf
  positivity

end Hierarchy.DescentColonies.RosterCandidate

end OAI
