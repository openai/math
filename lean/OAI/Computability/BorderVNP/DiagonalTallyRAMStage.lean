import OAI.Computability.BorderVNP.DiagonalTallyRAMFrame
import OAI.Computability.BorderVNP.DiagonalTallyRAMTrace
import OAI.Computability.BorderVNP.DiagonalTallyRAMValues
import OAI.Computability.BorderVNP.DiagonalTallyBitsPack

/-! # Linked execution of the complete distributed tally stage

The only comparison with the candidate common prefix is the check of the current
team's own row. Every entry of the global output is computed from that prefix. Once
all teams pass their checks, the broadcast therefore has one possible value.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ}

/-- The encoded subtotal proposed at a given team and coordinate. -/
def claimWord (f : Frame) (xs : List (List Bool)) (i j : ℕ) : Word w :=
  word w (VPVNP.TapeWord.value (xs[j+f.dim*i]?.getD []))

/-- The directory and input words immediately before and after decoding the broadcast. -/
structure Input {w : ℕ} (f : Frame) (pub : Arg → Word w) (m : Memory w)
    (rs : List (ℕ × ℕ)) (xs : List (List Bool)) : Prop where
  /-- All pointers and dimensions including end sentinels fit. -/
  fits : f.addressesFit w (pub 0).val
  /-- The original directory. -/
  initialFrame : f.resident pub m
  /-- The sparse record stream occupies its prescribed interval. -/
  recordsAt : DiagonalTallyScatter.RecordsAt m f.records rs
  /-- The record count agrees with the installed frame. -/
  recordCount : rs.length = f.count
  /-- Every coordinate is in the combined tally bank. -/
  coords : ∀ r ∈ rs, r.1 < f.dim
  /-- No partial sum wraps at any physical counter address. -/
  sumsFit : ∀ a, (m a).val + DiagonalTallyScatter.incrementAt f.localBase a rs < 2^w
  /-- Scatter does not overwrite its yet-unread records. -/
  separate : DiagonalTallyScatter.Separate f.localBase f.dim f.records (f.records+2*f.count)
  /-- The scalar directory remains readable after the local updates. -/
  afterLocalFrame : f.resident pub (DiagonalTallyScatter.after f.localBase rs m)
  /-- The bit stream of common, fixed-width subtotal words remains readable after scatter. -/
  bitsAt : DiagonalTallyBits.WordsAt (DiagonalTallyScatter.after f.localBase rs m) f.rawBits xs
  /-- The broadcast has one word for every team and coordinate. -/
  claimCount : xs.length = f.teams*f.dim
  /-- Every subtotal has its exact fixed binary length. -/
  wordLengths : ∀ b ∈ xs, b.length = f.width
  /-- The raw and decoded intervals do not overlap. -/
  packSeparate : f.rawBits+(f.teams*f.dim)*f.width ≤ f.claims ∨
    f.claims+f.teams*f.dim ≤ f.rawBits
  /-- The scalar directory is readable at both final subroutines. -/
  decodedFrame : f.resident pub (DiagonalTallyBits.outputMemory (DiagonalTallyScatter.after f.localBase rs m) f.claims xs)
  /-- The global output follows the decoded claim array. -/
  totalsSeparate : f.claims+f.dim*f.teams ≤ f.totals
  /-- The decoded subtotal words are separate from the local count bank. -/
  localSeparate : f.localBase+f.dim ≤ f.claims ∨ f.claims+f.teams*f.dim ≤ f.localBase

/-- The linked routine returns after the four directory reads and the sparse
update, bit decode, one row check, and all column sums. -/
def costBound (f : Frame) : ℕ :=
  scatterSetup.slots + packSetup.slots + verifySetup.slots + aggregateSetup.slots +
    (13*f.count+3) + (8*(f.teams*f.dim)*(f.width+1)+8) + (6*f.dim+1) +
    ((5*f.teams+8)*f.dim+1)

/-- Every encoded word appears at its prescribed rectangular address in the decoded memory. -/
theorem contains_claimWord (f : Frame) (xs : List (List Bool)) (m : Memory w)
    (hx : xs.length = f.teams*f.dim) :
    f.toTotalsFrame.contains (claimWord f xs) (DiagonalTallyBits.outputMemory m f.claims xs) := by
  intro i hi j hj
  have hj' : j+f.dim*i < xs.length := by
    rw [hx, Nat.mul_comm f.teams f.dim]
    have h := Nat.mul_le_mul_left f.dim (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at h
    omega
  rw [Nat.add_assoc, DiagonalTallyBits.outputMemory_word _ _ _ _ hj']
  simp [claimWord, List.getElem?_eq_getElem hj']

/-- The actual linked table has a positive, choice-free path for a valid assignment
and a broadcast agreeing with its own row. At the output it has written precisely the
sums of the individual decoded subtotal words. -/
theorem stage_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (rs : List (ℕ × ℕ)) (xs : List (List Bool))
    (h : Input f pub m rs xs)
    (hm : ∀ j < f.dim, DiagonalTallyScatter.after f.localBase rs m (f.localBase+j) =
      claimWord f xs f.team j) :
    let packed := DiagonalTallyBits.outputMemory (DiagonalTallyScatter.after f.localBase rs m) f.claims xs
    ∃ es t, Runs pub mac stage s m es t (writeTotals f.toTotalsFrame
        (fun j => ∑ i : Fin f.teams, claimWord f xs i.val j) packed 0 f.dim) ∧
      traceCost es ≤ costBound f ∧ ∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0 := by
  let localMem := DiagonalTallyScatter.after f.localBase rs m
  let packed := DiagonalTallyBits.outputMemory localMem f.claims xs
  have hh := h.fits
  obtain ⟨dir,localFit,recordFit,rawFit,claimFit,totalFit,teamFit,teamsFit,widthFit⟩ := hh
  obtain ⟨a,s₁,r₁,c₁,loaded⟩ := scatterSetup_runs pub mac m s f h.initialFrame h.fits
  obtain ⟨b,s₂,r₂,_,_,c₂⟩ := DiagonalTallyScatter.scatter_runs pub mac s₁ m rs loaded (by rw [h.recordCount])
    localFit.le h.separate h.recordsAt h.coords h.sumsFit
  obtain ⟨c,s₃,r₃,c₃,p₅₀,p₅₁,p₅₂,p₅₃,p₆₃⟩ := packSetup_runs pub mac localMem s₂ f h.afterLocalFrame h.fits
  obtain ⟨d,s₄,r₄,c₄,_,_,_⟩ := DiagonalTallyBits.pack_runs pub mac s₃ localMem xs p₅₀ p₅₃
    (p₅₁.trans h.claimCount.symm) p₅₂ p₆₃ widthFit h.wordLengths
    (h.claimCount ▸ rawFit) (by rw [h.claimCount]; omega)
    (h.claimCount ▸ h.packSeparate) h.bitsAt
  obtain ⟨e,s₅,r₅,c₅,h₄₈,h₄₉,h₅₀,h₆₃⟩ := verifySetup_runs pub mac packed s₄ f h.decodedFrame h.fits
  have table := contains_claimWord f xs localMem h.claimCount
  have indexFit := Nat.mul_le_mul_right f.dim (Nat.succ_le_of_lt teamFit)
  rw [Nat.succ_mul] at indexFit
  obtain ⟨g,s₆,r₆,c₆,_,_,_,_⟩ := verifyRow_runs (pub := pub) (macros := mac) f.dim f.localBase
    (f.claims+f.team*f.dim) s₅ packed localFit (by omega) h₄₈ h₄₉ h₅₀ h₆₃ (by
      intro j hj
      have outside : f.localBase+j < f.claims ∨ f.claims+xs.length ≤ f.localBase+j := by
        rw [h.claimCount]
        rcases h.localSeparate with h | h <;> omega
      have he := DiagonalTallyBits.outputMemory_outside localMem f.claims (f.localBase+j) xs outside
      have hx := table f.team teamFit j hj
      exact he.trans ((hm j hj).trans (by simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hx.symm)))
  obtain ⟨k,s₇,r₇,c₇,hf,hj⟩ := aggregateSetup_runs pub mac packed s₆ f h.decodedFrame h.fits
  obtain ⟨l,t,r₈,c₈,_,_⟩ := aggregate_runs (pub := pub) (macros := mac) f.toTotalsFrame
    ⟨by simpa [Nat.mul_comm] using claimFit,totalFit,teamsFit⟩ h.totalsSeparate
    (claimWord f xs) 0 f.dim (Nat.zero_add _) s₇ packed hf (by simpa using hj) table
  have run := r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq r₈))))))
  refine ⟨_,t,run, ?_, ordinary_run (show ordinary stage = true by decide) run⟩
  simp only [traceCost,VPVNP.RAMBuckets.cost_append]
  change traceCost a + (traceCost b + (traceCost c + (traceCost d + (traceCost e +
    (traceCost g + (traceCost k + traceCost l)))))) ≤ _
  rw [ordinary_cost (by decide) r₂, ordinary_cost (by decide) r₄, ordinary_cost (by decide) r₆,
    ordinary_cost (by decide) r₈, c₂.1, c₄.1, c₆.1, c₈.1, h.claimCount,h.recordCount]
  have hx := DiagonalTallyBits.ticks_le (f.teams*f.dim) f.width
  unfold costBound
  omega

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
