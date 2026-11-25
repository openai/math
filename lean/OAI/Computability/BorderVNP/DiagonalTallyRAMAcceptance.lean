import OAI.Computability.BorderVNP.DiagonalTallyRAMStage

/-!
# Returning from the tally validator forces the claimed row

This is the converse to the constructed run. It uses the actual deterministic prefixes of
the emitted table, so a false claim cannot contribute a second successful continuation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem seq_tail {a b : Code} {s u z : Bank w} {m mu mz : Memory w} {es fs}
    (ra : Runs pub mac a s m es u mu) (hd : a.deterministic = true)
    (r : Runs pub mac (.seq a b) s m fs z mz) : ∃ gs, Runs pub mac b u mu gs z mz := by
  cases r with
  | atom h _ _ => cases h
  | seq first second =>
    obtain ⟨_,rfl,rfl⟩ := ra.unique_of_deterministic hd first
    exact ⟨_,second⟩

/-- A successful run on a well-formed input forces agreement of all coordinates
in this team's claimed row with its true local increments. -/
theorem stage_sound (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (rs : List (ℕ × ℕ)) (xs : List (List Bool))
    (h : Input f pub m rs xs) {es t mt} (r : Runs pub mac stage s m es t mt) :
    ∀ j < f.dim, DiagonalTallyScatter.after f.localBase rs m (f.localBase+j) =
      claimWord f xs f.team j := by
  let localMem := DiagonalTallyScatter.after f.localBase rs m
  let packed := DiagonalTallyBits.outputMemory localMem f.claims xs
  obtain ⟨_,localFit,_,rawFit,claimFit,_,teamFit,_,widthFit⟩ := h.fits
  obtain ⟨_,s₁,r₁,_,loaded⟩ := scatterSetup_runs pub mac m s f h.initialFrame h.fits
  obtain ⟨_,s₂,r₂,_,_,_⟩ := DiagonalTallyScatter.scatter_runs pub mac s₁ m rs loaded
    (by rw [h.recordCount]) localFit.le h.separate h.recordsAt h.coords h.sumsFit
  obtain ⟨_,s₃,r₃,_,p₅₀,p₅₁,p₅₂,p₅₃,p₆₃⟩ := packSetup_runs pub mac localMem s₂ f h.afterLocalFrame h.fits
  obtain ⟨_,s₄,r₄,_,_,_,_⟩ := DiagonalTallyBits.pack_runs pub mac s₃ localMem xs p₅₀ p₅₃
    (p₅₁.trans h.claimCount.symm) p₅₂ p₆₃ widthFit h.wordLengths
    (h.claimCount ▸ rawFit) (by rw [h.claimCount]; omega)
    (h.claimCount ▸ h.packSeparate) h.bitsAt
  obtain ⟨_,s₅,r₅,_,h48,h49,h50,h63⟩ := verifySetup_runs pub mac packed s₄ f h.decodedFrame h.fits
  obtain ⟨_,rt₁⟩ := seq_tail r₁ (by decide) r
  obtain ⟨_,rt₂⟩ := seq_tail r₂ (by decide) rt₁
  obtain ⟨_,rt₃⟩ := seq_tail r₃ (by decide) rt₂
  obtain ⟨_,rt₄⟩ := seq_tail r₄ (by decide) rt₃
  obtain ⟨_,rt₅⟩ := seq_tail r₅ (by decide) rt₄
  cases rt₅ with
  | atom h _ _ => cases h
  | seq check _ =>
    have hIndex := Nat.mul_le_mul_right f.dim (Nat.succ_le_of_lt teamFit)
    rw [Nat.succ_mul] at hIndex
    have sound := verifyRow_sound (pub := pub) (macros := mac) f.dim f.localBase
      (f.claims+f.team*f.dim) s₅ packed localFit (by omega) h48 h49 h50 h63 check
    intro j hj
    have outside : f.localBase+j < f.claims ∨ f.claims+xs.length ≤ f.localBase+j := by
      rw [h.claimCount]
      rcases h.localSeparate with h | h <;> omega
    have left := DiagonalTallyBits.outputMemory_outside localMem f.claims (f.localBase+j) xs outside
    have right := contains_claimWord f xs localMem h.claimCount f.team teamFit j hj
    exact left.symm.trans ((sound j hj).trans (by
      simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using right))

/-- The fixed native table has an accepting choice tape exactly for matching claims. -/
theorem stage_accepts_iff (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (rs : List (ℕ × ℕ)) (xs : List (List Bool))
    (h : Input f pub m rs xs) :
    (∃ bits es, TeamRAM.execute (stage.program.fetch pub mac) ⟨0,s⟩ m bits = some es) ↔
      ∀ j < f.dim, DiagonalTallyScatter.after f.localBase rs m (f.localBase+j) =
        claimWord f xs f.team j := by
  constructor
  · rintro ⟨bits,es,run⟩
    obtain ⟨⟨t,mt,hr⟩,_⟩ := (Code.execute_iff_runs (c := stage) stage_withoutAccept).mp run
    exact stage_sound pub mac s m f rs xs h hr
  · intro hm
    obtain ⟨es,t,run,_,_⟩ := stage_runs pub mac s m f rs xs h hm
    exact ⟨_,_,(stage_execute_iff run _ _).mpr ⟨rfl,rfl⟩⟩

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
