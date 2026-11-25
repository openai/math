import OAI.Computability.BorderVNP.TransmissionPinSlots
import OAI.Computability.BorderVNP.TransmissionPinsIdentity
import OAI.Computability.BorderVNP.TransmissionPinsComplete

/-! # The live and substituted columns in the physical evaluator

The identity branch compares the processor-tape index to the advised column. The
evaluation branch keeps the actual live index in H, while a separate binary guess
supplies I. All inactive substitution slots contain the encoded zero bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Pins

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)

private theorem word_bit_inj {b c : Bool} (hw : 1 < 2^w) (e : TeamTapeInputEmit.word w b.toNat = TeamTapeInputEmit.word w c.toNat) :
    b = c := by
  have hv := congrArg Fin.val e
  simp only [TeamTapeInputEmit.word, Fin.val_ofNat, Nat.mod_eq_of_lt ((Bool.toNat_le b).trans_lt hw),
    Nat.mod_eq_of_lt ((Bool.toNat_le c).trans_lt hw)] at hv
  cases b <;> cases c <;> simp_all

/-- With the actual initialized processor words and advised H* in RAM, the memory
criterion for the identity branch is exactly equality of the two finite bit functions
on team zero. Other teams perform no index comparison. -/
theorem Wiring.identityMatches_iff (u : Fin (R+1)) (pin advised : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) (m : Memory w)
    (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (reference : ∀ i : Fin d, m (starbase+i.val) = TeamTapeInputEmit.word w (advised i).toNat)
    (hw : 1 < 2^w) (room : d ≤ r*(G.program.length+t)) :
    IdentityMatches (G.pinLayout u ibase hbase starbase) m ↔ (u = 0 → pin = advised) := by
  constructor
  · intro matched hu
    subst u
    funext i
    have e := matched rfl i.val i.isLt
    change m (livePinAddress (R+1) (G.program.length+t) link i.val) = m (starbase+i.val) at e
    rw [G.read_liveBit _ pin ext ibase hbase starbase m physical _ (i.isLt.trans_le room),
      reference i] at e
    apply word_bit_inj hw
    simpa [liveBit, i.isLt] using e
  · intro eqIndex hu x hx
    have hu' : u = 0 := Fin.ext hu
    have eq := congrFun (eqIndex hu') (⟨x,hx⟩ : Fin d)
    change m (livePinAddress (R+1) (G.program.length+t) link x) = m (starbase+x)
    rw [G.read_liveBit u pin ext ibase hbase starbase m physical _ (hx.trans_le room),
      reference ⟨x,hx⟩]
    have hx' : x < d := hx
    simpa only [liveBit, hu', ite_true, dite_eq_left hx'] using congrArg (fun b : Bool => TeamTapeInputEmit.word w b.toNat) eq

/-- The returning paths of the actual native identity branch exist precisely when the
live column equals the advised H* on its owner, with the formal width allowed to be zero. -/
theorem Wiring.identityPinIndex_iff (u : Fin (R+1)) (pin advised : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w)
    (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (reference : ∀ i : Fin d, m (starbase+i.val) = TeamTapeInputEmit.word w (advised i).toNat)
    (frame : Frame (G.pinLayout u ibase hbase starbase) (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w)
    (hs : (G.pinLayout u ibase hbase starbase).stride < 2^w)
    (hc : r*(G.program.length+t) < 2^w) (room : d ≤ r*(G.program.length+t))
    (fit : u = 0 → IdentityFits (G.pinLayout u ibase hbase starbase) w) :
    (∃ es z mz, Runs pub macros checkIdentityPins s m es z mz) ↔ (u = 0 → pin = advised) :=
  (checkIdentityPins_iff _ pub macros m s frame hframe (Nat.zero_lt_succ _) hs hc
    (fun hu ↦ fit (Fin.ext hu))).trans
    (G.identityMatches_iff u pin advised ext ibase hbase starbase m physical reference (by omega) room)

/-- Every independently selected column gives an actual native preparation. H receives
the genuine input on every active position, and I receives the chosen bit or a clamped
zero on every physical position. The trace records exactly the real guesses. -/
theorem Wiring.preparePinIndices (u : Fin (R+1)) (pin guess : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w)
    (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (frame : Frame (G.pinLayout u ibase hbase starbase) (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w)
    (hs : (G.pinLayout u ibase hbase starbase).stride < 2^w)
    (hc : r*(G.program.length+t) < 2^w) (room : d ≤ r*(G.program.length+t))
    (fit : LoopFits w (G.pinLayout u ibase hbase starbase))
    (sep : Separated (G.pinLayout u ibase hbase starbase)) :
    ∃ es z mz, Runs pub macros preparePins s m es z mz ∧
      traceCost es ≤ pinSetup.slots + 17*(r*(G.program.length+t)) + 1 ∧
      es.flatMap TeamRAM.Event.choices = (if u=0 then List.ofFn guess else []) ∧
      (∀ x < r*(G.program.length+t), mz (ibase+x) = TeamTapeInputEmit.word w (liveBit u guess x).toNat) ∧
      (u = 0 → ∀ i : Fin d, mz (hbase+i.val) = TeamTapeInputEmit.word w (pin i).toNat) := by
  let L := G.pinLayout u ibase hbase starbase
  let b := liveBit u guess
  obtain ⟨es,z,run,cost,choices,_⟩ := preparePins_run L pub macros m s b frame hframe
    (Nat.zero_lt_succ _) hs hc room fit
  refine ⟨es,z,_,run,cost,?_,?_,?_⟩
  · rw [choices]
    by_cases hu : u = 0
    · subst u
      simp [L,Wiring.pinLayout,b,liveBit]
    · have hv : u.val ≠ 0 := fun he ↦ hu (Fin.ext he)
      simp [L,Wiring.pinLayout,hu,hv]
  · intro x hx
    change preparedMemory L b m L.count (L.ibase+x) = _
    rw [preparedMemory_substitute L b m sep le_rfl hx]
    by_cases ha : L.active x
    · simp [ha,b]
    · have hb : liveBit u guess x = false := by
        by_cases hu : u = 0
        · have hn : ¬ x < d := fun h ↦ ha ⟨congrArg Fin.val hu,h⟩
          simp [liveBit,hu,hn]
        · simp [liveBit,hu]
      simp [ha,hb,TeamTapeInputEmit.word]
  · intro hu i
    have ha : L.active i.val := ⟨congrArg Fin.val hu,i.isLt⟩
    have hi := i.isLt.trans_le room
    change preparedMemory L b m L.count (L.hbase+i.val) = _
    rw [preparedMemory_liveCopy L b m sep le_rfl hi ha]
    change m (livePinAddress (R+1) (G.program.length+t) link i.val) = _
    rw [G.read_liveBit u pin ext ibase hbase starbase m physical i.val hi]
    simp [liveBit,hu,i.isLt]

end TeamContraction

end BorderVNP
end Computability
end OAI
