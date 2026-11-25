import OAI.Computability.BorderVNP.CubeRouteJointPacket
import OAI.Computability.BorderVNP.DiagonalPositiveHeaderSyntax
import OAI.Computability.BorderVNP.DiagonalTallySignedFinish

/-! # The real signed reference packet and copied subtotal header at startup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM DiagonalTallyRAM DiagonalResidueRAM PackedHistoryCircuit
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader Packing

variable {w reserve axes groups cap width : ℕ} (l : Layout)
variable (p : PositiveFields reserve axes groups cap l.cube.teams l.dim width)
variable (pub : Arg → Word w) (raw team : ℕ)

/-- All post-cell reads supplied by the parsed boot image, apart from the packet
lookup tables and count published by subsequent native stages. -/
structure HeaderSeed (mem : Memory w) : Prop where
  /-- Length-only allocator words, including the machine's real word width. -/
  seed : SelectedSeed l.after pub mem raw l.dim l.cube.teams team width
  /-- The true dimension preceding the scalar positions in the cube suffix. -/
  parameters : (mem ((pub 0).val+95)).val=l.p.parameters
  /-- The entire transmitted claim in its native packed-word input format. -/
  subtotal : DiagonalTallyBits.WordsAt mem raw p.tallyWords

/-- Physical addresses read from the original signed header before the tally
evaluation. The second interval contains one RAM word per transmitted bit. -/
def headerSeedRead (frame raw length x : ℕ) : Prop :=
  (∃ i ∈ [33,34,36,38,39,40,44,95,101], x=frame+i) ∨ (raw ≤ x ∧ x<raw+length)

theorem headerSeedRead_below {frame raw length x floor : ℕ} (read : headerSeedRead frame raw length x)
    (frameFit : frame+112 ≤ floor) (rawFit : raw+length ≤ floor) : x<floor := by
  rcases read with ⟨i,hi,rfl⟩ | bounds
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  · omega

theorem headerSeedRead_other {frame raw length x j : ℕ} (read : headerSeedRead frame raw length x)
    (lower : frame+112 ≤ raw) (small : j<112) (away : j ∉ [33,34,36,38,39,40,44,95,101]) : x≠frame+j := by
  rcases read with ⟨i,hi,rfl⟩ | bounds
  · exact fun eq => away (Nat.add_left_cancel eq ▸ hi)
  · omega

/-- The retained original words suffice even on a history with an arbitrary
common claim. The last column has exactly the width in the parsed header. -/
theorem HeaderSeed.transfer {m mt : Memory w} (s : HeaderSeed l p pub raw team m)
    (kept : ∀ x,headerSeedRead (pub 0).val raw (l.cube.teams*l.dim*width) x → mt x=m x) :
    HeaderSeed l p pub raw team mt := by
  have field (i : ℕ) (hi : i ∈ [33,34,36,38,39,40,44,95,101]) :
      mt ((pub 0).val+i)=m ((pub 0).val+i) := kept _ (Or.inl ⟨i,hi,rfl⟩)
  obtain ⟨⟨dim,localAddr⟩,⟨rawAddr,teams,teamID,wid⟩,⟨descriptors,machineWidth⟩⟩ := s.seed
  refine ⟨⟨⟨field 33 (by decide) ▸ dim,field 34 (by decide) ▸ localAddr⟩,
    ⟨field 36 (by decide) ▸ rawAddr,field 38 (by decide) ▸ teams,field 39 (by decide) ▸ teamID,field 40 (by decide) ▸ wid⟩,
    ⟨field 44 (by decide) ▸ descriptors,field 101 (by decide) ▸ machineWidth⟩⟩,field 95 (by decide) ▸ s.parameters,?_⟩
  apply DiagonalTallyBits.words_congr _ _ raw width _ s.subtotal p.tallyWords_width
  intro x lo hi
  exact kept x (Or.inr ⟨lo,p.tallyWords_length ▸ hi⟩)

/-- The actual return of the positive-header boot installs all tally fields
and copies the arbitrary parsed bits from the physical reference blocks. -/
theorem headerSeed_boot {d : ℕ} {L : Pins.Layout} {F : Pins.ProcessorFields L} {f : BroadcastFrame}
    {A : AdviceLayout} {ref : ReferencePacket w d} {state : Bank w} {mem : Memory w}
    (old : Fin 81 → Word w) (D : Directory.Layout) (origin edges cells fresh profile gates outputs geomWidth off ell : ℕ)
    (rawAt : raw=f.dst+1+reserve+Cube.DeclarationBits.length axes groups cap)
    (literal : ref.extension = signedProfileExtension l old D origin edges cells raw team width fresh profile gates outputs geomWidth off ell)
    (boot : BootHeaderState F f A ref pub p.bits state mem)
    (dimFit : l.dim<2^w) (localFit : l.after.localBase<2^w) (rawFit : raw<2^w)
    (teamsFit : l.cube.teams<2^w) (member : team<l.cube.teams) (widthFit : width ≤ w) (wpos : 0<w) :
    HeaderSeed l p pub raw team mem := by
  let previous := fun k => (l.cube.extension old ⟨min (k-31) 80,by omega⟩).val
  have atField (i : Fin 81) (h : i.val+31 ∈ [33,34,35,36,38,39,40,44,45,46,71,80,89,90,95])
      (fit : l.reportFields raw team width previous (31+i.val)<2^w) :
      (mem ((pub 0).val+(31+i.val))).val=l.reportFields raw team width previous (31+i.val) := by
    rw [←Nat.add_assoc,boot.extension,literal]
    exact signedProfileExtension_report l old D origin edges cells raw team width fresh profile gates outputs geomWidth off ell i h fit
  have machine : (mem ((pub 0).val+101)).val=w := by
    change (mem ((pub 0).val+31+(70 : Fin 81).val)).val=w
    rw [boot.extension,literal,signedProfileExtension_geometry]
    exact Nat.mod_eq_of_lt Nat.lt_two_pow_self
  have addr : l.after.descriptors < 2^w := by
    apply lt_of_le_of_lt _ localFit
    unfold DiagonalTallyAllocation.AfterTasks.localBase DiagonalTallyAllocation.AfterTasks.fresh
    omega
  refine ⟨⟨⟨atField 2 (by decide) dimFit,atField 3 (by decide) localFit⟩,
    ⟨atField 5 (by decide) rawFit,atField 7 (by decide) teamsFit,atField 8 (by decide) (member.trans teamsFit),
      atField 9 (by decide) (widthFit.trans_lt Nat.lt_two_pow_self)⟩,⟨atField 13 (by decide) addr,machine⟩⟩,?_,?_⟩
  · exact atField 64 (by decide) ((Nat.le_add_right l.p.parameters l.p.report.gadgets).trans_lt dimFit)
  · exact rawAt ▸ (p.copied wpos boot.header).2.2

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
