import OAI.Computability.BorderVNP.RoutingISABroadcastCopy
import OAI.Computability.BorderVNP.RoutingISABroadcastCompare

/-! # Complete native common-broadcast test

The branch is read on a physical incident block. Every other incident
block must carry the same prefix. The returned contiguous scratch words
are exactly the bits on the chosen reference block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- All physical incident prefixes equal the reference prefix. -/
def BroadcastFrame.Agrees (f : BroadcastFrame) (mem : ℕ → ℕ) : Prop :=
  ∀ v < f.teams, v ≠ f.team → ∀ j < f.header, mem (f.addr v j) = mem (f.addr f.partner j)

/-- Allowance for setup, the one reference copy, and all incident comparisons. -/
def BroadcastFrame.readTicks (f : BroadcastFrame) : ℕ :=
  headerSetup.slots + ((2+f.header*(copyHeaderBit.slots+1)) +
    (2+f.teams*(6+f.header*(compareHeaderBit.slots+1))))

private theorem copy_agrees_iff {w : ℕ} (f : BroadcastFrame) {base : ℕ}
    (fit : f.Fits w base) (m : ℕ → ℕ) (mt : Memory w)
    (image : readings mt = f.copied m f.header) :
    (∀ v < f.teams, v ≠ f.team → ∀ j < f.header, mt (f.addr v j) = mt (f.dst+j)) ↔ f.Agrees m := by
  have eq (v : ℕ) (hv : v < f.teams) (hd : v ≠ f.team) (j : ℕ) (hj : j < f.header) :
      mt (f.addr v j) = mt (f.dst+j) ↔ m (f.addr v j) = m (f.addr f.partner j) := by
    have before : f.addr v j < f.dst :=
      (f.addr_lt_input fit hv hd (hj.trans_le fit.cap)).trans_le
        (fit.input.trans (by have := fit.frame; omega))
    rw [←Fin.val_inj]
    change readings mt (f.addr v j) = readings mt (f.dst+j) ↔ _
    rw [image, f.copied_before m f.header _ before, f.copied_at m hj]
  exact ⟨fun h v hv hd j hj ↦ (eq v hv hd j hj).mp (h v hv hd j hj),
    fun h v hv hd j hj ↦ (eq v hv hd j hj).mpr (h v hv hd j hj)⟩

/-- On actual Boolean input words, the native broadcast checker returns exactly
when the physical prefixes agree. Its returned scratch memory contains the
reference prefix and preserves all words outside that interval. -/
theorem readBroadcast_test {w : ℕ} (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (bits : f.ReferenceBits (readings m)) :
    TestRun pub macros readBroadcast s m f.readTicks (f.Agrees (readings m))
      (fun z ↦ f.Stable z.reg ∧ z.mem = f.copied (readings m) f.header) := by
  obtain ⟨es,t,first,cost,stable⟩ := headerSetup_run f pub macros s m image fit
  have setup : BoundedRun pub macros headerSetup s m headerSetup.slots
      (fun z ↦ f.Stable z.reg ∧ z.mem = readings m) := ⟨es,t,m,first,cost,stable,rfl⟩
  let P (z : NatState) := f.Stable z.reg ∧ z.mem = f.copied (readings m) f.header
  have compare (u : Bank w) (mu : Memory w) (hp : P (.ofWords u mu)) :
      TestRun pub macros compareHeaders u mu (2+f.teams*(6+f.header*(compareHeaderBit.slots+1)))
        (f.Agrees (readings m)) P := by
    obtain ⟨st,hm⟩ := hp
    change readings mu = f.copied (readings m) f.header at hm
    have img : f.At (readings pub) (readings mu) := hm ▸ f.copied_image fit image _
    have same := copy_agrees_iff f fit (readings m) mu hm
    constructor
    · intro h
      obtain ⟨fs,z,run,cap,kept,_⟩ := compareHeaders_run f img fit st (same.mpr h) (macros := macros)
      exact ⟨fs,z,mu,run,cap,kept,hm⟩
    · intro fs z mz run
      obtain ⟨rfl,st',_,agree⟩ := compareHeaders_sound f img fit st run
      exact ⟨same.mp agree,st',hm⟩
  have tail (u : Bank w) (mu : Memory w) (hp : f.Stable (readings u) ∧ readings mu = readings m) :
      TestRun pub macros (.seq copyHeader compareHeaders) u mu
        ((2+f.header*(copyHeaderBit.slots+1))+(2+f.teams*(6+f.header*(compareHeaderBit.slots+1))))
        (True ∧ f.Agrees (readings m)) P := by
    obtain ⟨st,hm⟩ := hp
    have same : mu = m := funext fun j ↦ Fin.ext (congrFun hm j)
    subst mu
    exact ((copyHeader_run f pub macros u m image fit bits st).asTest (by decide)).seq compare
  exact ((setup.asTest (by decide)).seq tail).mono le_rfl (by simp) (fun _ h ↦ h)

end RoutingISA

end BorderVNP
end Computability
end OAI
