import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceHeader
import OAI.Computability.BorderVNP.TransmissionJointInstall

/-! # The actual all-batch boot supplies the finite team's broadcast snapshot

The joint literal image can carry the field-valued machine prefix. Its serialized
stripe is read from the original physical processor tapes, including at batch size
one. Both boot stages preserve the input region and scalar frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction ProcessorSlots RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open FiniteBoot GeometryAdvice

/-- The ordinary scalar boot followed by the wide finite-field advice loader. -/
def wideStartup : Code := .seq bootFrame FiniteBoot.installFrame

/-- Charged tick allowance for the deterministic wide startup on a given advice count. -/
def wideStartupBudget (w count : ℕ) : ℕ :=
  126 + (FiniteBoot.setup.slots+count*(copyStripeBit.slots+1)+1 +
    (ExtendedFrame.setup.slots+8*81*(w+1)+8))

variable {R r t d link inner n w : ℕ} {Edge : Type}

/-- Every actual jointly installed packet yields the post-startup snapshot for
the common-tag theorem and the pin frame for the unit and evaluation branches. -/
theorem wideBootSnapshot_fields (G : Wiring R r t d link inner n Edge) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase header dst : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w)
    (a : AdviceLayout) (pre : List (Word w)) (extension : Fin 81 → Word w)
    (D : Packing.Directory.Layout) (start tail : ℕ) (geom : Stripe) (geomBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) :
    let L := G.pinLayout u ibase hbase starbase
    let f := G.transferFrame u header dst
    let fields := G.processorFields u pin ext ibase hbase starbase
    let stripe := bootStripe a f (pre.length+81)
    PacketFrame L f a pre.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val →
    a.count = (pre.length+81)*w → a.offset+width a.count f.processors ≤ f.literal →
    ExtendedFrame.Fits w (pub 0).val a.dst pre.length →
    JointImage D start tail stripe geom (serialized (pre ++ List.ofFn extension)) geomBits strings u.val fields →
    ∃ b : BootSnapshot G u pin ext ibase hbase starbase header dst wideStartup pub mac bank,
      PacketFrame L f a pre.length w (readings pub) (readings b.mem) ∧
      (∀ i : Fin 81, b.mem ((pub 0).val+31+i.val) = extension i) ∧
      (∀ i : Fin 31, b.mem ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
      traceCost b.events ≤ wideStartupBudget w a.count := by
  intro L f fields stripe scalar fit count room space joint
  let initial := processorMemory fields w
  let mb := bootMemory pub initial 31
  obtain ⟨bs,b,boot,bc⟩ := bootFrame_run pub mac bank initial (by have := space.frameBound; omega)
  have bootFields : PacketFrame L f a pre.length w (readings pub) (readings mb) :=
    scalar.congr (boot_field pub initial)
  have inputRoom : fields.header.length ≤ (pub 0).val := by
    rw [fields.header_length,scalar.input_extent]
    exact fit.input
  have bootInput : fields.ContainsInput mb := (fields.containsInput_initial w).boot pub 31 inputRoom
  have cap : (serialized (pre ++ List.ofFn extension)).length ≤ L.processors*stripe.width := by
    simp only [serialized_length,List.length_append,List.length_ofFn]
    change (pre.length+81)*w ≤ f.processors*width a.count f.processors
    rw [← count]
    exact capacity a.count f.processors fit.procs
  have same := joint.stripe_install_eq true stripe _ (by simp) (Nat.zero_lt_succ _) cap
  have loaded : (stripe.install fields (serialized (pre++List.ofFn extension))).ContainsInput mb := by rw [same]; exact bootInput
  obtain ⟨fs,z,wide,ct,_⟩ := initialize_run a f pub mac b mb pre extension fields bootFields.broadcast
    bootFields.pins bootFields.advice fit bootFields.extension count room space loaded
  let dest := stripe.image f.stride mb a.count
  let mt := ExtendedFrame.installed dest (pub 0).val extension
  have below (j : ℕ) (hj : j < (pub 0).val+31) : mt j = mb j := by
    apply (ExtendedFrame.installed_outside dest (pub 0).val extension j (.inl hj)).trans
    exact stripe.image_outside mb (.inl (by change j < a.dst; have := space.separate; omega))
  have keep : fields.ContainsInput mt := fun j hj =>
    (below _ (by have := hj.trans_le inputRoom; omega)).trans (bootInput j hj)
  have post : PacketFrame L f a pre.length w (readings pub) (readings mt) :=
    bootFields.congr fun i hi => by
      change (mt ((pub 0).val+i)).val = (mb ((pub 0).val+i)).val
      exact congrArg Fin.val (below _ (by omega))
  let snap : BootSnapshot G u pin ext ibase hbase starbase header dst wideStartup pub mac bank :=
    ⟨bs++fs,z,mt,boot.seq wide,keep,post.broadcast,fit⟩
  refine ⟨snap,post,fun i => ExtendedFrame.installed_at ..,fun i => ?_,?_⟩
  · exact (below _ (by have := i.isLt; omega)).trans (by
      simp only [mb,bootMemory,Nat.le_add_right,Nat.add_sub_cancel_left,i.isLt,and_self,dite_true]
      apply congrArg pub; apply Fin.ext
      exact (Nat.mod_eq_of_lt (by have := i.isLt; omega : i.val+1 < 32)).symm)
  · change traceCost (bs++fs) ≤ 126+_
    exact (Transmission.cost_append bs fs).trans_le (Nat.add_le_add bc.le ct)

/-- Every actual jointly installed packet yields the post-startup snapshot for
the common-tag theorem and the pin frame for the unit and evaluation branches. -/
theorem wideBootSnapshot (G : Wiring R r t d link inner n Edge) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase header dst : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w)
    (a : AdviceLayout) (pre : List (Word w)) (extension : Fin 81 → Word w)
    (D : Packing.Directory.Layout) (start tail : ℕ) (geom : Stripe) (geomBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) :
    let L := G.pinLayout u ibase hbase starbase
    let f := G.transferFrame u header dst
    let fields := G.processorFields u pin ext ibase hbase starbase
    let stripe := bootStripe a f (pre.length+81)
    PacketFrame L f a pre.length w (fun _ => 0) (operand pub) →
    f.Fits w (pub 0).val →
    a.count = (pre.length+81)*w → a.offset+width a.count f.processors ≤ f.literal →
    ExtendedFrame.Fits w (pub 0).val a.dst pre.length →
    JointImage D start tail stripe geom (serialized (pre ++ List.ofFn extension)) geomBits strings u.val fields →
    ∃ b : BootSnapshot G u pin ext ibase hbase starbase header dst wideStartup pub mac bank,
      Frame L (readings pub) (readings b.mem) ∧ traceCost b.events ≤ wideStartupBudget w a.count := by
  intro L f fields stripe scalar fit count room space joint
  obtain ⟨b,frame,_,_,time⟩ := wideBootSnapshot_fields G u pin ext ibase hbase starbase header dst
    pub mac bank a pre extension D start tail geom geomBits strings scalar fit count room space joint
  exact ⟨b,frame.pins,time⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
