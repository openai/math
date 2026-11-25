import OAI.Computability.BorderVNP.DiagonalNativeSelection
import OAI.Computability.BorderVNP.RoutingISABroadcastProof

/-! # Actual broadcast dispatch on the unit branch

The branch bit is read from the reference incident block and copied into scratch.
Both the exterior zero test and the live-column comparison refer to the original
physical input. The only array which may be after the copy is the advised column.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM Pins
variable {w : ℕ}

private theorem copied_pinFrame (f : BroadcastFrame) (L : Layout) {pub : Arg → ℕ} {m : ℕ → ℕ}
    (fit : f.Fits w (pub 0)) (p : Frame L pub m) : Frame L pub (f.copied m f.header) := by
  have before (j : ℕ) (hj : j ≤ 24) : frameField pub (f.copied m f.header) j = frameField pub m j :=
    f.copied_before m _ _ (by have := fit.frame; omega)
  exact ⟨(before _ (by decide)).trans p.team,(before _ (by decide)).trans p.teams,
    (before _ (by decide)).trans p.processors,(before _ (by decide)).trans p.literal,
    (before _ (by decide)).trans p.link,(before _ (by decide)).trans p.ibase,
    (before _ (by decide)).trans p.hbase,(before _ (by decide)).trans p.width,
    (before _ (by decide)).trans p.starbase⟩

private theorem copied_unit_iff (f : BroadcastFrame) (L : Layout) {base : ℕ} (fit : f.Fits w base)
    (m mu : Memory w) (copied : readings mu = f.copied (readings m) f.header)
    (live : L.processors*L.stride ≤ f.dst) (room : L.width ≤ L.count)
    (apart : L.starbase+L.width ≤ f.dst ∨ f.dst+f.header ≤ L.starbase) :
    UnitTest f L mu ↔ UnitTest f L m := by
  have atAddr (v : ℕ) (hv : v < f.teams) (hd : v ≠ f.team) (j : ℕ) (hj : j < f.capacity) :
      readings mu (f.addr v j) = readings m (f.addr v j) := by
    rw [copied]
    exact f.copied_before _ _ _ ((f.addr_lt_input fit hv hd hj).trans_le (fit.input.trans
      (by have := fit.frame; omega)))
  have match_iff (i : ℕ) (hi : i < L.width) : pinMatch L mu i ↔ pinMatch L m i := by
    unfold pinMatch
    rw [←Fin.val_inj,←Fin.val_inj]
    change (readings mu _ = readings mu _) ↔ (readings m _ = readings m _)
    rw [copied, f.copied_before _ _ _ ((livePinAddress_lt L (hi.trans_le room)).trans_le live)]
    have preserved : f.copied (readings m) f.header (L.starbase+i) = readings m (L.starbase+i) := by
      unfold BroadcastFrame.copied
      split_ifs with h <;> first | rfl | omega
    rw [preserved]
  exact and_congr (forall_congr' fun v => forall_congr' fun hv => forall_congr' fun hd =>
    forall_congr' fun j => forall_congr' fun _ => forall_congr' fun hj => by rw [atAddr v hv hd j hj])
    (forall_congr' fun _ => forall_congr' fun i => forall_congr' fun hi => match_iff i hi)

private theorem agrees_of_unit (f : BroadcastFrame) {w base} (fit : f.Fits w base) {L : Layout} {m : Memory w}
    (yes : UnitTest f L m) : f.Agrees (readings m) := by
  intro v hv hd j hj
  have partner := f.partner_spec fit.three
  rw [yes.1 _ hv hd j (Nat.zero_le _) (hj.trans_le fit.cap),
    yes.1 _ partner.2 partner.1 j (Nat.zero_le _) (hj.trans_le fit.cap)]

/-- On the physical reference tag zero, the broadcast and full selector accept precisely
the original all-zero incident blocks and the original distinguished column. Both
tests use the actual input bank, and the only memory effect is the public header copy. -/
theorem broadcast_unit (f : BroadcastFrame) (L : Layout) (eval : Code)
    (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (bits : f.ReferenceBits (readings m)) (zero : readings m (f.addr f.partner 0) = 0)
    (frame : Frame L (readings pub) (readings m)) (hs : L.stride < 2^w) (hc : L.count < 2^w)
    (room : L.width ≤ L.count) (apart : L.starbase+L.width ≤ f.dst ∨ f.dst+f.header ≤ L.starbase)
    (pins : L.team = 0 → IdentityFits L w) :
    TestRun pub macros (.seq readBroadcast (select eval)) s m (f.readTicks+(2+unitBudget f L))
      (UnitTest f L m) (fun z => z.mem = f.copied (readings m) f.header) := by
  have ht : 0 < L.teams := by
    have e := frame.teams.symm.trans image.2.1
    rw [e]; exact (by have := fit.three; omega)
  have live : L.processors*L.stride ≤ f.dst := by
    have np := frame.processors.symm.trans image.2.2.1
    have nl := frame.literal.symm.trans image.2.2.2.1
    have nt := frame.teams.symm.trans image.2.1
    have nk := frame.link.symm.trans image.2.2.2.2.1
    have stride : L.stride = f.stride := by simp [Layout.stride,Layout.offset,BroadcastFrame.stride,nl,nt,nk]; omega
    rw [np,stride]
    exact fit.input.trans (by have := fit.frame; omega)
  have hf : readings pub 0 + 24 < 2^w := by have h := fit.frame; have ho := fit.out; change (pub 0).val + 24 < _; omega
  have bcast := readBroadcast_test f pub macros s m image fit bits
  have stage (t : Bank w) (mu : Memory w)
      (post : f.Stable (readings t) ∧ readings mu = f.copied (readings m) f.header) :
      TestRun pub macros (select eval) t mu (2+unitBudget f L) (UnitTest f L m)
        (fun z => z.mem = f.copied (readings m) f.header) := by
    have at0 : (mu f.dst).val = 0 := by
      change readings mu f.dst = _
      rw [post.2,←Nat.add_zero f.dst,f.copied_at _ fit.branch,zero]
    have check := unit_check f L pub macros (Function.update t 10 (mu f.dst)) mu
      (post.2 ▸ f.copied_image fit image _) fit (post.2 ▸ copied_pinFrame f L fit frame) hf ht hs hc pins
    have selected := select_zero_check f eval pub macros t mu post.1 at0 check
    have same := copied_unit_iff f L fit m mu post.2 live room apart
    constructor
    · intro yes
      obtain ⟨fs,z,r,cap⟩ := selected.complete (same.mpr yes)
      exact ⟨fs,z,mu,r,cap,post.2⟩
    · intro fs z mz r
      obtain ⟨rfl,test⟩ := selected.sound r
      exact ⟨same.mp test,post.2⟩
  have full := bcast.seq stage
  exact ⟨fun yes => full.complete ⟨agrees_of_unit f fit yes,yes⟩,
    fun r => ⟨(full.sound r).1.2,(full.sound r).2⟩⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
