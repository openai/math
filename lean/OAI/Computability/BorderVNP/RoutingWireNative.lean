import OAI.Computability.BorderVNP.RoutingWireChecks

/-! # Native success and soundness at the logical message coordinates

The compiled header, relay and padding instruction fragments return on exactly
their local clauses of the exterior assignment. Their original time bounds
and final memory properties are retained.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
  {u : Fin (R+1)} (A : TransferBank G pin ext L.width w L.header u)

/-- Native header-copy and comparison on an actual processor input, at its proved
clock, return exactly when the incident messages have one common broadcast. -/
theorem TransferBank.native_broadcast (hw : 0 < w) (macros : TeamOpcode.Macros w 8) (s : Bank w) :
    let f := G.transferFrame u L.header A.dst
    TestRun A.pub macros readBroadcast s A.mem f.readTicks
      (∀ b c : Block (R+1), Incident u b → Incident u c →
        (L.exteriorEquiv ext).broadcast b = (L.exteriorEquiv ext).broadcast c)
      (fun z => f.Stable z.reg ∧ z.mem = f.copied (readings A.mem) f.header) := by
  intro f
  have hp := f.partner_spec L.three
  let v : Fin (R+1) := ⟨f.partner,hp.2⟩
  have hd : u ≠ v := fun he => hp.1 (congrArg Fin.val he.symm)
  have bits : f.ReferenceBits (readings A.mem) := by
    intro j hj
    exact (G.read_message_header L u v hd pin ext A.ibase A.hbase A.starbase A.mem A.physical
      hw ⟨j,hj⟩).trans_lt (Bool.toNat_lt _)
  exact (readBroadcast_test f A.pub macros s A.mem A.schedule.frame A.schedule.fit bits).mono
    le_rfl (A.broadcast_iff hw) (fun _ h => h)

/-- Native scan over all incident padding positions. Every return validates the typed
padding bits, and zero padding supplies a returning run within the same cost. -/
theorem TransferBank.native_padding (hw : 0 < w) (macros : TeamOpcode.Macros w 8) (s : Bank w) :
    let f := G.transferFrame u L.header A.dst
    NativeLinkCheck A.pub macros checkPadding s A.mem
      (f.linkCheckTicks (headerSetup.slots+(readFrame 19 62 63 18).slots+1) paddingStartBlock.slots)
      (∀ (v : Fin (R+1)) (hd : u ≠ v) (i : Fin (L.slack (blockOf u v hd))),
        (L.exteriorEquiv ext).padding ⟨blockOf u v hd,i⟩ = false) := by
  intro f
  have h := checkPadding_schedule f A.pub macros s A.mem A.schedule.frame A.schedule.fit L.width
    A.schedule.table A.schedule.pair A.schedule.capacity
  constructor
  · intro good
    exact h.complete (fun v hv => ((A.padding_iff hw v (fun h => hv (congrArg Fin.val h.symm)))).mpr (good v _))
  · intro es q m run
    obtain ⟨hm,pass⟩ := h.sound run
    exact ⟨hm, fun v hd => (A.padding_iff hw v hd).mp (pass v (fun eq => hd (Fin.ext eq.symm)))⟩

/-- On an initialized public scheduling table the actual relay code tests the two
copies of every oriented message bit. The frame bounds apply at the real RAM word width. -/
theorem TransferBank.native_relays (hw : 0 < w) (macros : TeamOpcode.Macros w 8) (s : Bank w)
    (l : TableLayout) (row : ℕ → TableRow) (hcount : l.teams = R+1)
    (hwidth : L.width = fun a b => l.widthMatrix row (Fin.cast hcount.symm a) (Fin.cast hcount.symm b))
    (al : l.Allocated w) (fit : l.RowsFit w row) (base : (A.pub 0).val = l.frame)
    (fields : l.frameFields (readings A.mem))
    (widths : ∀ i < l.teams^2, readings A.mem (l.widths+i) = l.pairWidth row l.count i)
    (space : RelayRooms w l.teams (fun x y => l.partnerLength row x u.val y)
      (readings A.pub) (readings A.mem) u.val) :
    let len := fun x y => l.partnerLength row x u.val y
    TestRun A.pub macros checkRelays s A.mem (relayCheckCost l.teams len)
      (∀ (x : Fin (R+1)) (p : Hop L.three L.width x u),
        (L.exteriorEquiv ext).hop x u p = (L.exteriorEquiv ext).hop p.1 u (otherHop L.three L.width p))
      (RelayState l (readings A.mem) u.val l.teams) := by
  intro len
  obtain ⟨frame,teams,count,records,widthsBase,offsets,used,ordinals⟩ := l
  change teams = R+1 at hcount
  subst teams
  let l : TableLayout := ⟨frame,R+1,count,records,widthsBase,offsets,used,ordinals⟩
  have hmat : L.width = l.widthMatrix row := hwidth
  have chk := checkRelays_test A.pub macros al row s A.mem fit base fields A.schedule.frame.1 u.isLt widths space
  apply chk.mono le_rfl _ (fun _ h => h)
  refine (relayChecks_iff_hops l row L.three u (readings A.pub) (readings A.mem)).trans ?_
  rw [← hmat]
  exact forall_congr' fun x => forall_congr' fun p => A.relay_hop_iff hw p

end TeamContraction

end BorderVNP
end Computability
end OAI
