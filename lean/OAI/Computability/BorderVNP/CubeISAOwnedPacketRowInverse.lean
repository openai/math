import OAI.Computability.BorderVNP.CubeISAOwnedPacketTape
import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay

/-! # Inverting every returning native packet row into physical bit assignments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.PacketRowData

open RoutingISA RoutingISA.Owned Physical Physical.Owned VPVNP.BurstRAM DiagonalResidueRAM Tally

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s)

private theorem program_native (ms : List Mode) : (program ms).nativeOnly = true := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    exact Bool.and_eq_true_iff.mpr ⟨by cases m <;> decide,ih⟩

/-- The complete packet scan and its dispatch table contain only native instructions. -/
theorem loop_nativeOnly (n b h K s : ℕ) :
    (rowLoop (packetCandidate n) (ownedPacket n b h K s)).nativeOnly = true := by
  have prepare := (packetCandidate n).nativeOnly_of_unsigned (packetCandidate_frame n).1
  have first : (ownedPrefix n K h).nativeOnly = true := by
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨by decide,program_native _⟩,decodeOwner.nativeOnly_of_unsigned (by decide)⟩
  have tail : (scatterPacket n b h K s).nativeOnly = true := dispatch_nativeOnly _ (fun _ _ _ => program_native _)
  simp only [rowLoop,ownedPacket,Code.nativeOnly,prepare,first,tail,Bool.and_self]

/-- All fetched PCs in the complete native packet row carry the native opcode tag. -/
theorem native_tags (n b h K s : ℕ) :
    ∀ pc, (rowLoop (packetCandidate n) (ownedPacket n b h K s)).program.tag pc = .native :=
  Code.program_tag_native _ (loop_nativeOnly n b h K s)

/-- Every actual native return of this entire row recovers physical private assignments, with
the complete trace, sign, cost and final memory of that realization. All original crossing and
non-owned data agree. Two returns on the same chronological word agree in their full state. -/
theorem recover (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r₀ : Bank w) (m₀ : Memory w) (entry : D.Entry r₀ m₀)
    (prepared : D.PreparedRow src m₀) (positive : 0 < D.stride) (width : selectorWidth n K h ≤ D.stride)
    (allocation : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ 2^w)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    {es t mt} (run : Runs pub mac (rowLoop (packetCandidate n) (ownedPacket n b h K s)) r₀ m₀ es t mt) :
    ∃ x z, D.KeepsExterior x z ∧
      (∀ p, (D.body p).map Position.routed = ((D.withWords x z).body p).map Position.routed) ∧
      TraceOK es (rowChoices packetTrialValid (D.withWords x z).choices) es.length ∧
      traceCost es ≤ (∑ t : Fin (packetTrials n d blocks), (6*n+22 + if packetTrialValid t then ownedPacketCost n b h K s else 1))+1 ∧
      (D.withWords x z).At r₀ m₀ (packetTrials n d blocks) t mt := by
  let bs := es.flatMap TeamRAM.Event.choices
  obtain ⟨x,z,outside,routed,tape⟩ := D.realize_tape (ChoiceTape.extend bs)
  let E := D.withWords x z
  have start : E.Entry r₀ m₀ := ⟨entry.scan,entry.group,entry.axis,entry.dim,entry.width,entry.count,
    entry.selector,entry.crossing⟩
  obtain ⟨fs,y,my,canon,tr,cost,state⟩ := E.scatterRow_run pub mac src r₀ m₀ start
    (D.prepared_withWords m₀ prepared x z routed) positive width allocation fit
  obtain ⟨a,a',compat⟩ := ChoiceTape.compatible bs (ChoiceTape.offset D.privateWidth (packetTrials n d blocks))
  have agree := (congrArg (· ++ a) (tr.2.1.trans tape)).trans compat
  obtain ⟨rfl,rfl,rfl⟩ := unique_returns (native_tags n b h K s) canon run agree
  exact ⟨x,z,outside,routed,tr,cost,state⟩

/-- Equal chronological private choices on two actual returns yield the same whole row path. -/
theorem unique {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r m es t mt fs y my}
    (first : Runs pub mac (rowLoop (packetCandidate n) (ownedPacket n b h K s)) r m es t mt)
    (second : Runs pub mac (rowLoop (packetCandidate n) (ownedPacket n b h K s)) r m fs y my)
    (eqn : es.flatMap TeamRAM.Event.choices = fs.flatMap TeamRAM.Event.choices) :
    es = fs ∧ t = y ∧ mt = my :=
  unique_returns (native_tags n b h K s) first second (tail := []) (tail' := []) (by simpa using eqn)

end Cube.Scatter.PacketRowData

end BorderVNP
end Computability
end OAI
