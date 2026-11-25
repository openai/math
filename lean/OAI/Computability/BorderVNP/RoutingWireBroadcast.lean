import OAI.Computability.BorderVNP.RoutingWireReads
import OAI.Computability.BorderVNP.TransmissionAcross
import OAI.Computability.BorderVNP.RoutingISABroadcastProof

/-! # Equivalence of the physical broadcast comparison and the message check -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA

private theorem incident_block {R : ℕ} (u v : Fin (R+1)) (h : u ≠ v) :
    Incident u (blockOf u v h) := by unfold blockOf; split <;> simp [Incident]

private theorem exists_partner {R : ℕ} {u : Fin (R+1)} {b : Block (R+1)} (hu : Incident u b) :
    ∃ (v : Fin (R+1)) (h : u ≠ v), blockOf u v h = b := by
  obtain ⟨⟨x,y⟩,hxy⟩ := b
  rcases hu with rfl | rfl
  · exact ⟨y,hxy.ne,by simp [blockOf,hxy]⟩
  · exact ⟨x,hxy.ne.symm,by simp [blockOf,not_lt_of_gt hxy]⟩

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- The concrete header check in one team compares precisely the broadcasts
of its incident blocks. The reference partner is the one selected by the native code. -/
theorem TransferBank.broadcast_iff (hw : 0 < w) {u : Fin (R+1)}
    (A : TransferBank G pin ext L.width w L.header u) :
    (G.transferFrame u L.header A.dst).Agrees (readings A.mem) ↔
      ∀ b c : Block (R+1), Incident u b → Incident u c →
        (L.exteriorEquiv ext).broadcast b = (L.exteriorEquiv ext).broadcast c := by
  let f := G.transferFrame u L.header A.dst
  have hv := f.partner_spec L.three
  let partner : Fin (R+1) := ⟨f.partner,hv.2⟩
  have hp : u ≠ partner := fun h => hv.1 (congrArg Fin.val h.symm)
  have read (v : Fin (R+1)) (h : u ≠ v) (i : Fin L.header) :
      readings A.mem (f.addr v i) = ((L.exteriorEquiv ext).broadcast (blockOf u v h) i).toNat :=
    G.read_message_header L u v h pin ext A.ibase A.hbase A.starbase A.mem A.physical hw i
  constructor
  · intro h b c hb hc
    obtain ⟨v,hd,rfl⟩ := exists_partner hb
    obtain ⟨z,he,rfl⟩ := exists_partner hc
    funext i
    have hr (v : Fin (R+1)) (hd : u ≠ v) :
        ((L.exteriorEquiv ext).broadcast (blockOf u v hd) i).toNat =
          ((L.exteriorEquiv ext).broadcast (blockOf u partner hp) i).toNat :=
      (read v hd i).symm.trans ((h v v.isLt (fun he => hd (Fin.ext he.symm)) i i.isLt).trans (read partner hp i))
    have hx := (hr v hd).trans (hr z he).symm
    have inject : Function.Injective Bool.toNat := by decide
    exact inject hx
  · intro h v hv hd j hj
    let z : Fin (R+1) := ⟨v,hv⟩
    have hz : u ≠ z := fun he => hd (congrArg Fin.val he.symm)
    let i : Fin L.header := ⟨j,hj⟩
    have he := congrFun (h _ _ (incident_block u z hz) (incident_block u partner hp)) i
    exact (read z hz i).trans ((congrArg Bool.toNat he).trans (read partner hp i).symm)

/-- Running the physical header comparison at all teams is precisely the common
broadcast condition of the global message check. -/
theorem transfer_broadcasts_iff (hw : 0 < w)
    (A : ∀ u, TransferBank G pin ext L.width w L.header u) :
    (∀ u, (G.transferFrame u L.header (A u).dst).Agrees (readings (A u).mem)) ↔
      LocalBroadcast (L.exteriorEquiv ext).broadcast :=
  forall_congr' (fun u => (A u).broadcast_iff hw)

end TeamContraction

end BorderVNP
end Computability
end OAI
