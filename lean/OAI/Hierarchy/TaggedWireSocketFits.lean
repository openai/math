import OAI.Hierarchy.TaggedWireRoleChart

namespace OAI
/-! # Physical range checks for the terminal role-field scans -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open ProtocolRAM ReportSockets
open Computability.VPVNP.BurstRAM PrivateRAM

/-- All four row expressions of one native socket can use the same input range. -/
structure Socket.Fits (v : Socket) (w out : ℕ) : Prop where
  positive : v.positive.Fits w out
  ordinal : v.ordinal.Fits w out
  group : v.group.Fits w out
  slot : v.slot.Fits w out

namespace RoleRoom
variable {w start out : ℕ} (z : Sizes)

theorem bank_fits {base n : ℕ} (bankEnd : base+n≤z.stop start)
    (below : z.ceiling start≤out) (room : z.ceiling start<2^w) :
    (RoleROM.bank base n).Fits w out := by
  have cap := z.rounded_fits start bankEnd
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (cap.trans_lt room),cap.trans below⟩

/-- Every speculative rounded table lookup fits, including both arms of a
conditional whose row might represent a dormant purchased slot. -/
theorem socket_fits (v : Socket) (args : v.Fits w out)
    (below : z.ceiling start≤out) (room : z.ceiling start<2^w) :
    (socketSite (z.chart start) v).Fits w out ∧ (socketCode (z.chart start) v).Fits w out := by
  have pub : (RoleROM.bank (z.pub start) z.publicRows).Fits w out := by
    apply bank_fits z _ below room
    dsimp [Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free]
    omega
  have site : (RoleROM.bank (z.pub start+z.publicRows) z.publicRows).Fits w out := by
    apply bank_fits z _ below room
    dsimp [Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free]
    omega
  have codes : (RoleROM.bank (z.positive start) (z.groups*z.slots)).Fits w out := by
    apply bank_fits z _ below room
    dsimp [Sizes.stop,Sizes.offset]
    omega
  have offsets : (SiteROM.offsets (z.offset start) z.groups).Fits w out := by
    apply bank_fits z (base:=z.offset start) (n:=z.groups) _ below room
    dsimp [Sizes.stop]
    omega
  have targets : (SiteROM.sites (z.offset start) z.groups z.slots).Fits w out := by
    apply bank_fits z (base:=z.offset start+z.groups) (n:=z.groups*z.slots) _ below room
    dsimp [Sizes.stop]
    omega
  exact ⟨⟨args.positive,trivial,⟨site,args.ordinal⟩,⟨targets,⟨offsets,args.group⟩,args.slot⟩⟩,
    ⟨args.positive,trivial,⟨pub,args.ordinal⟩,⟨codes,⟨offsets,args.group⟩,args.slot⟩⟩⟩

theorem field_fits (v : Bool→Socket) (args : ∀s,(v s).Fits w out)
    (below : z.ceiling start≤out) (room : z.ceiling start<2^w) (reported : Bool) (j : Fin 4) :
    (field (z.chart start) v reported j).Fits w out := by
  have l := socket_fits z (v false) (args false) below room
  have r := socket_fits z (v true) (args true) below room
  have chooseFit (b : Bool) (a c : Expr) (ha : a.Fits w out) (hc : c.Fits w out) :
      (sortedRead (socketSite (z.chart start) (v false)) (socketSite (z.chart start) (v true)) b a c).Fits w out := by
    cases b
    · exact ⟨l.1,r.1,ha,hc⟩
    · exact ⟨l.1,r.1,hc,ha⟩
  have tagFit (a : Expr) (fit : a.Fits w out) : (tagged reported a).Fits w out := ⟨⟨fit,fit⟩,trivial⟩
  fin_cases j
  · exact chooseFit false _ _ l.1 r.1
  · exact chooseFit true _ _ l.1 r.1
  · exact tagFit _ (chooseFit false _ _ l.2 r.2)
  · exact tagFit _ (chooseFit true _ _ l.2 r.2)

end RoleRoom
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
