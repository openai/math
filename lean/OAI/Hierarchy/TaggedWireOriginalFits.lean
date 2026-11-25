import OAI.Hierarchy.TaggedWireSocketFits
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds
import OAI.Hierarchy.TaggedWireOriginalSocketExpr

namespace OAI
/-! # Range checks on every original signed turn input, including the speculative cases -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe ReportSockets ProtocolRAM Calendar
open Computability.VPVNP.BurstRAM PrivateRAM

variable {w out : ℕ}

private theorem zip_fits (f : Expr→Expr→Expr) (a b : Socket) (ha : a.Fits w out) (hb : b.Fits w out)
    (ok : ∀ x y,x.Fits w out → y.Fits w out → (f x y).Fits w out) : (zipSocket f a b).Fits w out :=
  ⟨ok _ _ ha.positive hb.positive,ok _ _ ha.ordinal hb.ordinal,ok _ _ ha.group hb.group,ok _ _ ha.slot hb.slot⟩

private theorem scaled {x : Expr} (hx : x.Fits w out) (n : ℕ) : (scale n x).Fits w out := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hx,ih⟩

theorem paid_fits (b : CatalogueRows.Board) (core bought : Bool→Socket)
    (c : ∀s,(core s).Fits w out) (p : ∀s,(bought s).Fits w out) (side : Bool) :
    (paidInputs b core bought side).Fits w out :=
  zip_fits b.select _ _ (c side) (p side) (fun x y=>b.select_fits x y)

theorem original_fits (z : Sizes) (start h W k : ℕ) (core : CatalogueRows.CoreSource) (paid : Bool→Socket)
    (raw : ∀s,(paid s).Fits w out) (source : core.All (Expr.Fits w out))
    (wires : z.wires=2^h) (sites : z.signedSites=(siteLast h (2^W) k+1)*(2*k))
    (before : z.ceiling start≤out) (room : z.ceiling start<2^w) (side : Bool) :
    (originalInputs (z.chart start) start z.old (z.ext start) (z.axis start) h W k core paid side).Fits w out := by
  have mb (f : Fin 7) : («meta» start z.old f).Fits w out := by
    refine ⟨bank_fits z ?_ before room,trivial⟩
    have bounded:=Nat.mul_le_mul_right z.old f.isLt
    rw [Nat.succ_mul] at bounded
    dsimp [Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]
    omega
  have publicFit (e : Expr) (he : e.Fits w out) : (publicInput e).Fits w out :=
    ⟨trivial,he,trivial,trivial⟩
  have extent : z.wires≤z.ceiling start := by
    dsimp [Sizes.ceiling,Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext];omega
  have perm : (⟨0,h⟩ : Bank).Fits w out := by
    change 0<2^h ∧ 2^h<2^w ∧ 0+2^h≤out
    rw [←wires]
    exact ⟨by simp [wires],extent.trans_lt room,by simpa using extent.trans before⟩
  have extBank : (RoleROM.bank (z.ext start+side.toNat*2^h) (2^h)).Fits w out := by
    apply bank_fits z _ before room
    rw [←wires]
    dsimp [Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis]
    cases side <;> simp [Bool.toNat] <;> omega
  have exteriorFit (e : Expr) (he : e.Fits w out) : (exterior (z.ext start) h e side).Fits w out := by
    apply publicFit
    refine ⟨extBank,?_⟩
    cases side <;> first | exact he | exact ⟨perm,he⟩
  have axisBank : (RoleROM.bank (z.axis start) ((siteLast h (2^W) k+1)*(2*k))).Fits w out := by
    apply bank_fits z _ before room
    rw [←sites]
    dsimp [Sizes.stop,Sizes.offset,Sizes.positive]
    omega
  have altFit : (altInput (z.axis start) (siteLast h (2^W) k+1) k
      (altSite core («meta» start z.old (if side then 3 else 2)) side) («meta» start z.old 4)).Fits w out := by
    apply publicFit
    refine ⟨axisBank,scaled ?_ _,mb 4⟩
    apply CatalogueRows.fits_atRow _ _ _ (mb _)
    cases side
    · exact source.2.1
    · exact source.2.2.1
  have normal : (normalized (z.chart start) paid side).Fits w out := by
    apply zip_fits _ _ _ (raw false) (raw true)
    intro x y hx hy
    have left := (socket_fits z (paid false) (raw false) before room).1
    have right := (socket_fits z (paid true) (raw true) before room).1
    cases side
    · exact ⟨left,right,hx,hy⟩
    · exact ⟨left,right,hy,hx⟩
  let id := «meta» start z.old 1
  have atId (x : Expr) (hx : x.Fits w out) : (x.atRow id).Fits w out :=
    CatalogueRows.fits_atRow x id hx (mb 1)
  have buy : (mapSocket (fun e=>e.atRow id) (normalized (z.chart start) paid side)).Fits w out :=
    ⟨atId _ normal.positive,atId _ normal.ordinal,atId _ normal.group,atId _ normal.slot⟩
  have branch (t : ℕ) (a b : Socket) (ha : a.Fits w out) (hb : b.Fits w out) :
      (branchSocket («meta» start z.old 0) t a b).Fits w out :=
    zip_fits _ a b ha hb (fun x y hx hy=>⟨mb 0,trivial,hx,hy⟩)
  exact branch 0 _ _ buy (branch 1 _ _ (exteriorFit _ (mb 1))
    (branch 2 _ _ altFit (publicFit _ (mb _))))

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI
