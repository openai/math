import OAI.Hierarchy.TaggedWirePacketOpcode
import OAI.Hierarchy.TaggedWideSiteReplay

namespace OAI
/-! # The packet's published, site-local fields on the common candidate scatter -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ChosenPackets.RowRouting TurnShelf
open scoped Classical Fin.CommRing
variable {n S m t W L count : ℕ}

namespace Operands
variable {len : Fin n→ℕ} (o : Operands len) (ord : Fin t≃Σi,Fin (len i))

def column (encode : Fin n→ℕ→Fin 7→Expr) (party : Expr) (code : Fin ((n*3)*5)) : Expr :=
  let z : Fin (n*3)×Fin 5:=finProdFinEquiv.symm code
  let ij : Fin n×Fin 3:=finProdFinEquiv.symm z.1
  if ij.2.val<len ij.1+1 then .branch .eq (o.width ij.1) (.lit 0) (.lit 0)
    (.branch .eq (o.site ij.1 ij.2.val) party (encode ij.1 ij.2.val (z.2.castLE (by decide))) (.lit 0))
  else .lit 0

def field (party : Expr) := o.column (o.words ord) party

def siteFields (party : Fin L→Expr) : Fin L→Fin ((n*3)*5)→Expr := fun s=>o.field ord (party s)
end Operands

variable (old : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m))
    (bits : Fin n→ℕ) (ord : Fin t≃Σi,Fin (route i).length) (short : ∀i,(route i).length≤2)
    (turns : Fin count≃Positions route) (o : Operands fun i=>(route i).length) (mem : Memory W)
    (row : Word W)
local notation "before" => fun (i : Fin n) (b : Bool)=>(halfCode i b).val
local notation "after" => PostCode.after (NativeSlot.edge route ord) n
local notation "cols" => fields old edge route bits ord before after short turns
local notation "putAt" => put old edge route bits ord before after short turns

/-- Read a single real header with exactly the ordinal used by the
global scatter. The same physical word is zero on all other participants. -/
theorem column_eval (encode : Fin n→ℕ→Fin 7→Expr) (numbers : Fin count→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live numbers ↪ Fin S×Fin (n*3))
    (position : ∀u,put u=(vertex old edge route (turns u.val),StripPaths.positionSeat route short (turns u.val)))
    (width : ∀r,numbers r 4=bits (turns r).1)
    (values : ∀r f,(encode (turns r).1 (turns r).2.val f).eval mem row=(numbers r f : Word W))
    (party : Expr) (s : Fin S) (real : party.eval mem row=(s.val : Word W))
    (reads : Reads old edge route bits o mem row) (sites : S≤2^W)
    (wide : ∀i,bits i<2^W) (slot : Fin (n*3)) (f : Fin 5) :
    (o.column encode party (finProdFinEquiv (slot,f))).eval mem row=
      ProtocolRAMTurnShelf.entry numbers put f (s,slot) := by
  let ij : Fin n×Fin 3:=finProdFinEquiv.symm slot
  have rep : finProdFinEquiv ij=slot :=finProdFinEquiv.apply_symm_apply _
  have decode (u : ProtocolRAMTurnShelf.Live numbers) (atSlot : (put u).2=slot) :
      ij.1=(turns u.val).1 ∧ ij.2.val=(turns u.val).2.val := by
    rw [position u] at atSlot
    have eq:=congrArg finProdFinEquiv.symm atSlot
    change finProdFinEquiv.symm (StripPaths.positionSeat route short (turns u.val))=ij at eq
    rcases hh:turns u.val with ⟨i,j⟩
    rw [hh,StripPaths.positionSeat_decode] at eq
    exact ⟨congrArg Prod.fst eq.symm,congrArg (fun z : Fin n×Fin 3=>z.2.val) eq.symm⟩
  simp only [Operands.column,Equiv.symm_apply_apply]
  change (if ij.2.val<(route ij.1).length+1 then _ else _ : Expr).eval mem row=_
  by_cases h : ij.2.val<(route ij.1).length+1
  · rw [ite_eq_left h,PacketScan.eq_select mem row _ _ _ _ (reads.width ij.1) rfl
      (wide _) (Nat.two_pow_pos W)]
    let a : Positions route:=⟨ij.1,⟨ij.2.val,h⟩⟩
    let ix:=turns.symm a
    have back : turns ix=a := turns.apply_symm_apply a
    by_cases zero : bits ij.1=0
    · rw [ite_eq_left zero]
      apply (ProtocolRAMTurnShelf.entry_blank _ _ _ _ ?_).symm
      rintro ⟨u,hu⟩
      obtain ⟨same,_⟩:=decode u (congrArg Prod.snd hu)
      exact u.property ((width u.val).trans ((congrArg bits same).symm.trans zero))
    · rw [ite_eq_right zero,PacketScan.eq_select mem row _ _ _ _ (site_eval old edge route bits o mem row reads sites _ _)
        real ((vertex old edge route a).isLt.trans_le sites) (s.isLt.trans_le sites)]
      change (if (vertex old edge route a).val=s.val then _ else _ : Word W)=_
      have atSlot : StripPaths.positionSeat route short a=slot := by
        rw [←rep]
        apply finProdFinEquiv.injective.eq_iff.mpr
        exact Prod.ext rfl (Fin.ext rfl)
      by_cases hs : vertex old edge route a=s
      · have siteVal:=congrArg Fin.val hs
        rw [ite_eq_left siteVal]
        let u : ProtocolRAMTurnShelf.Live numbers:=⟨ix,by rw [width,back];exact zero⟩
        have location : put u=(s,slot) := by
          rw [position u]
          change (vertex old edge route (turns ix),StripPaths.positionSeat route short (turns ix))=_
          rw [back,hs,atSlot]
        rw [←location,ProtocolRAMTurnShelf.entry_live]
        have reindex := congrArg (fun z : Positions route=>
          (encode z.1 z.2.val (f.castLE (by decide))).eval mem row) back
        exact reindex.symm.trans (values ix (f.castLE (by decide)))
      · rw [ite_eq_right (Fin.ext_iff.not.mp hs)]
        apply (ProtocolRAMTurnShelf.entry_blank _ _ _ _ ?_).symm
        rintro ⟨u,hu⟩
        rw [position u] at hu
        have otherSlot : StripPaths.positionSeat route short (turns u.val)=slot := congrArg Prod.snd hu
        have eq := (StripPaths.positionSeat route short).injective (atSlot.trans otherSlot.symm)
        exact hs ((congrArg (vertex old edge route) eq).trans (congrArg Prod.fst hu))
  · rw [ite_eq_right h]
    apply (ProtocolRAMTurnShelf.entry_blank _ _ _ _ ?_).symm
    rintro ⟨u,hu⟩
    obtain ⟨same,pos⟩:=decode u (congrArg Prod.snd hu)
    exact h (same ▸ pos ▸ (turns u.val).2.isLt)

theorem field_eval (party : Expr) (s : Fin S) (real : party.eval mem row=(s.val : Word W))
    (reads : Reads old edge route bits o mem row) (sites : S≤2^W) (room : m≤2^W)
    (wide : ∀i,bits i<2^W) (slot : Fin (n*3)) (f : Fin 5) :
    (o.field ord party (finProdFinEquiv (slot,f))).eval mem row=
      ProtocolRAMTurnShelf.entry cols putAt f (s,slot) := by
  exact column_eval old edge route bits short turns o mem row (o.words ord) cols putAt (fun _=>rfl)
    (fun _=>rfl) (words_eval old edge route bits ord o mem row reads sites room short turns)
    party s real reads sites wide slot f

/-- Readback at the literal flattened candidate/party/field row of the
single global selected scatter. The positive participant supplies its own
candidate-register value to every original operand. -/
theorem scatter_field {I : ℕ} (base : ℕ) (party active : Fin L→Expr) (candidate : Fin I) (localId : Fin L)
    (s : Fin S) (slot : Fin (n*3)) (f : Fin 5)
    (mounted : ∀z : Fin 3,ProbeStage.CoreBoard.HistoryRoles.RoleROM.Mounted
      (base+z.val*(I*(L*((n*3)*5)))) (SiteScatter.directory I L ((n*3)*5) z) mem)
    (rowsFit : I*(L*((n*3)*5))≤2^W) (partyFit : L≤2^W) (fieldFit : (n*3)*5≤2^W)
    (member : (active localId).eval mem (candidate.val:Word W)≠0)
    (here : (party localId).eval mem (candidate.val:Word W)=(s.val : Word W))
    (reads : Reads old edge route bits o mem (candidate.val:Word W)) (sites : S≤2^W) (room : m≤2^W)
    (wide : ∀i,bits i<2^W) :
    let key:=SiteScatter.order I L ((n*3)*5) (candidate,(localId,finProdFinEquiv (slot,f)))
    (SiteScatter.selectedValue (I:=I) base active (o.siteFields ord party)).eval mem (key.val:Word W)=
      ProtocolRAMTurnShelf.entry cols putAt f (s,slot) := by
  let q : Fin I×(Fin L×Fin ((n*3)*5)) := (candidate,localId,finProdFinEquiv (slot,f))
  change (SiteScatter.selectedValue (I:=I) base active (o.siteFields ord party)).eval mem
    (((SiteScatter.order I L ((n*3)*5) q).val):Word W)=_
  rw [SiteScatter.value_read mem mounted rowsFit partyFit fieldFit active (o.siteFields ord party) q, ite_eq_right member]
  exact field_eval old edge route bits ord short turns o mem (candidate.val:Word W)
    (party localId) s here reads sites room wide slot f

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
