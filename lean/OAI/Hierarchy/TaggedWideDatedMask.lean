import OAI.Hierarchy.TaggedWideDatedRoleInput
import OAI.Hierarchy.ProtocolRAMCatalogueEdgeCost
import OAI.Hierarchy.ProtocolRAMCatalogueRows

namespace OAI
/-! # Only actually acquired original catalogue rows publish dated paid widths -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope AdaptiveProbe ProtocolRAM ProtocolRAM.Calendar.CatalogueRows RoleProgram
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {h W k attempts n w : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : ReportSockets.Marks h W k attempts) (b : Calendar.CatalogueRows.Board) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (size : attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (orderRows : Fin n≃Source S π depth marked)
local notation "raw" => DatedRows.raw S π depth marked b order size orderRows
local notation "ord" => b.ordinal S π depth marked order size
local notation "acq" => fun p : ReportSockets.Bought S π depth marked =>
  Fin.cast size (originalBought S π depth marked p)

def mask (b : Calendar.CatalogueRows.Board) (g : Inventory) (amount : Expr) : Expr :=
  .branch .eq (.branch .eq g.kind (.lit 0) (b.checkedEdge g.index) g.index) g.index amount (.lit 0)

theorem mask_fits (g : Inventory) (e : Expr) {dest : ℕ} (flag : b.bought.flag.Fits w dest)
    (kind : g.kind.Fits w dest) (idx : g.index.Fits w dest) (amount : e.Fits w dest) :
    (mask b g e).Fits w dest := ⟨⟨kind,trivial,b.checkedEdge_fits _ flag idx,idx⟩,idx,amount,trivial⟩

theorem mask_work (g : Inventory) (e : Expr) :
    (mask b g e).work≤g.kind.work+edgeWork g.index.work b.bought.flag.work+2*g.index.work+e.work+4 := by
  have bound:=b.checkedEdge_work g.index
  simp only [mask,Expr.work]
  omega

/-- All dated fields are read after the physical prefix replay has finished.
An initialized catalogue flag below its first write retains the original
bidirectional purchased-row characterization on that same final memory. -/
theorem flags_frame (before after : Memory w) (limit : ℕ) (fit : b.bought.flag.Fits w limit)
    (frame : ∀a<limit,after a=before a)
    (flags : ∀j : Fin b.boughtRows,b.bought.flag.eval before (j.val:Word w)≠0 ↔ ∃p,acq p=j) :
    ∀j : Fin b.boughtRows,b.bought.flag.eval after (j.val:Word w)≠0 ↔ ∃p,acq p=j := by
  intro j
  rw [eval_below b.bought.flag (j.val:Word w) before after fit frame]
  exact flags j

variable (g : Inventory) (m : Memory w) (v : Expr) (o : Fin (Fintype.card (Old h W k b.rows)))
local notation "rr" => (o.val:Word w)
local notation "old" => SettledMatrix.Layout.numbered (r:=b.rows) (I:=Goods h W k) (A:=Catalysts h W k) o
variable (hdr : g.kind.eval m (o.val : Word w) =
    (tag (SettledMatrix.Layout.numbered (r:=b.rows) (I:=Goods h W k) (A:=Catalysts h W k) o) : Word w) ∧
  g.index.eval m (o.val : Word w) =
    (localIndex (SettledMatrix.Layout.numbered (r:=b.rows) (I:=Goods h W k) (A:=Catalysts h W k) o) : Word w))
    (room : b.rows<2^w) (wide : 2<2^w)

include hdr room wide in
theorem mask_live (i : Fin n) (orig : o=raw i) (active : ∀p,b.bought.flag.eval m ((acq p).val:Word w)≠0) :
    (mask b g v).eval m rr=v.eval m rr := by
  subst o
  rw [DatedRows.numbered_raw] at hdr
  have ne:=codes wide
  rcases hit : orderRows i with (p|p)|a|c
  · rw [hit] at hdr
    let j:=order.symm p
    change g.kind.eval m (↑(raw i).val)=0 ∧ g.index.eval m (↑(raw i).val)=(j.val:Word w) at hdr
    have hi : j.val<2^w:= (b.coreIndex j).isLt.trans room
    have chk:=b.checked_core g.index m ((raw i).val:Word w) j room
      (by rw [hdr.2,Fin.val_cast_of_lt hi])
    simp [mask,Expr.eval,Comparison.test,hdr.1,hdr.2,chk]
  · rw [hit] at hdr
    let j:=acq p
    change g.kind.eval m (↑(raw i).val)=0 ∧
      g.index.eval m (↑(raw i).val)=((b.boughtIndex j).val:Word w) at hdr
    have chk:=b.checked_bought g.index m ((raw i).val:Word w) j room
      (by rw [hdr.2,Fin.val_cast_of_lt ((b.boughtIndex j).isLt.trans room)]) (active p)
    simp [mask,Expr.eval,Comparison.test,hdr.1,hdr.2,chk]
  · rw [hit] at hdr
    change g.kind.eval m (↑(raw i).val)=1 ∧ _ at hdr
    simp [mask,Expr.eval,Comparison.test,hdr.1,ne.1]
  · rw [hit] at hdr
    change g.kind.eval m (↑(raw i).val)=2 ∧ _ at hdr
    simp [mask,Expr.eval,Comparison.test,hdr.1,ne.2.1]

include hdr room in
theorem mask_blank (missing : DatedRows.lookup S π depth marked b order size orderRows o=none)
    (found : ∀j : Fin b.boughtRows,b.bought.flag.eval m (j.val:Word w)≠0 → ∃p,acq p=j) :
    (mask b g v).eval m rr=0 := by
  obtain ⟨e,which,no⟩:=DatedRows.lookup_dormant S π depth marked b order size orderRows missing
  rw [which] at hdr
  change g.kind.eval m rr=0 ∧ g.index.eval m rr=(e.val:Word w) at hdr
  rcases b.split_index e with ⟨j,eqn⟩|⟨j,eqn⟩
  · apply False.elim
    apply no
    exact ⟨.inl (order j),(congrArg b.coreIndex (order.symm_apply_apply j)).trans eqn⟩
  · have different : (b.checkedEdge g.index).eval m rr≠g.index.eval m rr := by
      intro same
      have seen:=b.checked_hit g.index m rr j room (by rw [same,hdr.2,Fin.val_cast_of_lt (e.isLt.trans room),eqn])
      obtain ⟨p,hit⟩:=found j seen
      exact no ⟨.inr p,(congrArg b.boughtIndex hit).trans eqn⟩
    simp [mask,Expr.eval,Comparison.test,hdr.1,different]

include hdr room wide in
/-- Even before choosing any semantic incidence enumeration, the mask
leaves measured widths unchanged whenever every charged acquisition was open. -/
theorem mask_supported (paid : Fin b.rows→ℕ) (flow : Goods h W k→ℕ) (left : Catalysts h W k→ℕ)
    (read : (v.eval m rr).val=Sum.elim paid (Sum.elim flow left) old)
    (backed : ∀j : Fin b.boughtRows,0<paid (b.boughtIndex j)→b.bought.flag.eval m (j.val:Word w)≠0) :
    (mask b g v).eval m rr=v.eval m rr := by
  have ne:=codes wide
  rcases code : old with e|i|a
  · rw [code] at hdr read
    change g.kind.eval m rr=0 ∧ g.index.eval m rr=(e.val:Word w) at hdr
    change (v.eval m rr).val=paid e at read
    rcases b.split_index e with ⟨j,rfl⟩|⟨j,rfl⟩
    · have same:=b.checked_core g.index m rr j room
        (by rw [hdr.2,Fin.val_cast_of_lt ((b.coreIndex j).isLt.trans room)]; rfl)
      simp [mask,Expr.eval,Comparison.test,hdr.1,hdr.2,same,Calendar.CatalogueRows.Board.coreIndex]
    · by_cases used : 0<paid (b.boughtIndex j)
      · have same:=b.checked_bought g.index m rr j room
          (by rw [hdr.2,Fin.val_cast_of_lt ((b.boughtIndex j).isLt.trans room)]) (backed j used)
        simp [mask,Expr.eval,Comparison.test,hdr.1,hdr.2,same]
      · have zero : v.eval m rr=0:=Fin.ext (by change (v.eval m rr).val=0;omega)
        simp [mask,Expr.eval,zero]
  · rw [code] at hdr
    change g.kind.eval m rr=1 ∧ _ at hdr
    simp [mask,Expr.eval,Comparison.test,hdr.1,ne.1]
  · rw [code] at hdr
    change g.kind.eval m rr=2 ∧ _ at hdr
    simp [mask,Expr.eval,Comparison.test,hdr.1,ne.2.1]

include hdr room wide in
/-- This is the word read by both endpoints of the dated native row. It assigns
each present source its measured width and emits zero on every non-source. -/
theorem mask_lookup (paid : Fin b.rows→ℕ) (flow : Goods h W k→ℕ) (left : Catalysts h W k→ℕ)
    (read : (v.eval m rr).val=Sum.elim paid (Sum.elim flow left) old)
    (flags : ∀j : Fin b.boughtRows,b.bought.flag.eval m (j.val:Word w)≠0 ↔ ∃p,acq p=j) :
    ((mask b g v).eval m rr).val=(DatedRows.lookup S π depth marked b order size orderRows o).elim 0
      (fun i=>Sum.elim (fun e=>paid (ord e)) (Sum.elim flow left) (orderRows i)) := by
  cases look : DatedRows.lookup S π depth marked b order size orderRows o with
  | none=>
    rw [mask_blank S π depth marked b order size orderRows g m v o hdr room look (fun j=>(flags j).mp)]
    rfl
  | some i=>
    have orig:=(DatedRows.lookup_found S π depth marked b order size orderRows look).symm
    rw [mask_live S π depth marked b order size orderRows g m v o hdr room wide i orig
      (fun p=>(flags _).mpr ⟨p,rfl⟩),read,orig]
    exact width_at S π depth marked b order size orderRows paid flow left i

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleInput
end

end OAI
