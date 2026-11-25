import OAI.Hierarchy.DescentResetOriginalDonors

namespace OAI
/-! # Retaining all three measured donor fields after the complete publication -/
namespace Hierarchy.DescentResetOriginalDonors.Layout
open DescentSIMDLookup DescentPackedZip DescentResetDenseOperand
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (L : DescentResetOriginalDonors.Layout) (base : ℕ) (src : Sensors L.slots) {w : ℕ}
local notation "N" => L.slots
local notation "X" => L.blocks
local notation "A" => Fin L.sparseHosts
local notation "G" => Fin (L.groups*X)
local notation "t₀" => L.ticketBase base
local notation "h₀" => L.haloBase base

structure Values where
  label : Bool→Fin N→A→G→Cell L.fieldBits
  ticket : Bool→Fin N→A→G→Cell L.fieldBits
  halo : Fin N→A→G→Cell L.metaBits

structure Seen (v : L.Values) (m : Memory w) : Prop where
  label : ∀s j,Source (src.label s j) (v.label s j) L.lanes m
  ticket : ∀s j,Source (src.ticket s j) (v.ticket s j) L.lanes m
  halo : ∀j,Source (src.halo j) (v.halo j) L.lanes m

private theorem later_source {hosts groups lanes b w cut : ℕ} (e : Expr) (a d : Memory w)
    (v : Fin hosts→Fin groups→Cell b) (fit : e.Fits w cut) (before_ : Source e v lanes a)
    (keep : ∀p,p<cut→d p=a p) : Source e v lanes d := fun row=>
  (ProtocolRAM.eval_below _ _ a d fit keep).trans (before_ row)

structure Exhibits (v : L.Values) (m : Memory w) : Prop where
  label : ∀s j x,(L.labels.bank base (L.wing s j) x).Fits w (L.endAddress base) ∧
    Source (.lookup (L.labels.bank base (L.wing s j) x) .row)
      (fun h g=>DescentContactWidthPage.recode L.selectorBits (v.label s j h (finProdFinEquiv (g,x)))) L.lanes m
  ticket : ∀s j x,(L.tickets.bank t₀ (L.wing s j) x).Fits w (L.endAddress base) ∧
    Source (.lookup (L.tickets.bank t₀ (L.wing s j) x) .row)
      (fun h g=>DescentContactWidthPage.recode L.shortBits (v.ticket s j h (finProdFinEquiv (g,x)))) L.lanes m
  halo : ∀j x,(L.halos.bank h₀ j x).Fits w (L.endAddress base) ∧
    Source (.lookup (L.halos.bank h₀ j x) .row)
      (fun h g=>DescentContactWidthPage.recode L.shortBits (v.halo j h (finProdFinEquiv (g,x)))) L.lanes m

theorem exhibits (v : L.Values) (m : Memory w) (ready : L.Ready base src w) (seen : L.Seen src v m) :
    L.Exhibits base v (L.after base src m) := by
  obtain ⟨low,mid,high⟩:=L.cuts base
  let lm:=L.labels.after base (L.lift src.label) m
  let tm:=L.tickets.after t₀ (L.lift src.ticket) lm
  let labelVal (q : Fin (2*N)):=v.label (finTwoEquiv (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2
  let ticketVal (q : Fin (2*N)):=v.ticket (finTwoEquiv (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2
  have lr:=(mid.trans high).trans_lt ready.room
  have tr:=high.trans_lt ready.room
  have first:=L.labels.any base (L.lift src.label) m ready.lanes ready.blocks (fun _=>ready.label _ _) lr
  have second:=L.tickets.any t₀ (L.lift src.ticket) lm ready.lanes ready.blocks
    (fun _=>ProtocolRAMGeneratedWrite.fits_mono _ low (ready.ticket _ _)) tr
  have last:=L.halos.any h₀ src.halo tm ready.lanes ready.blocks
    (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ (low.trans mid) (ready.halo j)) ready.room
  have earlier (p : ℕ) (lt : p<base) : tm p=m p :=
    (second.2.2 p (.inl (lt.trans_le low))).trans (first.2.2 p (.inl lt))
  have labels:=L.labels.rows base (L.lift src.label) m labelVal ready.lanes ready.blocks
    (fun _=>ready.label _ _) (fun _=>seen.label _ _) lr
  have tickets:=L.tickets.rows t₀ (L.lift src.ticket) lm ticketVal ready.lanes ready.blocks
    (fun _=>ProtocolRAMGeneratedWrite.fits_mono _ low (ready.ticket _ _))
    (fun _=>later_source _ m lm _ (ready.ticket _ _) (seen.ticket _ _) (fun p lt=>first.2.2 p (.inl lt))) tr
  have halos:=L.halos.rows h₀ src.halo tm v.halo ready.lanes ready.blocks
    (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ (low.trans mid) (ready.halo j))
    (fun j=>later_source _ m tm _ (ready.halo j) (seen.halo j) earlier) ready.room
  refine ⟨?_,?_,halos⟩
  · intro s j x
    obtain ⟨fit,stored⟩:=labels (L.wing s j) x
    refine ⟨⟨fit.1,fit.2.1,fit.2.2.trans (mid.trans high)⟩,?_⟩
    apply later_source _ lm _ _ (show (Expr.lookup _ .row).Fits w t₀ from ⟨fit,trivial⟩)
    · have sourceAtWing : labelVal (L.wing s j) = v.label s j := by
        simp only [labelVal, wing, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      rw [sourceAtWing] at stored
      with_unfolding_all exact stored
    · exact fun p lt=>(last.2.2 p (.inl (lt.trans_le mid))).trans (second.2.2 p (.inl lt))
  · intro s j x
    obtain ⟨fit,stored⟩:=tickets (L.wing s j) x
    refine ⟨⟨fit.1,fit.2.1,fit.2.2.trans high⟩,?_⟩
    apply later_source _ tm _ _ (show (Expr.lookup _ .row).Fits w h₀ from ⟨fit,trivial⟩)
    · have sourceAtWing : ticketVal (L.wing s j) = v.ticket s j := by
        simp only [ticketVal, wing, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      rw [sourceAtWing] at stored
      with_unfolding_all exact stored
    · exact fun p lt=>last.2.2 p (.inl lt)

/-- The same compact receiver count and inverse are used for every original field;
this includes the zero receiver in each padded row. -/
theorem compact (v : L.Values) (m : Memory w) (available : L.Exhibits base v m)
    {H used : ℕ} (first : ℕ) (cnt inv : Bank) (name : Fin used→Fin L.sparseHosts)
    (book : (⟨first,H,L.sparseHosts,chunks L.groups L.lanes⟩ : DescentResetDenseOperand.Layout).Books m)
    (roof : ℕ) (banks : (⟨first,H,L.sparseHosts,chunks L.groups L.lanes⟩ : DescentResetDenseOperand.Layout).Fits cnt inv w roof)
    (count : m cnt.base=(used:Word w)) (names : ∀i : Fin used,m (inv.base+i.val)=((name i).val:Word w))
    (fits : used<2^w) (hosts : H≤2^w) (size : used≤ inv.size) :
    let R : DescentResetDenseOperand.Layout := ⟨first,H,L.sparseHosts,chunks L.groups L.lanes⟩
    (∀x s j,Source (L.label base R cnt inv x s j) (dense (H:=H) name
      (fun h g=>DescentContactWidthPage.recode L.selectorBits (v.label s j h (finProdFinEquiv (g,x))))) L.lanes m) ∧
    (∀x s j,Source (L.cargo base R cnt inv x s 0 j) (dense (H:=H) name
      (fun h g=>DescentContactWidthPage.recode L.shortBits (v.ticket s j h (finProdFinEquiv (g,x))))) L.lanes m) ∧
    ∀x s j,Source (L.cargo base R cnt inv x s 1 j) (dense (H:=H) name
      (fun h g=>DescentContactWidthPage.recode L.shortBits (v.halo j h (finProdFinEquiv (g,x))))) L.lanes m :=by
  exact ⟨fun x s j=>DescentResetDenseOperand.source first cnt inv _ m name _ (available.label s j x).2 roof
      book banks count names fits hosts size,
    fun x s j=>DescentResetDenseOperand.source first cnt inv _ m name _ (available.ticket s j x).2 roof
      book banks count names fits hosts size,
    fun x s j=>DescentResetDenseOperand.source first cnt inv _ m name _ (available.halo j x).2 roof
      book banks count names fits hosts size⟩

end
end Hierarchy.DescentResetOriginalDonors.Layout

end OAI
