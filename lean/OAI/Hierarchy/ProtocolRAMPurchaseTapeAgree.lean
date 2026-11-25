import OAI.Hierarchy.ProtocolRAMPurchaseSignedAllocation
import OAI.Hierarchy.ProtocolRAMBelow

namespace OAI
/-! # Prefix agreement for complete numeric outputs of the signed purchase processor

The addresses and one-based row words of sparse owner writes are determined by the
same actual subdivision. Every other transfer is an expression scan over fixed banks.
These statements compare all addresses below the chosen cutoff, including scratch.
-/

namespace Hierarchy.ProtocolRAM.PurchaseTape
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w n m groups D k cut : ℕ} {G : Type*}

private theorem image_cut {dep : ℕ} (out count : ℕ) (e : Expr) {left right : Memory w}
    (readers : e.Fits w dep) (limit : dep≤cut) (same : Calendar.Below cut left right) :
    Calendar.Below cut (ProtocolRAM.image out count e left) (ProtocolRAM.image out count e right) :=
  same.fill _ _ _ _ fun _ _ _ _ => same.expr e _ readers limit

private theorem columns_cut {dep : ℕ} (rows : ℕ) (es : List Expr)
    (readers : ∀ e∈es,e.Fits w dep) (limit : dep≤cut) (out : ℕ) {left right : Memory w}
    (same : Calendar.Below cut left right) :
    Calendar.Below cut (result (ProbeStage.Native.columns rows out es) left)
      (result (ProbeStage.Native.columns rows out es) right) := by
  induction es generalizing out left right with
  | nil => exact same
  | cons e es ih =>
    exact ih (fun v hv => readers v (List.mem_cons_of_mem e hv)) (out+rows)
      (image_cut out rows e (readers e (List.mem_cons_self ..)) limit same)

private theorem indexed_cut (addr : Fin n → ℕ) (val : Fin n → Word w) {left right : Memory w}
    (same : Calendar.Below cut left right) (len : ℕ) :
    Calendar.Below cut (ProtocolRAMIndexedWrite.image addr val left len)
      (ProtocolRAMIndexedWrite.image addr val right len) := by
  induction len with
  | zero => exact same
  | succ t ih =>
    intro a ha
    by_cases row : t<n
    · simp only [ProtocolRAMIndexedWrite.image,dite_eq_left row]
      by_cases hit : a=addr ⟨t,row⟩
      · subst a; simp
      · simpa only [Function.update_of_ne hit] using ih a ha
    · simpa only [ProtocolRAMIndexedWrite.image,dite_eq_right row] using ih a ha

/-- Includes the scratch banks that held the generated address and word streams. -/
theorem owners_agree (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    {left right : Memory w} (fits : ProtocolRAMPurchaseOwners.Fits s.columns w n groups m s.ownerScratch)
    (bound : s.columns.owner.base≤cut) (same : Calendar.Below cut left right) :
    Calendar.Below cut (ProtocolRAMPurchaseOwners.image s.ownerScratch s.columns p enc left)
      (ProtocolRAMPurchaseOwners.image s.ownerScratch s.columns p enc right) := by
  let x := s.columns
  have clear := image_cut (cut:=cut) (dep:=s.columns.owner.base) x.owner.base (groups*m) (.lit 0)
    (left:=left) (right:=right) trivial bound same
  have reads : (ProtocolRAMPurchaseOwners.addressExpr x).Fits w x.owner.base :=
    ⟨trivial,⟨⟨fits.stride,fits.group,trivial⟩,fits.input,trivial⟩⟩
  have addresses := image_cut s.ownerScratch n (ProtocolRAMPurchaseOwners.addressExpr x) reads bound clear
  have values := image_cut (dep:=s.columns.owner.base) (s.ownerScratch+n) n
    ProtocolRAMPurchaseOwners.rowCode ⟨trivial,trivial⟩ bound addresses
  exact indexed_cut _ _ values n

theorem prefix_agree (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (h : ℕ)
    {left right : Memory w} (size : Fits s w n groups m h) (bound : s.source.base≤cut)
    (same : Calendar.Below cut left right) :
    Calendar.Below cut (prefixOut s p enc h left) (prefixOut s p enc h right) := by
  have owner := owners_agree s p enc size.owners (size.sourceAfter.trans bound) same
  let field := PurchaseColumns.field s.directory n h (edge s)
  have room : s.source.base<2^w := by
    have low := size.sourceFit.2.2
    have hi := size.target
    omega
  have fits (e : Expr) (he : e∈List.ofFn field) : e.Fits w s.source.base := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact Expr.fits_of_inputEnd _ (size.fields j) room
  exact columns_cut (count n D h) (List.ofFn field) fits bound s.source.base owner

theorem output_agree (s : Plan D) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (h : ℕ)
    {left right : Memory w} (size : Fits s w n groups m h) (bound : s.packed≤cut)
    (same : Calendar.Below cut left right) :
    Calendar.Below cut (output s p enc h left) (output s p enc h right) := by
  have source := size.sourceFit.2.2
  have «prefix» := prefix_agree s p enc h size (by omega : s.source.base≤cut) same
  have read (e : Expr) (he : e∈GateColumns.inputs s.source s.gates s.work) : e.Fits w s.packed := by
    simp only [GateColumns.inputs,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;> exact GateColumns.term_fits _ _ _ _ size.sourceFit size.gateFit
  exact columns_cut (ProtocolRAMPurchaseGateColumns.gates (count n D h) (h+1)) _ read bound s.packed «prefix»

theorem signed_agree (s : Plan D) (b : Signed k) (j : Fin (2*k)) (p : Tiles (Fin n) G m)
    (enc : G ↪ Fin groups) (h : ℕ) {left right : Memory w}
    (size : Fits s w n groups m h) (sign : SignedFits s b w n) (bound : s.source.base≤cut)
    (same : Calendar.Below cut left right) :
    Calendar.Below cut (signedOut s b j p enc h left) (signedOut s b j p enc h right) := by
  have mark := sign.marks.2.2
  have ord := size.sourceAfter
  exact image_cut b.marks.base (n+1) (PurchaseMarks.markExpr n b.threshold b.stock j)
    (mark_fits s b j sign) (by omega) (prefix_agree s p enc h size bound same)

end Hierarchy.ProtocolRAM.PurchaseTape

namespace Hierarchy.ProtocolRAMPurchaseAllocation.Layout
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w k cut : ℕ} {G : Type*}

theorem prefix_agree (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT)
    (p : Tiles (Fin L.rows) G L.sockets) (enc : G ↪ Fin L.groups) {left right : Memory w}
    (fits : PurchaseTape.Fits (L.plan ct) w L.rows L.groups L.sockets L.height)
    (bound : L.endAddress≤cut) (same : Calendar.Below cut left right) :
    Calendar.Below cut (PurchaseTape.prefixOut (L.plan ct) p enc L.height left)
      (PurchaseTape.prefixOut (L.plan ct) p enc L.height right) := by
  obtain ⟨_,_,_,_,_,src,rom,pack,last⟩ := L.regions
  exact PurchaseTape.prefix_agree _ p enc _ fits (by change L.source.base≤cut; omega) same

theorem output_agree (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT)
    (p : Tiles (Fin L.rows) G L.sockets) (enc : G ↪ Fin L.groups) {left right : Memory w}
    (fits : PurchaseTape.Fits (L.plan ct) w L.rows L.groups L.sockets L.height)
    (bound : L.endAddress≤cut) (same : Calendar.Below cut left right) :
    Calendar.Below cut (PurchaseTape.output (L.plan ct) p enc L.height left)
      (PurchaseTape.output (L.plan ct) p enc L.height right) := by
  have pack := L.regions.tape
  have last := L.regions.limit
  exact PurchaseTape.output_agree _ p enc _ fits (by change L.packed≤cut; omega) same

theorem signed_agree (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT) (threshold : Bank)
    (stock : Fin (2*k) → Bank) (j : Fin (2*k)) (p : Tiles (Fin L.rows) G L.sockets)
    (enc : G ↪ Fin L.groups) {left right : Memory w}
    (fits : PurchaseTape.Fits (L.plan ct) w L.rows L.groups L.sockets L.height)
    (sign : PurchaseTape.SignedFits (L.plan ct) (L.signedInputs threshold stock) w L.rows)
    (bound : L.endAddress≤cut) (same : Calendar.Below cut left right) :
    Calendar.Below cut (PurchaseTape.signedOut (L.plan ct) (L.signedInputs threshold stock) j p enc L.height left)
      (PurchaseTape.signedOut (L.plan ct) (L.signedInputs threshold stock) j p enc L.height right) := by
  obtain ⟨_,_,_,_,_,src,rom,pack,last⟩ := L.regions
  exact PurchaseTape.signed_agree _ _ j p enc _ fits sign (by change L.source.base≤cut; omega) same

end Hierarchy.ProtocolRAMPurchaseAllocation.Layout

end OAI
