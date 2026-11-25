import OAI.Hierarchy.DescentResetPublicOperandBook
import OAI.Hierarchy.DescentOperandPublicCasts
import OAI.Hierarchy.DescentOperandPreparedPacketPhase
import OAI.Hierarchy.DescentStemCoordinateBook

namespace OAI
/-! # Public operand inputs from the relocated packet, coordinate columns and reported host -/
namespace Hierarchy.DescentResetPublicOperandBook
open ProtocolRAM DescentSIMDLookup DescentPackedZip DescentPacking DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

inductive Port where
  | active
  | register (i : Fin 4)
  | aux (i : Fin 4)
  | coordinate (j : Fin 3) (lo : ℕ)
  | packet (matrix : Bool) (i : ℕ)
  | empty

namespace Config
variable (C : Config) {n : ℕ}
def headerPort : Fin 8→Port :=
  ![.active,.register 0,.register 3,.aux 3,.register 1,.register 2,.empty,.empty]

/-- The matrix prefix occurs in the original fallback packet as well. Its two
extra blocks are represented by their ordinals in the authentic matrix packet. -/
def port (i : Fin (C.inputs n)) : Port :=
  match finSumFinEquiv.symm i with
  | .inr j=>.packet true (DescentRotorWindowArchive.ix (cap:=C.oldCap) (.inr ((C.extraId).symm j))).val
  | .inl z=>match (C.oldConfig.ports n).symm z with
    | .inl (.inl j)=>headerPort j
    | .inl (.inr (j,p))=>
      let q : Fin C.donors×Fin (2*C.oldCap):=finProdFinEquiv.symm p
      if j=0 then .coordinate 0 q.1.val else if j=1 then .coordinate 1 q.1.val else .empty
    | .inr j=>.packet false (DescentFallbackPeriod.number j).val

theorem port_basic (i : Fin (C.oldConfig.inputs n)) :
    C.port (Fin.castAdd C.extraCount i)=
      (match (C.oldConfig.ports n).symm i with
       | .inl (.inl j)=>headerPort j
       | .inl (.inr (j,p))=>
         let q : Fin C.donors×Fin (2*C.oldCap):=finProdFinEquiv.symm p
         if j=0 then Port.coordinate 0 q.1.val else if j=1 then .coordinate 1 q.1.val else .empty
       | .inr j=>.packet false (DescentFallbackPeriod.number j).val) :=by
  simp [port]

theorem port_extra (e : C.Extra) : C.port (Fin.natAdd (C.oldConfig.inputs n) (C.extraId e))=
    .packet true (DescentRotorWindowArchive.ix (cap:=C.oldCap) (.inr e)).val :=by
  simp [port]

end Config
structure Ports where
  packets : DescentOperandRootPull.Pair
  coordinates : DescentStemCoordinateBook.Shape
  casts : DescentOperandPublicCasts.Plan
  saved : Bank
  coordinateBase : ℕ
  packetBase : ℕ
  castBase : ℕ
  aux : Fin 4→Expr
  active : Expr
  registers : Fin 4→Expr

namespace Ports
variable (P : Ports)
def expr (x : ℕ) : Port→Expr
  | .active=>P.active
  | .empty=>.lit 0
  | .register j=>P.registers j
  | .aux j=>P.casts.expr P.castBase 2 (P.aux j)
  | .coordinate j lo=>
    if hit : x<2^P.coordinates.fine ∧ lo<2^P.coordinates.residual then
      P.casts.expr P.castBase 1 (P.coordinates.src P.coordinateBase P.saved j ⟨x,hit.1⟩ ⟨lo,hit.2⟩)
    else .lit 0
  | .packet f j=>
    if hit : j<(P.packets.stage 0 f).fields ∧ x<P.packets.blocks then
      P.casts.expr P.castBase 0 (P.packets.src P.packetBase f ⟨j,hit.1⟩ ⟨x,hit.2⟩)
    else .lit 0

def publicInput (C : Config) {n : ℕ} (x : ℕ) (j : Fin (C.inputs n)) : Expr :=P.expr x (C.port j)

/-- These functions index only measured columns at the current receiver. Their
domains are the original finite packets and donor window, independent of host count. -/
structure Values (P : Ports) (H G : ℕ) where
  active : Fin H→Fin G→Cell P.casts.bits
  register : Fin 4→Fin H→Fin G→Cell P.casts.bits
  aux : Fin 4→Fin H→Fin G→Cell (P.casts.width 2)
  coord : Fin 3→Block P.coordinates.fine→Block P.coordinates.residual→Fin H→Fin G→Cell (P.casts.width 1)
  packet : (f : Bool)→Fin (P.packets.stage 0 f).fields→Fin P.packets.blocks→Fin H→Fin G→Cell (P.casts.width 0)

def value {H G} (v : P.Values H G) (x : ℕ) (h : Fin H) (g : Fin G) : Port→Cell P.casts.bits
  | .active=>v.active h g
  | .empty=>0
  | .register j=>v.register j h g
  | .aux j=>(v.aux j h g).val
  | .coordinate j d=>if hit:x<2^P.coordinates.fine ∧ d<2^P.coordinates.residual then
      (v.coord j ⟨x,hit.1⟩ ⟨d,hit.2⟩ h g).val else 0
  | .packet f j=>if hit:j<(P.packets.stage 0 f).fields ∧ x<P.packets.blocks then
      (v.packet f ⟨j,hit.1⟩ ⟨x,hit.2⟩ h g).val else 0

structure RawPrior {H G w} (v : P.Values H G) (m : Memory w) : Prop where
  aux : ∀j,(P.aux j).Fits w P.castBase ∧ Source (P.aux j) (v.aux j) P.casts.lanes m
  coord : ∀j x d,let s:=P.coordinates.src P.coordinateBase P.saved j x d
                 s.Fits w P.castBase ∧ Source s (v.coord j x d) P.casts.lanes m
  packet : ∀f j x,let s:=P.packets.src P.packetBase f j x
                  s.Fits w P.castBase ∧ Source s (v.packet f j x) P.casts.lanes m

structure Prior {H G w} (v : P.Values H G) (m : Memory w) : Prop extends P.RawPrior v m where
  active : P.active.Fits w P.castBase ∧ Source P.active v.active P.casts.lanes m
  register : ∀j,(P.registers j).Fits w P.castBase ∧ Source (P.registers j) (v.register j) P.casts.lanes m

theorem public_late {H G w roof} (v : P.Values H G) (m dst : Memory w) (held : P.RawPrior v m)
    (room : P.casts.endAddress P.castBase<2^w) (bound : P.casts.endAddress P.castBase≤roof)
    (frame : ∀z,z<P.casts.endAddress P.castBase→dst z=P.casts.image P.castBase m z)
    (active : P.active.Fits w roof ∧ Source P.active v.active P.casts.lanes dst)
    (reg : ∀j,(P.registers j).Fits w roof ∧ Source (P.registers j) (v.register j) P.casts.lanes dst)
    (x : ℕ) (p : Port) :
    (P.expr x p).Fits w roof ∧ Source (P.expr x p) (fun h g=>P.value v x h g p) P.casts.lanes dst :=by
  let out:=P.casts.image P.castBase m
  have zero : (Expr.lit 0).Fits w roof ∧
      Source (Expr.lit 0) (fun (_:Fin H) (_:Fin G)=>(0:Cell P.casts.bits)) P.casts.lanes dst :=by
    refine ⟨trivial,?_⟩
    intro q
    change 0=(((finFunctionFinEquiv (fun i : Fin P.casts.lanes=>
      if _ : q.2.val*P.casts.lanes+i.val<G then (0:Cell P.casts.bits) else 0)).val:ℕ):Word w)
    simp []
  have keep (s : Expr) (a : Fin H→Fin G→Cell P.casts.bits)
      (r : s.Fits w (P.casts.endAddress P.castBase) ∧ Source s a P.casts.lanes out) :
      s.Fits w roof ∧ Source s a P.casts.lanes dst :=by
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ bound r.1,?_⟩
    intro q
    exact (eval_below _ _ out dst r.1 frame).trans (r.2 q)
  cases p with
  | empty=>exact zero
  | active=>exact active
  | register j=>exact reg j
  | aux j=>exact keep _ _ (P.casts.issued P.castBase 2 (P.aux j) m _ (held.aux j).1 (held.aux j).2 room)
  | coordinate j d=>
    by_cases hit:x<2^P.coordinates.fine ∧ d<2^P.coordinates.residual
    · simp only [expr,value,dite_eq_left hit]
      exact keep _ _ (P.casts.issued P.castBase 1 _ m _ (held.coord j _ _).1 (held.coord j _ _).2 room)
    · simpa only [expr,value,dite_eq_right hit] using zero
  | packet f j=>
    by_cases hit:j<(P.packets.stage 0 f).fields ∧ x<P.packets.blocks
    · simp only [expr,value,dite_eq_left hit]
      exact keep _ _ (P.casts.issued P.castBase 0 _ m _ (held.packet f _ _).1 (held.packet f _ _).2 room)
    · simpa only [expr,value,dite_eq_right hit] using zero

theorem public_read {H G w} (v : P.Values H G) (m : Memory w) (held : P.Prior v m)
    (room : P.casts.endAddress P.castBase<2^w) (x : ℕ) (p : Port) :
    let out:=P.casts.image P.castBase m
    (P.expr x p).Fits w (P.casts.endAddress P.castBase) ∧
      Source (P.expr x p) (fun h g=>P.value v x h g p) P.casts.lanes out :=by
  let out:=P.casts.image P.castBase m
  have keep (s : Expr) (a : Fin H→Fin G→Cell P.casts.bits)
      (r : s.Fits w P.castBase ∧ Source s a P.casts.lanes m) :
      s.Fits w (P.casts.endAddress P.castBase) ∧ Source s a P.casts.lanes out :=by
    have f:=(P.casts.any P.castBase m room).2.2
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) r.1,?_⟩
    intro q
    exact (eval_below _ _ m out r.1 (fun z hz=>f z (.inl hz))).trans (r.2 q)
  exact P.public_late v m out held.toRawPrior room le_rfl (fun _ _=>rfl)
    (keep _ _ held.active) (fun j=>keep _ _ (held.register j)) x p

end Ports
end
end Hierarchy.DescentResetPublicOperandBook

end OAI
