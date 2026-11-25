import OAI.Computability.BorderVNP.DiagonalBootedRouteDecoding

/-! # Recovering every native prefix from the prepared history decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CellMacro.Generator BorderVNP.Cube
variable {R n w axes box lanes choices symbols : ℕ} {X : Type}
    {id : TableEntry axes box lanes choices symbols → ℕ} {gen : Fragment IO}
    (U : X → Fin (R+1) → PinStart gen n w)

private theorem prefix_ext {S : PinStart gen n w} {a b : S.Prefix id}
    (pins : List.ofFn a.1=List.ofFn b.1) (returns : a.2.val=b.2.val) : a=b := by
  obtain ⟨i,v⟩ := a
  obtain ⟨j,z⟩ := b
  obtain rfl : i=j := List.ofFn_injective pins
  exact congrArg (Sigma.mk i) (Subtype.ext returns)

/-- The exterior, raw pin word and chronological machine return determine the whole native prefix tuple. -/
theorem joint_prefix_ext {a b : Σ x : X,(u : Fin (R+1)) → (U x u).Prefix id}
    (wire : a.1=b.1) (pins : ∀ u, List.ofFn (a.2 u).1=List.ofFn (b.2 u).1)
    (returns : ∀ u, (a.2 u).2.val=(b.2 u).2.val) : a=b := by
  obtain ⟨x,p⟩ := a
  obtain ⟨y,t⟩ := b
  change x=y at wire
  subst y
  apply congrArg (Sigma.mk x)
  exact funext fun u => prefix_ext (pins u) (returns u)

end RoutingISA.Evaluator.PinStart

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (gen : Fragment IO) (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation "guess" => (fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl)

local notation "headers" => positiveExteriorFieldsEquiv G args pin L fixed hw size base fit headerWidth
variable {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
  (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
    (Σ c : Physical.Broadcast axes groups cap,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code q,c,claim⟩) ≃
        Σ v : Route q,Report i q v)
  (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B)

/-- Restore the actual entire native tuple underlying a decoded history. The same exterior and each
team's actual pin and full chronological return are retained. This lets predicates on the complete
owned visit and all subsequent report stages use the returned source tuple directly. -/
theorem PreparedHistoryDecoder.bare_restored (i : Fin d → Bool) (q : Hist) (v : Route q)
    (claim : Fin ((R+1)*dim*tally) → Bool) (rows : Report i q v) :
    let source := (routed i q claim).symm ⟨v,rows⟩
    let x := (headers).symm ⟨(⟨code q,source.1,claim⟩ : Fields),source.2.1⟩
    let actual := fun u => (⟨(G.jointGuess ib hb sb).symm i u, source.2.2 u⟩ : (B x u).start.Prefix id)
    (decoder.bare Route Report routed).val.symm ⟨i,q,v,claim,rows⟩ = ⟨x,actual⟩ := by
  intro source x actual
  have h := (decoder.bare Route Report routed).property i q v claim rows
  apply PinStart.joint_prefix_ext (id:=id) U
  · exact Subtype.ext h.1
  · exact fun u => (h.2 u).2
  · exact fun u => (h.2 u).1

/-- Forgetting support on the restored tuple gives precisely the complete physical bare return
at the same decoded fields, on every team simultaneously. -/
theorem PreparedHistoryDecoder.supported_bare_symm
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    (f : PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report) :
    let P := PinStart.positivePrefixes U (fun y => PinStart.preCallSupport_iff (id:=id) U y.val y.property)
      (supportedTeam id B limit burst room next) (supportedTeam_start id B limit burst room next)
    P ((decoder.supported limit burst room next Route Report routed).val.symm f) =
      (decoder.bare Route Report routed).val.symm f := by
  intro P
  apply (decoder.bare Route Report routed).val.injective
  rw [Equiv.apply_symm_apply]
  exact (decoder.supported_apply limit burst room next routed _).symm.trans (Equiv.apply_symm_apply _ f)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
