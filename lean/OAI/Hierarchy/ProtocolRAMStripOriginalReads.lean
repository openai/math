import OAI.Hierarchy.ProtocolRAMStripEdgeIDs

namespace OAI
/-! # The original strip expressions and their equality at a native ballot -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.StripPorts
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe

variable {S : PurchaseSampler} {h d k w : ℕ} {C H A B : Type*}
    (p : StripPorts S h d k C H B) (b : Board) (stored : A→Expr)
local notation "R" => ColumnWires.Role C H (A⊕B) k

structure OriginalFits (w cut : ℕ) : Prop where
  primary : ∀r:R,(p.primary b r).Fits w cut
  mate : ∀r:R,(p.mate b r).Fits w cut
  column : ∀c,(p.column c).Fits w cut
  stock : ∀u,(stored u).Fits w cut

structure OriginalReads (left right : Memory w) : Prop where
  primary : ∀r:R,∀reg,(p.primary b r).eval left reg=(p.primary b r).eval right reg
  mate : ∀r:R,∀reg,(p.mate b r).eval left reg=(p.mate b r).eval right reg
  column : ∀c,∀reg,(p.column c).eval left reg=(p.column c).eval right reg
  stock : ∀u,∀reg,(stored u).eval left reg=(stored u).eval right reg

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.StripPorts

end OAI
