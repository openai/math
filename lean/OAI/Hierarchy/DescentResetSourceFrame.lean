import OAI.Hierarchy.DescentResetAtomLedger
import OAI.Hierarchy.DescentPlainTerminal

namespace OAI
/-! # Original exterior attachments retain their actual selected hub prefix -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentResetAttachments DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P H Q : Type} [Field F] [Fintype H] [Fintype Q] {d n : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (input : Bool→A.graph.Edge→Q) (hub : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth input w))
variable (T : R.Tables F)

omit [Fintype Q] in
theorem installedExterior (p : P) :
    installedNames A home input hub same R T ((install A home input hub same R T).graph.attach p)=
      .inl (false,home (A.graph.attach p)) := by subst w;rfl

end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentGL DescentColonies DescentResetTrunks DescentContacts
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable (pos : A.graph.Site→V) (ix : A.graph.Site→Block k) (hub : V→Bool) (g : ℕ)

/-- The already measured basis on the original block coordinates, together with
the original host positions tracked into the existential placement. -/
structure SourceFrame where
  host : V≃Z.V
  basis : Layout k
  used : HEq basis Z.placement.L
  extent : Z.k=k
  actor : ∀s i,(Z.placement.old s i).1=host (pos (DescentResetAttachments.ends A.graph s i))
  oldBlock : ∀s i,(Z.placement.old s i).2.val=(ix (DescentResetAttachments.ends A.graph s i)).val
  homeHigh : ∀u,DescentChosenRouter.coarseName T.commonDepth (T.code (T.home u))=
    group T.commonDepth (rearrange basis (ix u))
  homeHost : ∀u,(T.code (T.home u)).1=host (pos u)
  rotorHub : ∀v,Z.placement.hub (host v) ↔ hub v=true
  originalHub : ∀u,Z.hub u=hub (pos u)
  fits : g≤k
  enough : T.commonDepth≤k-g
  atHub : ∀u,hub (pos u)=true → T.code (T.home u)=
    (host (pos u),((k-g,group (k-g) (rearrange basis (ix u))),none))

/-- The very host IDs, geometric incidence and marked-epoch traffic used
by the instantiated public rotor and fallback directories. -/
def SourceFrame.Roster (frame : SourceFrame Z T pos ix hub g) (vertex : V↪ℕ) (near : V→Finset V)
    (n f B wire K : ℕ) (traffic : V→V→Block k→ℝ) (Δ : ℕ) (weight : V→Block k→ℕ)
    [Fintype V] [DecidableEq V] : Prop :=
  (∀v,T.columns.host (frame.host v)=vertex v) ∧
  (∀v w,frame.host w∈T.columns.near (frame.host v) ↔ w∈near v) ∧
  (∀v w,T.columns.size (frame.host v) (frame.host w)=
    DescentBaseProfile.rowCount (2^n) ((2:ℝ)^f*(B/wire))
      (DescentBaseProfile.pairCapacity k (Z.placement.b (frame.host v)) (Z.placement.b (frame.host w))
        (DescentBaseProfile.blockMean k (traffic v w)) ((2:ℕ)^f*B) K/wire)) ∧
  (∀v j,(frame.host v,j)∈Z.placement.keys ↔ (v,j)∈resetKeys near Δ f B K weight traffic
    (fun v=>Z.placement.b (frame.host v)) (fun v=>(Z.placement.depth (frame.host v)).trans_eq frame.extent) frame.basis) ∧
  (∀z,T.leaves.window z=DescentFineTerminals.window (k:=Z.k-T.commonDepth) (g:=g) (f:=f)
    (D:=32*Nat.clog 2 (2*Δ)) T.columns.near (fun v=>hub (frame.host.symm v)) z) ∧
  ∃ room : ∀v x,weight v x≤B,
    let row:=DescentPlainTerminal.endpoint near (fun v=>Z.placement.b (frame.host v)) frame.basis weight
      f (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) room (fun v j=>(frame.host v,j)∈Z.placement.keys) hub
    (∀u,DescentPlainTerminal.fields (T.code (T.home u)).2=row (pos u) (ix u)) ∧
    ∀v z,(∃t,(T.code t).1=frame.host v ∧ DescentPlainTerminal.fields (T.code t).2=z) ↔
      ∃x,row v x=z

theorem read_source_pin (p : P) : resetNames Z T ((Z.reenter T).graph.attach p)=
    .inl (false,T.home (A.graph.attach p)) :=
  installedExterior _ _ _ _ _ _ _ p

theorem source_pin_site (frame : SourceFrame Z T pos ix hub g) (p q : P)
    (both : hub (pos (A.graph.attach p))=true) (position : pos (A.graph.attach p)=pos (A.graph.attach q))
    (high : group (k-g) (rearrange frame.basis (ix (A.graph.attach p)))=
      group (k-g) (rearrange frame.basis (ix (A.graph.attach q)))) :
    (Z.reenter T).graph.attach p=(Z.reenter T).graph.attach q := by
  apply (resetNames Z T).injective
  rw [read_source_pin,read_source_pin]
  apply congrArg (fun z=>Sum.inl (false,z))
  apply T.code.injective
  rw [frame.atHub _ both,frame.atHub _ (position ▸ both),position,high]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
