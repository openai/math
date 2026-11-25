import OAI.Hierarchy.DescentFallbackCellLeaf

namespace OAI
/-! # Reading all arrived leaves by the earlier signed-port data pins -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le m g)
local notation "H" => Host J V k
local notation "src" => DescentIssuedFallbackPanel.endSite (W:=W) A
variable (names : Host J V k ↪ ℕ)
def oldCellAt (t : Z.Fallback) (lo : Fin (2^(m-c))) : H :=
  donor digits frame.basis fits (frame.host.symm (T.code t).1) (selectedRoot A S ready Z T t) lo

/-- Output of one gathered local-cell field and its counterpart. Both are
addressed by a local slot and a relative old coordinate. -/
def signedLeaf (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (digits : Block m ≃ J × Block k) (native : W.graph.Edge ↪ ℕ)
    (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
      (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
    (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u => (A.pos u).2)
      (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (names : Host J V k ↪ ℕ) (s : Bool) (t : Z.Fallback)
    (j : Fin (2^(m-T.commonDepth)) × Fin (2*A.cap)) : Option (Fin (2^Ht)) :=
  let u : Host J V k := oldCellAt A S ready digits Z T frame t j.1
  (DescentIssuedFallbackPanel.signedPeer A native S ready names s u j.2).bind
    (fun v => cellLeaf A S ready digits Z T frame s t u v)


private theorem donorHigh (t : Z.Fallback) (lo : Fin (2^(m-c))) :
    group c (rearrange frame.basis (oldBlock digits (oldCellAt A S ready digits Z T frame t lo)))=
      coarseName c (T.code t) := by
  let hi := selectedRoot A S ready Z T t
  change group c (rearrange frame.basis (digits.symm
    (digits ((rearrange frame.basis).symm (join fits hi lo))))) = hi.val
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  exact congrArg Fin.val (DescentPlainTerminal.high_join fits hi lo)

theorem signedLeaf_read (s : Bool) (t : Z.Fallback) (j : Fin (2^(m-c))×Fin (2*A.cap)) :
    signedLeaf A S ready digits native Z T frame names s t j=
      leafPanel A S ready digits native Z T frame s t (finProdFinEquiv j) := by
  let u : Host J V k := oldCellAt A S ready digits Z T frame t j.1
  simp only [signedLeaf,signedPeer_slot,leafPanel,Equiv.symm_apply_apply,fallbackPanel,panel]
  change ((atSlot A native S ready s u j.2).map _).bind _=
    ((atSlot A native S ready s u j.2).filter _).bind _
  cases one : atSlot A native S ready s u j.2 with
  | none=>rfl
  | some e=>
    have p:=(atSlot_iff A native S ready s u j.2 e).mp one
    have atRoot : home A (src s e)=u := (port_fst A s e).symm.trans (congrArg Prod.fst p)
    have hi : coarseName c (T.code (T.home (src s e)))=coarseName c (T.code t) := by
      have moved := congrArg
        (fun x : Host J V k => group c (rearrange frame.basis (oldBlock digits x))) atRoot
      exact (frame.homeHigh (src s e)).trans
        (moved.trans (donorHigh A S ready digits Z T frame t j.1))
    change cellLeaf A S ready digits Z T frame s t u (home A (src (!s) e))=_
    rw [←atRoot,cellLeaf_read A S ready digits Z T frame s t e hi]
    by_cases live : falls A S ready Z s t e <;> simp [Option.filter, arrivedLeaf, live]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
