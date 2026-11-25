import OAI.Hierarchy.DescentPhysicalFallbackPanel
import OAI.Hierarchy.DescentRotorInstalledMatrix

namespace OAI
/-! # Stored signed donors for every public reset half-stem at its terminal -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
local notation "Q" => A.z*G.b
local notation "Wold" => W.granular A.grainCount Q (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le ..)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "theSite" => DescentIssuedFallbackPanel.endSite A


/-- Half-stems on either polarity use the actual signed old face at that end. -/
def stemRows (s : Bool) (t : Z.Fallback) : Fin (2^(m-c)*(2*A.cap))→Option E :=
  fun j=>panel A native S ready digits frame.basis fits s (frame.host.symm (T.code t).1)
    (selectedRoot A S ready Z T t) (fun e=>T.home (theSite s e)=t) (finProdFinEquiv.symm j)

theorem stem_slot_read (s : Bool) (t : Z.Fallback) (e : E) (atTerminal : T.home (theSite s e)=t) :
    stemRows A S ready digits native Z T frame s t (finProdFinEquiv
       (localAddress A native S ready digits frame.basis s e))=some e := by
  unfold stemRows
  rw [Equiv.symm_apply_apply]
  apply panel_at A native S ready digits frame.basis fits s (frame.host.symm (T.code t).1)
    (selectedRoot A S ready Z T t) (fun x=>T.home (theSite s x)=t)
  · intro x same
    constructor
    · apply frame.host.injective
      exact (frame.homeHost _).symm.trans ((congrArg (fun t=> (T.code t).1) same).trans (frame.host.apply_symm_apply _).symm)
    · change group c (rearrange frame.basis (StarKeys.filled W.graph A.pos A.block digits (theSite s x)))=coarseName c (T.code t)
      exact (frame.homeHigh _).symm.trans (congrArg (fun t=>coarseName c (T.code t)) same)
  · exact atTerminal

def stemRoster (s : Bool) (t : Z.Fallback) :
    {e : E // T.home (theSite s e)=t} ↪ Fin (2^(m-c)*(2*A.cap)) where
  toFun e:=finProdFinEquiv (localAddress A native S ready digits frame.basis s e.val)
  inj' x y same:=by
    apply Subtype.ext
    apply Option.some.inj
    exact (stem_slot_read A S ready digits native Z T frame s t x.val x.property).symm.trans
      ((congrArg (stemRows A S ready digits native Z T frame s t) same).trans
        (stem_slot_read A S ready digits native Z T frame s t y.val y.property))

theorem stemRoster_read (s : Bool) (t : Z.Fallback) (x : {e : E // T.home (theSite s e)=t}) :
    stemRows A S ready digits native Z T frame s t (stemRoster A S ready digits native Z T frame s t x)=some x.val :=
  stem_slot_read A S ready digits native Z T frame s t x.val x.property

/-- At the bank endpoint all stems owned by the same good or exceptional
root still fit one remixed donor group of signed old faces. -/
def bankRoot (owner : (R).Site) : V×Block c :=
  match owner with
  | .inl root=>(frame.host.symm root.val.1,Z.rootBlock T (.inl root))
  | .inr t=>(frame.host.symm (T.code t).1,selectedRoot A S ready Z T t)

def bankStemRows (s : Bool) (owner : (R).Site) : Fin (2^(m-c)*(2*A.cap))→Option E :=
  fun j=>panel A native S ready digits frame.basis fits s (bankRoot A S ready digits Z T frame owner).1
    (bankRoot A S ready digits Z T frame owner).2 (fun e=>(R).site s ((R).input s e)=owner) (finProdFinEquiv.symm j)

theorem bank_stem_slot_read (s : Bool) (owner : (R).Site) (e : E) (member : (R).site s ((R).input s e)=owner) :
    bankStemRows A S ready digits native Z T frame s owner
      (finProdFinEquiv (localAddress A native S ready digits frame.basis s e))=some e := by
  unfold bankStemRows
  rw [Equiv.symm_apply_apply]
  apply panel_at A native S ready digits frame.basis fits s _ _ (fun u=>(R).site s ((R).input s u)=owner)
  · intro u atRoot
    have fitsRoot:=((R).align s u).symm.trans atRoot
    cases owner with
    | inl root=>exact rotorCellsAt A S ready digits Z T frame s root u fitsRoot
    | inr t=>exact falls_parameters A S ready digits Z T frame fitsRoot
  · exact member

def bankStemRoster (s : Bool) (owner : (R).Site) :
    {e : E // (R).site s ((R).input s e)=owner} ↪ Fin (2^(m-c)*(2*A.cap)) where
  toFun e:=finProdFinEquiv (localAddress A native S ready digits frame.basis s e.val)
  inj' x y eqn:=by
    apply Subtype.ext
    apply Option.some.inj
    exact (bank_stem_slot_read A S ready digits native Z T frame s owner x.val x.property).symm.trans
      ((congrArg (bankStemRows A S ready digits native Z T frame s owner) eqn).trans
        (bank_stem_slot_read A S ready digits native Z T frame s owner y.val y.property))

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
