import OAI.Hierarchy.DescentOrdinaryPalettePosted
import OAI.Hierarchy.DescentOperandLaneRead
import OAI.Hierarchy.DescentPaddedRasterValue

namespace OAI
/-! The physical candidate pool commutes with the old group shuffle and rectangular host padding. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentOrdinaryRasterReturn DescentScalarBookReshape
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {H J : ℕ} (L : Layout) (S : L.Stock) (includeHost : H≤L.hosts)
    (group : Fin L.oldGroups→Fin J)
    (old : Fin L.blocks→Fin H→Fin J→Cell (L.primitiveBits*L.oldNodes))
    (borne : Fin L.blocks→Fin L.capacity→Fin 6→Fin H→Fin J→Cell L.primitiveBits)
    (near : Fin H→Fin L.ports→Option (Fin H))
local notation "D" => L.degree
local notation "k" => L.k
local notation "K" => L.oldNodes
local notation "cap" => L.capacity

def oldPool (h : Fin H) (g : Fin J) :=encode L.primitiveBits L.candidates (fun z=>
  (near h (bookRoot D k K cap z)).elim 0 (fun t=>
    item old borne (bookBlock D k K cap z) (bookItem D k K cap z) t g))

theorem pool_on (prior : ∀x h g,S.previous x (h.castLE includeHost) g=old x h (group g))
    (fresh : ∀x p a h g,S.newborn (L.bornIndex x p a) (h.castLE includeHost) g=borne x p a h (group g))
    (adj : ∀h p,S.next (h.castLE includeHost) p=(near h p).map (Fin.castLE includeHost))
    (h : Fin H) (g : Fin L.oldGroups) :
    S.pool (h.castLE includeHost) g=oldPool L old borne near h (group g):=by
  apply congrArg (encode L.primitiveBits L.candidates)
  funext z
  let root : Fin L.ports := bookRoot D k K cap z
  let block : Fin L.blocks := bookBlock D k K cap z
  let slot : Fin (K + cap*6) := bookItem D k K cap z
  let get (t : Fin L.hosts) := item S.previous (fun x port who => S.newborn (L.bornIndex x port who))
    block slot t g
  change (S.next (h.castLE includeHost) root).elim 0 get =
    (near h root).elim 0 (fun t => item old borne block slot t (group g))
  calc
    _ = ((near h root).map (Fin.castLE includeHost)).elim 0 get :=
      congrArg (fun o : Option (Fin L.hosts) => o.elim 0 get) (adj h root)
    _ = _ := ?_
  cases peer : near h root with
  | none => rfl
  | some t =>
    simp only [Option.map_some,Option.elim_some,get,item]
    cases tag : finSumFinEquiv.symm slot with
    | inl n=>simp only [Sum.elim_inl,prior]
    | inr n=>simp only [Sum.elim_inr,fresh]

theorem book_on (prior : ∀x h g,S.previous x (h.castLE includeHost) g=old x h (group g))
    (fresh : ∀x p a h g,S.newborn (L.bornIndex x p a) (h.castLE includeHost) g=borne x p a h (group g))
    (adj : ∀h p,S.next (h.castLE includeHost) p=(near h p).map (Fin.castLE includeHost))
    (x : Fin L.blocks) (v : Fin (H*L.lows)) (g : Fin L.groups) :
    S.onBlock x (DescentOrdinaryRasterReturn.widen includeHost v) g=
      book (fun _:Fin L.lows=>fun (h:Fin H) (j:Fin L.oldGroups)=>oldPool L old borne near h (group j)) x v g:=by
  simp only [Stock.onBlock,book,DescentOrdinaryRasterReturn.endpoints]
  exact pool_on L S includeHost group old borne near prior fresh adj _ _

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI
