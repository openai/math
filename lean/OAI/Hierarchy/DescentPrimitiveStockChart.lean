import OAI.Hierarchy.DescentOrdinaryPaletteGather

namespace OAI
/-! Coordinate readback when the reached calendar identifies the primitive host and socket layouts. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup
noncomputable section
variable {L T:Layout} (chart:L=T) (stock:L.Stock)

theorem chart_previous (x:Fin T.blocks) (h:Fin T.hosts) (g:Fin T.oldGroups) (j:Fin T.oldNodes):
    ((encode T.primitiveBits T.oldNodes).symm ((chart ▸ stock : T.Stock).previous x h g) j).val=
      ((encode L.primitiveBits L.oldNodes).symm
        (stock.previous (x.cast (congrArg blocks chart.symm)) (h.cast (congrArg Layout.hosts chart.symm))
          (g.cast (congrArg oldGroups chart.symm))) (j.cast (congrArg Layout.oldNodes chart.symm))).val:=by
  subst T
  rfl

theorem chart_newborn (x:Fin T.blocks) (t:Fin T.capacity) (party:Fin 6) (h:Fin T.hosts) (g:Fin T.oldGroups):
    ((chart ▸ stock : T.Stock).newborn (T.bornIndex x t party) h g).val=
      (stock.newborn (L.bornIndex (x.cast (congrArg blocks chart.symm))
        (t.cast (congrArg Layout.capacity chart.symm)) party)
        (h.cast (congrArg Layout.hosts chart.symm)) (g.cast (congrArg oldGroups chart.symm))).val:=by
  subst T
  rfl

theorem chart_origin (x:Fin T.blocks) (h:Fin T.successors) (g:Fin T.groups):
    ((chart ▸ stock : T.Stock).origin x h g).val=
      (stock.origin (x.cast (congrArg blocks chart.symm))
        (h.cast (congrArg successors chart.symm)) (g.cast (congrArg Layout.groups chart.symm))).val:=by
  subst T
  rfl

theorem chart_peer (h:Fin T.hosts) (p:Fin T.ports):
    ((chart ▸ stock : T.Stock).next h p).map Fin.val=
      (stock.next (h.cast (congrArg Layout.hosts chart.symm)) (p.cast (congrArg ports chart.symm))).map Fin.val:=by
  subst T
  rfl

theorem option_fin_eq {n:ℕ} {a b:Option (Fin n)} (values:a.map Fin.val=b.map Fin.val):a=b:=by
  cases a <;> cases b <;> simp_all [Fin.ext_iff]

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI
