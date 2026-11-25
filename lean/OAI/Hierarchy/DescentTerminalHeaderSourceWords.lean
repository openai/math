import OAI.Hierarchy.DescentTerminalGraphHeaderIssue

namespace OAI
/-! # Both physical header bank reads, including public origin translation, from the native width scans -/
namespace Hierarchy.DescentTerminalHeaderDraft
open DescentKernelHistory hiding Word
open DescentTerminalChipSource DescentTerminalRecipeRows DescentTerminalGraphPositions
open DescentTerminalHeaderGroups DescentTerminalDenseHeader DescentTerminalDenseWindow
open DescentTerminalDenseGraphRead DescentTerminalCableOrder DescentTerminalPorts DescentTerminalPublicGroup
open Computability.BorderVNP.Crossing ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {P Tag:Type} [Fintype P] {deg S p q w rawRows:ℕ} {bits:P→ℕ}
    (N:Network deg P bits) (home:N.Site→Fin S) (native:N.Edge↪Fin (Fintype.card N.Edge))
    (external:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,Boundary N v↪ℕ)
    (r:∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (hp:0<p)
    (birth:∀v,(r v).Node↪ℕ) (hq:0<q)
local notation "L" => order N home native p external nodes ops
local notation "sites" => DescentTerminalBundleRows.site L r hp birth
local notation "Inst" => GroupRow (q:=q) sites
set_option quotPrecheck false in
local notation "gOf" => fun (a : Inst) => (Order.groups L a.1).symm a.2.1
local notation "ipt" => DescentTerminalHeaderGroups.stream (p:=p) N home native external nodes ops q hp
local notation "ept" => DescentTerminalExteriorHeaders.stream (p:=p) (q:=q) N home native external nodes ops
local notation "ix" => DescentTerminalScalarInput.index (q:=q) (rawRows:=rawRows) N home native external nodes ops r hp birth
local notation "fm" => DescentTerminalScalarInput.control N home native external nodes ops r hp birth hq
set_option quotPrecheck false in
local notation "head" => fun (a : Inst) => DescentTerminalScatterRows.srcStart N home native external nodes ops r hp birth a+a.2.2.val

theorem pair_bound (v u:Fin S) : pair v u<S*S := by
  have left:min v.val u.val<S := (Nat.min_le_left ..).trans_lt v.isLt
  have right:max v.val u.val<S:=max_lt v.isLt u.isLt
  have bound:=Nat.mul_le_mul_right S (show min v.val u.val+1≤S by omega)
  rw [Nat.succ_mul] at bound
  unfold pair
  omega

def fieldBank (layout:DescentTerminalDenseHeaderRAM.Layout) (format:Bool) : Bank :=
  if format then layout.control else layout.index
def fieldWord (format:Bool) (a:Inst) : Word w := if format then
    ((formatIndex q p (fm (anchor sites hq a))).val:Word w) else (ix (anchor sites hq a):Word w)

theorem source_words (m:Memory w) (cable outer:DescentTerminalDenseHeaderRAM.Layout)
    (privateRows:∀(t:ℕ) (_:t<S*S) (live:0<pairMass N home t),
      let g:=selected N home native external nodes ops hp t live
      ∀k:Fin (poolBatchCount (Fintype.card (Order.At L g.site g.group)) q),
        let z:DescentTerminalDenseCableFetch.Packet N L q:=⟨g.site,g.other,g.group,g.near,k⟩
        m (cable.index.base+((ipt t).length+k.val))=(DescentTerminalDenseCableFetch.index N home native external nodes ops z:Word w) ∧
        m (cable.control.base+((ipt t).length+k.val))=((formatIndex q p
          (DescentTerminalDenseCableFetch.fmt N home native external nodes ops (Nat.mul_pos hq hp) z)).val:Word w))
    (publicRows:∀(i:Fin S) (g:Order.Group L i) (_:g.val=none) (k:Fin (poolBatchCount (Fintype.card (Order.At L i g)) q)),
      let len:=groupLengths N L i g
      let small:∀z,len z≤p:=fun z=>by dsimp [len,groupLengths];cases ((Order.inGroup L i g).symm z).val <;> exact Nat.min_le_left ..
      m (outer.index.base+((ept i.val).length+k.val))=((DescentTerminalDenseWindow.first len q (DescentTerminalPublicGroup.siteBase N home i) k.val/(q*p):ℕ):Word w) ∧
      m (outer.control.base+((ept i.val).length+k.val))=((formatIndex q p (format len (Nat.mul_pos hq hp) small
        (DescentTerminalPublicGroup.siteBase N home i) k.val)).val:Word w))
    (format:Bool) (a:Inst) {capacity:ℕ} (span:head a<capacity) (room:capacity≤2^w)
    (inner:capacity≤(fieldBank cable format).size) (ext:capacity≤(fieldBank outer format).size) :
    ((gOf a).val.isNone=false→(fieldBank cable format).read m (head a:Word w)=
      fieldWord (rawRows:=rawRows) N home native external nodes ops r hp birth hq format a) ∧
    ((gOf a).val.isNone=true→((if format then 0 else rawRows+2:ℕ):Word w)+(fieldBank outer format).read m
      (head a:Word w)=fieldWord (rawRows:=rawRows) N home native external nodes ops r hp birth hq format a) := by
  have bankRead (b : Bank) (bound : capacity ≤ b.size) :
      b.read m (head a : Word w) = m (b.base + head a) := by
    change m (b.base + (head a : Word w).val % b.size) = _
    rw [Fin.val_cast_of_lt (span.trans_le room), Nat.mod_eq_of_lt (span.trans_le bound)]
  cases kind:(gOf a).val with
  | none=>
    have result:=DescentTerminalScatterRows.exterior (rawRows:=rawRows) N home native external nodes ops r hp birth hq a kind m outer publicRows
    constructor
    · simp
    · intro _
      rw [bankRead _ ext]
      cases format with
      | false => exact result.1
      | true =>
        change (0 : Word w) + m (outer.control.base + head a) = _
        rw [zero_add]
        exact result.2
  | some v=>
    have result:=DescentTerminalScatterRows.interior (rawRows:=rawRows) N home native external nodes ops r hp birth hq a v kind m
      cable (S*S) (pair_bound a.1 v) privateRows
    constructor
    · intro _
      rw [bankRead _ inner]
      cases format with
      | false => exact result.1
      | true => exact result.2
    · simp


end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
