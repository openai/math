import OAI.Hierarchy.DescentReachedFundedCursor
import OAI.Hierarchy.DescentResetOriginClass
import OAI.Hierarchy.DescentResetPrimitivePage
import OAI.Hierarchy.DescentPrimitiveBirthCases

namespace OAI
/-! # Actual funded admission of every new relay and bank node at its installed ordinal -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
set_option quotPrecheck false
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "prog" => b.reset.laneRecipe key m p hp fit
local notation "next" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentResetActorClass DescentCommonHost
open Reached.NodeCells DescentColonies
open scoped Classical Fin.CommRing
variable [Fintype P] (stored : b.Recorded p) (token : a.bit.Tokenized cap.placement.records)
local notation "Y" => b.next
local notation "H" => S.hostSize (i+1)
local notation "Groups" => S.groupCount (i+1)
local notation "prevRank" => (Y).vertex.trans (Fin.castLEEmb (Y).valid.host)
local notation "census" => Census.count (Y).placement (Equiv.refl _) prevRank
local notation "cell" => whereAt Y next order
local notation "residual" => b.reset.k-b.terminals.commonDepth
local notation "cls" => (fun rack : Fin H => (ClosedReset.Window.paidActorAt b rack).elim 0 (fun u=>DescentResetActorClass.indexed b.reset.graph residual u.val))

include stored token in
theorem funded_active {N precision : ℕ} (fits : ∀v,((Y).placement.records v).length<2^precision)
    (x : Block k) (n : Fin N) (h : Fin H) (g : Fin Groups) (atom : NodeOrder.All next) (found : cell x n h g=some atom)
    (birth : (∀old,names atom≠.inl old)) : n.val<(census precision h g x).val:=by
  obtain ⟨position,rank⟩:=(whereAt_some Y next order x n h g atom.1 atom.2).mp found
  have site:siteAt Y x h g=some atom.1:=(siteAt_some Y x h g _).mpr position
  rw [funded_site,site]
  change n.val<(((Y).placement.records atom.1).length:Cell precision).val
  rw [Fin.val_cast_of_lt (fits _)]
  have origin:=reached_node_site b hp whole a atom
  have count:((Y).placement.records atom.1).length=Fintype.card ((next).recipe atom.1).Node:=by
    cases who:names atom with
    | inl old=>exact False.elim (birth old who)
    | inr fresh=>
      rw [who] at origin
      rw [←origin]
      rcases fresh with e|v
      · exact born_recipient_records b hp whole a stored token (.inl (true,_)) (by simp)
      · exact born_recipient_records b hp whole a stored token (.inr v.1) (by simp)
  rw [count,rank]
  exact (order atom.1 atom.2).isLt

include stored token in
theorem funded_blank {N precision : ℕ} (fits : ∀v,((Y).placement.records v).length<2^precision)
    (x : Block k) (n : Fin N) (h : Fin H) (g : Fin Groups) (hole : cell x n h g=none) :
    (census precision h g x).val≤n.val:=
  funded_cursor Y next order fits (recipient_records_le b hp whole a stored token) x n h g hole

omit [Fintype P] in
theorem class_of_node {N : ℕ} (x : Block k) (n : Fin N) (h : Fin H) (g : Fin Groups) (atom : NodeOrder.All next)
    (found : cell x n h g=some atom) : cls h=originClass b hp whole a (names atom):=by
  have coordinate₀:=((whereAt_some Y next order x n h g atom.1 atom.2).mp found).1
  have wh:(((Y).vertex ((Y).placement.pos atom.1).2).castLE (Y).valid.host)=h:=congrArg Prod.fst coordinate₀
  rw [←wh]
  exact checkpoint_origin_index b hp whole a (Y).valid.host atom

theorem smallIndex (val n res : ℕ) (small : val≤5) : ((val:Cell (indexBits n res))).val=val:=by
  apply Fin.val_cast_of_lt
  exact (show val<6+2*(2^res*2^n) by omega).trans_le (Nat.le_pow_clog (by decide) _)

omit [Fintype P] in
theorem bank_class_not_relay (v : NodeOrder.Global prog) : (originClass b hp whole a (.inr (.inr v))).val≠2:=by
  rcases v with ⟨⟨⟨s,g|t⟩,site⟩,op⟩
  · rcases site with ⟨u,(_|_)|i⟩
    · change (6+_)≠2
      omega
    · change ((0:Cell (indexBits _ _))).val≠2
      simp
    · change ((4:Cell (indexBits _ _))).val≠2
      rw [show (4:Cell (indexBits b.reset.n residual)).val=4 from smallIndex 4 _ _ (by decide)]
      decide
  · change ((5:Cell (indexBits _ _))).val≠2
    rw [show (5:Cell (indexBits b.reset.n residual)).val=5 from smallIndex 5 _ _ (by decide)]
    decide

include stored token in
theorem relay_at_slot {N precision : ℕ} (fits : ∀v,((Y).placement.records v).length<2^precision)
    (x : Block k) (n : Fin N) (h : Fin H) (g : Fin Groups) :
    (if n.val<(census precision h g x).val ∧ (cls h).val=2 then (1:Cell 1) else 0)=
      (cell x n h g).elim 0 (fun a=>match names a with | .inr (.inl _)=>1 | _=>0):=by
  cases found:cell x n h g with
  | none=>simp [Nat.not_lt_of_ge (funded_blank b hp whole a earlier stored token fits x n h g found)]
  | some atom=>
    rw [class_of_node b hp whole a earlier x n h g atom found]
    cases who:names atom with
    | inl old=>
      have kind:(originClass b hp whole a (.inl old)).val=1:=smallIndex 1 _ _ (by decide)
      simp [kind,who]
    | inr fresh=>
      have live:=funded_active b hp whole a earlier stored token fits x n h g atom found (by intro old;rw [who];simp)
      rcases fresh with e|v
      · have kind:(originClass b hp whole a (.inr (.inl e))).val=2:=smallIndex 2 _ _ (by decide)
        simp [live,kind,who]
      · simp [bank_class_not_relay b hp whole a v,who]

include stored token in
/-- Physical classifier and funded page decide the three non-bank arms, including
nullary records and all vacant argument headers. Only the original bank-local
rotation or equality tag is evaluated on the fresh arm. -/
theorem born_at_slot (z₀ : DescentPrimitiveBirth.Layout) (kindBits : z₀.classBits=indexBits b.reset.n residual)
    (fits : ∀v,((Y).placement.records v).length<2^z₀.paidBits) (x : Block k) (n : Fin z₀.nodes) (h : Fin H) (g : Fin Groups)
    (spans : Fin z₀.arguments→Cell z₀.spanBits) (roots : Fin z₀.roots→Cell z₀.rootBits) :
    let κ:Cell z₀.classBits:=Fin.cast (congrArg (fun j : ℕ=>2^j) kindBits.symm) (cls h)
    z₀.raw n κ (census z₀.paidBits h g x) spans roots=
      (cell x n h g).elim 0 (fun ptr=>match names ptr with
        | .inl _=>0 | .inr (.inl _)=>0
        | .inr (.inr v)=>
          let code:Cell z₀.classBits:=Fin.cast (congrArg (fun j : ℕ=>2^j) kindBits.symm) (originClass b hp whole a (.inr (.inr v)))
          (z₀.rootId code).elim (z₀.tag code (z₀.extra spans)) roots):=by
  dsimp only
  cases found:cell x n h g with
  | none=>exact z₀.blank n _ _ spans roots (funded_blank b hp whole a earlier stored token fits x n h g found)
  | some atom=>
    have actor := class_of_node b hp whole a earlier x n h g atom found
    dsimp only at actor
    rw [actor]
    simp only [Option.elim_some]
    cases who:names atom with
    | inl u=>
      apply z₀.primary
      exact smallIndex 1 _ _ (by decide)
    | inr fresh=>
      rcases fresh with e|v
      · apply z₀.relay_zero
        exact smallIndex 2 _ _ (by decide)
      · have yes:=funded_active b hp whole a earlier stored token fits x n h g atom found (by intro old;rw [who];simp)
        simp [DescentPrimitiveBirth.Layout.raw,DescentPrimitiveBirth.Layout.admitted,yes]

end
end Hierarchy.DescentPrimitivePalette

end OAI
