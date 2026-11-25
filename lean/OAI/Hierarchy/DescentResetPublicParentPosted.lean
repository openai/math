import OAI.Hierarchy.DescentResetOriginalPosted
import OAI.Hierarchy.DescentResetActualSourcePull
import OAI.Hierarchy.DescentResetPublicParentRaster
import OAI.Hierarchy.DescentResetPublicParentStatics

namespace OAI
/-! # Direct and trunk words on the same original slots used by source-ticket selection -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetPublicParentWord DescentDenseHostOrder
open DescentResetLocalRoster DescentResetParentCodec DescentSIMDLookup DescentPackedZip
open DescentResetMixedWordRAM.OriginalDate DescentResetMixedWordRAM.OriginalBooks DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "Ht" => GroupStage.depthBound D n f g
local notation "s" => publicShape B
local notation "X" => 2^k
local notation "J" => (contactCount B+1)
local notation "K" => totalLocal B
local notation "grp" => S.groupCount (i+1)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "pal" => DescentDenseHostOrder.roster (Z).graph (s).depth Ht

def publicShelf : Fin J↪Fin K where
  toFun j:=⟨stemsCount B+j.val,by have cut:=j.isLt;unfold totalLocal;omega⟩
  inj' a b eqn:=Fin.ext (Nat.add_left_cancel (congrArg Fin.val eqn))

def publicKind (j : Fin J) : Fin 2:=Fin.cases 0 (fun _=>1) j
def publicFn (mode : Fin 2) : WordFn :=
  if mode=0 then trunkWord (Z).graph (s).halo (s).depth (s).span (s).cap (s).sockets (s).program Ht else fun live atZero halo arg=>directWord s Ht live atZero (halo-1) arg

theorem publicShelf_trunk : publicShelf B 0=trunkCandidate B:=Fin.ext (Nat.add_zero _)
theorem publicShelf_contact (t : Fin (contactCount B)) : publicShelf B t.succ=contactShelfIndex B t:=by
  apply Fin.ext
  change stemsCount B+(t.val+1)=stemsCount B+1+t.val
  omega

variable {H M mb zb ub tb ob ww : ℕ}
def publicDate (H M mb zb ub tb ob header original : ℕ) (E : Fields X J) : Date X J K:=
  ⟨publicShelf B,publicKind B,header,original,H*chunks grp M,M,mb,zb,ub,tb,ob,publicFn B,E⟩

/-- The last two inputs are strictly earlier observations: physical halo and raw receiver
palette on the trunk, physical halo and reciprocal prior sender ticket on a live contact. -/
theorem original_publics (rack : Fin H→Option B.next.V) (header original : ℕ) (E : Fields X J) (m : Memory ww)
    (x : Fin X) (j : Fin J) (halo : Fin H→Fin grp→Cell ub) (arg : Fin H→Fin grp→Cell tb)
    (mbpos : 0< mb) (zbpos : 0<zb)
    (room : (publicDate B H M mb zb ub tb ob header original E).Room ww)
    (metaRead : Source (E.meta (finProdFinEquiv (x,j))) (fun v g=>DescentResetFieldAssembler.raw mb (actualMeta B rack x (publicShelf B j) v g)) M m)
    (zeroRead : Source (E.zero (finProdFinEquiv (x,j))) (fun (_ : Fin H) (g : Fin grp)=>((decide (g.val=0 ∧ x.val=0)).toNat:Cell zb)) M m)
    (haloRead : Source (E.halo (finProdFinEquiv (x,j))) halo M m)
    (argRead : Source (E.arg (finProdFinEquiv (x,j))) arg M m)
    (trunk : j=0→∀v h,rack v=some h→∀g,
      (halo v g).val=haloNumber B ((g,h),x) (receiverRoot B ((g,h),x)).1 ∧
      (arg v g).val=((Z).rawHostRank T vertex h).val%(pal).card)
    (contact : ∀c : Fin (contactCount B),j=c.succ→∀v h,rack v=some h→∀g,
      ∀(a : (R).Contact) (live : active (blocks B) ((g,h),x) (contactParent B a)),
      contactDigit B ((g,h),x) ⟨a,live⟩=c→∀e : (old).graph.Edge,(R).contact e=a→
        (halo v g).val=haloNumber B ((g,h),x) ((Z).rootVertex T ((R).owner false a))+1 ∧ (arg v g).val=(Z).senderJoint T false a) :
    let L:=publicDate B H M mb zb ub tb ob header original E
    Source (.lookup (L.output x j) .row) (fun v g=>(actualParentNumber B rack x (publicShelf B j) v g:Cell ob)) M (L.dst m):=by
  intro L
  have miss (q : Fin 2) : publicFn B q 0 0 0 0=0:=by
    by_cases eqn : q=0 <;>simp [publicFn,eqn,trunkWord,directWord]
  have rawRead:=L.posted room m x j rfl (actualMeta B rack x (publicShelf B j))
    (fun (_ : Fin H) (g : Fin grp)=>decide (g.val=0 ∧ x.val=0)) halo arg mbpos zbpos (miss _) metaRead zeroRead haloRead argRead
  have eqn (v : Fin H) (g : Fin grp) :
    publicFn B (publicKind B j) (actualMeta B rack x (publicShelf B j) v g).live.toNat (decide (g.val=0 ∧ x.val=0)).toNat
      (halo v g).val (arg v g).val=actualParentNumber B rack x (publicShelf B j) v g:=by
    cases present : rack v with
    | none=>
      by_cases first : publicKind B j=0 <;>simp [actualMeta,actualParentNumber,present,Meta.blank,publicFn,first,trunkWord,directWord]
    | some h=>
      induction j using Fin.cases with
      | zero=>
        obtain ⟨hh,aa⟩:=trunk rfl v h present g
        have exactWord:=trunk_raster_word B ((g,h),x)
        simp only [publicKind,Fin.cases_zero,publicFn,publicShelf_trunk,actualMeta,actualParentNumber,present,
          Option.elim_some,hh,aa]
        rw [public_zero B ((g,h),x)] at exactWord
        exact exactWord
      | succ j=>
        have exactWord:=contact_raster_word B ((g,h),x) j ((halo v g).val-1) (arg v g).val (by
          intro a active key e found
          obtain ⟨h₁,h₂⟩:=contact j rfl v h present g a active key e found
          exact ⟨by omega,h₂⟩)
        simpa [publicKind,publicFn,publicShelf_contact,actualMeta,actualParentNumber,present,public_zero] using exactWord
  change Source (.lookup (L.output x j) .row) (fun v g=>(publicFn B (publicKind B j)
    (actualMeta B rack x (publicShelf B j) v g).live.toNat (decide (g.val=0 ∧ x.val=0)).toNat
    (halo v g).val (arg v g).val:Cell ob)) M (L.dst m) at rawRead
  simpa only [eqn] using rawRead

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
