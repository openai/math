import OAI.Hierarchy.DescentResetParentOriginBlocks
import OAI.Hierarchy.DescentResetCompactParent

namespace OAI
/-! # Comparing two observed parent roots at a physical receiver -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentChosenRouter
open scoped Classical
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "r" => (Z).k-(T).commonDepth
local notation "valid" => fun t=>((T).codeLegal t).2
local notation "siteLayout" => Layout.append (goodLayout (Fintype.card input.V) (Z).k)
  (termLayout (Fintype.card input.V) (Z).k Y)
local notation "original" => DescentResetCableSlots.siteDigits (R) vertex (T).code valid

def haloDigit (u : Host) (v : (Z).V) : Fin H :=
  ⟨haloNumber B u v,Nat.lt_succ_of_le (haloNumber_room B u v)⟩

def siteWord (u : Host) : (R).Site→SiteWord H r Y
  | .inl a=>.inl (haloDigit B u a.val.1,(Z).goodLabel T a)
  | .inr t=>.inr (haloDigit B u ((T).code t).1,(Z).fallLabel T t,optional ((T).code t).2.2)

def zeroCoarse (u : Host) := decide ((receiverRoot B u).2.val=0)

def siteBefore (u : Host) (a b : (R).Site) : Prop :=
  DescentResetCompactParent.siteBefore (T).commonDepth (zeroCoarse B u) (siteWord B u a) (siteWord B u b)

theorem site_before (u : Host) (x y : Local (blocks B) u) (a b : (R).Site)
    (atX : originSite B x.val=some a) (atY : originSite B y.val=some b) :
    siteBefore B u a b ↔ (siteLayout).before (original a) (original b) := by
  have hosts {x : Local (blocks B) u} {a : (R).Site} (present : originSite B x.val=some a) :
      originHost B x.val=some ((Z).rootVertex T a) := by rw [←originSite_host,present]; rfl
  have order:=origin_host_compare B u x y _ _ (hosts atX) (hosts atY)
  have common:=origin_intervals_same B u x y a b atX atY
  cases a with
  | inl a=>
    cases b with
    | inl b=>exact (Z).base_local_before T vertex a b _ _ order.1 order.2 common
    | inr b=>rfl
  | inr a=>
    cases b with
    | inl b=>rfl
    | inr b=>
      have yes:=(Z).terminal_local_before T vertex a b _ _ order.1 order.2 common
      have high : DescentChosenRouter.coarseName (T).commonDepth ((T).code a)=(receiverRoot B u).2.val :=
        origin_interval_high B u x (.inr a) atX
      rw [high] at yes
      exact yes

theorem site_tie (u : Host) (x y : Local (blocks B) u) (a b : (R).Site)
    (atX : originSite B x.val=some a) (atY : originSite B y.val=some b) :
    (¬siteBefore B u a b ∧ ¬siteBefore B u b a) ↔ original a=original b := by
  rw [site_before B u x y a b atX atY,site_before B u y x b a atY atX,Layout.before_iff,Layout.before_iff]
  exact ⟨fun h=>(siteLayout).place.injective (le_antisymm (le_of_not_gt h.2) (le_of_not_gt h.1)),
    fun h=>by rw [h]; simp⟩

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
