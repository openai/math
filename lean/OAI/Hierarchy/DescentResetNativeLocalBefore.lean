import OAI.Hierarchy.DescentResetWindowSiteBefore
import OAI.Hierarchy.DescentResetWindowStemOrder

namespace OAI
/-! # The full bounded local word for the actual reset parent's original order -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open scoped Classical BigOperators
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Kind" => (Bool×(old).graph.Edge) ⊕ ((Z).Fallback ⊕ ((R).Contact ⊕ PrivateOccurrence B))
local notation "Short" => DescentResetCompactParent.Word H r Y L (A).cap slots pcCap
local notation "sitely" => Layout.append (goodLayout U (Z).k) (termLayout U (Z).k Y)
local notation "originalSite" => DescentResetCableSlots.siteDigits (R) vertex (T).code okCode
local notation "direct" => directDigits (R) vertex (T).code okCode height (T).bookHeight
local notation "privateCode" => kernelDigits (R) vertex (T).code okCode height (T).bookHeight (Z).graph (Z).positive (Z).pay (Z).circuit d
local notation "original" => originParts (R) vertex (T).code okCode height (T).bookHeight (Z).graph (Z).positive (Z).pay (Z).circuit d birth
local notation "wholeLayout" => originalLayout (∑e,B.count e) U (Z).k Y height pcCap
local notation "ordinal" => (Z).installedResetOrdinal T vertex birth
local notation "ticket" => outgoingSlot A S input.valid input.order

def directDigit (c : (R).Contact) : Fin slots :=
  match leftSocket (R) c with
  | .inl a=>(paidSlot (R) a).2.castLE (Nat.le_max_left ..)
  | .inr a=>(leaf (R) height (T).bookHeight false a.1 a.2).castLE (Nat.le_max_right ..)

def namedWord (u : Host) : Kind→Short
  | .inl (s,j)=>
    let a:=beforeStem B j
    let bound:=compactStem_room B u a
    .inl (finTwoEquiv.symm s,⟨compactStemSource B u a,bound.1⟩,ticket a,⟨a.2.val,bound.2.2⟩)
  | .inr (.inl t)=>.inr (.inl (siteWord B u (.inr t)))
  | .inr (.inr (.inl c))=>.inr (.inr (.inl (siteWord B u ((R).owner false c),directDigit B c)))
  | .inr (.inr (.inr p))=>.inr (.inr (.inr (finTwoEquiv.symm p.1.1,siteWord B u p.1.2,(privateTicket B p).2.2)))

def nativeWord (u : Host) (e : (coarse).graph.Edge) : Short := namedWord B u (motherNames B e)

private def tagRoot : Kind→Option (R).Site
  | .inl _=>none
  | .inr (.inl t)=>some (.inr t)
  | .inr (.inr (.inl c))=>some ((R).owner false c)
  | .inr (.inr (.inr p))=>some p.1.2

private theorem source_tag (e : (coarse).graph.Edge) : originSite B e=tagRoot B (motherNames B e) := by
  unfold originSite
  rcases motherNames B e with stem|t|c|⟨⟨s,g₀⟩,j⟩ <;> rfl

private theorem direct_comparison (c b : (R).Contact) :
    ((sitely).before (originalSite ((R).owner false c)) (originalSite ((R).owner false b)) ∨
      originalSite ((R).owner false c)=originalSite ((R).owner false b) ∧ directDigit B c<directDigit B b) ↔
      (directLayout U (Z).k Y height).before (direct c) (direct b) := by
  rcases c with c|c <;> rcases b with b|b
  · change (_ ∨ Sum.inl (β:=(termLayout U (Z).k Y).Value) _=Sum.inl _ ∧ _) ↔ _
    rw [Sum.inl.injEq]; rfl
  · change (True ∨ _) ↔ True
    simp
  · change (False ∨ Sum.inr _=Sum.inl _ ∧ _) ↔ False
    simp
  · change (_ ∨ Sum.inr (α:=(goodLayout U (Z).k).Value) _=Sum.inr _ ∧ _) ↔ _
    rw [Sum.inr.injEq]; rfl

private theorem kernel_comparison (p q₀ : PrivateOccurrence B) :
    (finTwoEquiv.symm p.1.1<finTwoEquiv.symm q₀.1.1 ∨
     finTwoEquiv.symm p.1.1=finTwoEquiv.symm q₀.1.1 ∧
      ((sitely).before (originalSite p.1.2) (originalSite q₀.1.2) ∨
       originalSite p.1.2=originalSite q₀.1.2 ∧ (privateTicket B p).2.2<(privateTicket B q₀).2.2)) ↔
      (kernelLayout U (Z).k Y pcCap).before (privateCode p.1 p.2) (privateCode q₀.1 q₀.2) := by
  change (_ ∨ _ ∧ (_ ∨ _ ∧ _)) ↔
    ((_ < _ ∨ _ = _ ∧ (sitely).before (originalSite p.1.2) (originalSite q₀.1.2)) ∨
    (finTwoEquiv.symm p.1.1,originalSite p.1.2)=(finTwoEquiv.symm q₀.1.1,originalSite q₀.1.2) ∧
      (privateTicket B p).2.2<(privateTicket B q₀).2.2)
  rw [Prod.mk.injEq];tauto

/-- The original mathematical sparse ordinal is compared using just the
shared base depth, one local coarse-zero flag, and two finite short words. -/
theorem nativeLocalBefore (age : 0 < i) (sorted : SourceSorted W input.order)
    (u : Host) (x y : Local (blocks B) u) :
    DescentResetCompactParent.Word.before (T).commonDepth (zeroCoarse B u) (nativeWord B u x.val) (nativeWord B u y.val) ↔
      ordinal x.val<ordinal y.val := by
  refine Iff.trans ?_ ((Z).installed_parts_before T vertex birth x.val y.val)
  change DescentResetCompactParent.Word.before (T).commonDepth (zeroCoarse B u)
    (namedWord B u (motherNames B x.val)) (namedWord B u (motherNames B y.val)) ↔
    (wholeLayout).before (original (motherNames B x.val)) (original (motherNames B y.val))
  generalize hx : motherNames B x.val=p
  generalize hy : motherNames B y.val=q₀
  have scopes {a b : (R).Site} (ia : tagRoot B p=some a) (ib : tagRoot B q₀=some b) :
      (siteBefore B u a b ↔ (sitely).before (originalSite a) (originalSite b)) ∧
      ((¬siteBefore B u a b ∧ ¬siteBefore B u b a) ↔ originalSite a=originalSite b) := by
    have atX:=(source_tag B x.val).trans ((congrArg (tagRoot B) hx).trans ia)
    have atY:=(source_tag B y.val).trans ((congrArg (tagRoot B) hy).trans ib)
    exact ⟨site_before B u x y a b atX atY,site_tie B u x y a b atX atY⟩
  rcases p with a|a|a|a <;> rcases q₀ with b|b|b|b
  · obtain ⟨s,j⟩:=a
    obtain ⟨t,l⟩:=b
    change (finTwoEquiv.symm s<finTwoEquiv.symm t ∨ finTwoEquiv.symm s=finTwoEquiv.symm t ∧
        compactStemBefore B u (beforeStem B j) (beforeStem B l)) ↔
      (finTwoEquiv.symm s<finTwoEquiv.symm t ∨ finTwoEquiv.symm s=finTwoEquiv.symm t ∧ birth j<birth l)
    by_cases eqn : s=t
    · subst t
      have ex : x.val=stemParent B (s,j):=(Equiv.eq_symm_apply _).2 hx
      have ey : y.val=stemParent B (s,l):=(Equiv.eq_symm_apply _).2 hy
      have cmp:=stem_before_compact B age sorted u s j l (ex ▸ x.property.2) (ey ▸ y.property.2)
      rw [stem_ordinal B s j,stem_ordinal B s l,Nat.add_lt_add_iff_right,
        ←beforeStem_code B j,←beforeStem_code B l] at cmp
      simpa using cmp.symm
    · have neq : finTwoEquiv.symm s≠finTwoEquiv.symm t:=fun h=>eqn (finTwoEquiv.symm.injective h)
      simp [neq]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (scopes (a:=.inr a) (b:=.inr b) rfl rfl).1
  · rfl
  · rfl
  · rfl
  · rfl
  · have cert:=scopes (a:=(R).owner false a) (b:=(R).owner false b) rfl rfl
    change (siteBefore B u _ _ ∨ (¬siteBefore B u _ _ ∧ ¬siteBefore B u _ _) ∧ directDigit B a<directDigit B b) ↔ _
    rw [cert.2,cert.1]
    exact direct_comparison B a b
  · rfl
  · rfl
  · rfl
  · rfl
  · have cert:=scopes (a:=a.1.2) (b:=b.1.2) rfl rfl
    change (_ < _ ∨ _ = _ ∧ (siteBefore B u _ _ ∨ (¬siteBefore B u _ _ ∧ ¬siteBefore B u _ _) ∧
      (privateTicket B a).2.2<(privateTicket B b).2.2)) ↔ _
    rw [cert.2,cert.1]
    exact kernel_comparison B a b

theorem nativeLocalBefore_path {W₀ : MarkedWorld F d P bits} {start z₀ D₀ : ℕ}
    {first : Reached W₀ G q ε S k start z₀ D₀ w hist} (path : Chronology.Path first input)
    (ordinary : path.ordinaryOnly) (elapsed : start < i) (u : Host) (x y : Local (blocks B) u) :
    DescentResetCompactParent.Word.before (T).commonDepth (zeroCoarse B u) (nativeWord B u x.val) (nativeWord B u y.val) ↔
      ordinal x.val<ordinal y.val :=
  nativeLocalBefore B (Nat.zero_le start |>.trans_lt elapsed) (path.ordinary_sorted ordinary elapsed) u x y

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
