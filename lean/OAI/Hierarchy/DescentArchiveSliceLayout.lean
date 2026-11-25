import OAI.Hierarchy.DescentTerminalSliceClass
import OAI.Hierarchy.DescentResetPrimitiveWords
import OAI.Hierarchy.DescentTerminalRoleChronology
import OAI.Hierarchy.DescentTerminalResetTrunkRole
import OAI.Hierarchy.DescentTerminalResetRoleWords

namespace OAI
/-! # The primitive tag determines the partition of the operand slices along an issued path -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentKernelHistory DescentPrimitivePalette
open DescentRouterBank DescentNamedContact DescentContactTree DescentResetTrunks DescentChosenRouter DescentRotor DescentResetGates DescentBundleHistory
open DescentLocalArchiveOrder DescentTerminalCombinedRole DescentResetAttachments Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {s Z : ℕ} {op : RotorSpec} {dict : Label G s Z op→List (List Bool)→F}
    {B : BitDescription W}

def Layouts (code : Encoding (Label G s Z op) dict B) (sh : WorldShape p R B) : Prop :=
  ∀x : NodeOrder.All B,(classify G p s (code.atNode x)).correct (sh.nodeFields x)

theorem follow_layouts (code : Encoding (Label G s Z op) dict B) (sh : WorldShape p R B)
    (hp : 0<p) {w : ℕ} (hw : 0<w) (divides : p∣w) (n : Normalize W) (cuts : Normalize.CutsEqual w n)
    (previous : Layouts code sh) :
    Layouts (code.follow n) (WorldShape.follow hp hw divides n cuts sh) := by
  intro x
  rw [Encoding.follow_at,WorldShape.follow_fields]
  exact previous _

section Install
variable {H Q Y : Type} [Fintype H] [Fintype Q] {L d' : ℕ}
    (code : Encoding (Label G s Z op) dict B) (sh : WorldShape p R B) (hp : 0<p) (one : 1≤R)
    (home : W.graph.Site→H) (grp : Bool→W.graph.Edge→Q) (hub : H→Bool)
    {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (board : Network d' (Bool×Q) (publicWidth grp w))
    (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L)
    (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted)
    (device : ∀v,Shape p (prog v)) (bound : ∀v u j g,((device v).chunk u j g).stride≤R)
    (widths : ∀e,p∣board.width e)
    (relayRead : dict (.inr (.inr (.inl ())))=equalWord) (bank : Y→Label G s Z op)
    (read : ∀x,dict (bank x)=scalar x)
    (previous : Layouts code sh)
    (newRows : ∀v u,(classify G p s (bank ((prog v).tag u))).correct ((device v).sliceFields u))

include previous newRows in
theorem install_layouts :
    Layouts (Encoding.installTo dict code home grp hub same board legacy sorted ids scalar prog valid
      (.inr (.inr (.inl ()))) relayRead bank read)
      (installedWorldShape sh hp one home grp hub same board legacy sorted ids scalar prog valid device bound widths) := by
  subst w
  intro x
  rcases x with ⟨(⟨b,h⟩|v),u⟩
  · cases b
    · rcases u with ⟨⟨v,rfl⟩,u⟩
      change (classify G p s (code.atNode ⟨v,u⟩)).correct _
      rw [show (installedWorldShape sh hp one home grp hub rfl board legacy sorted ids scalar prog valid
        device bound widths).nodeFields ⟨.inl (false,home v),⟨⟨v,rfl⟩,u⟩⟩ = (sh.sites v).sliceFields u from
        retained_fields W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device v u]
      exact previous ⟨v,u⟩
    · refine ⟨W.graph.width u.val/p,?_⟩
      exact relay_fields W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device h u
  · change (classify G p s (bank ((prog v).tag u))).correct _
    rw [show (installedWorldShape sh hp one home grp hub rfl board legacy sorted ids scalar prog valid
      device bound widths).nodeFields ⟨.inr v,u⟩=(device v).sliceFields u from
      device_fields W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device v u]
    exact newRows v u
end Install

private theorem lane_layout {Y : ℕ} {A : Type} {bw : A→ℕ} (units : A→ℕ)
    (multiple : ∀a,bw a=units a*p) (hp : 0<p) (prg : DescentLaneGates.Program Y p bw) (u : prg.Node) :
    Layout.rotor.correct ((ofProgram units multiple hp prg).sliceFields u) := by
  have eqn:=congrArg Prod.snd (lane_terminal_tag (hp:=hp) (units:=units) (multiple:=multiple) (prg:=prg) u)
  rw [(ofProgram units multiple hp prg).tag_fields hp u] at eqn
  refine ⟨List.ofFn (fun j:Fin (prg.op u).arity=>
    (⟨((prg.op u).arg j).residue,((prg.op u).arg j).stride,((prg.op u).arg j).count units⟩:SliceCode)),?_⟩
  simpa only [List.map_ofFn,Function.comp_def] using eqn

section Path
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (menu : Runnable F op) (b : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R)
    (pos : 0<b.reset.unit) (whole : p∣b.reset.unit) (fixed : resetSpec b=op)
    (wide : max 1 (max b.reset.width (C*b.reset.width))≤R) (a : Archive W)
    (code : Encoding (Label G s Z op) (dictionary G op menu p) a.bit) (sh : WorldShape p R a.bit)

theorem reset_layouts (previous : Layouts code sh) :
    let split:=sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole)
    let key:=DescentOrderedReset.grains W b.count b.order
    let fit: b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole).symm
    Layouts (Encoding.reset op menu b hp whole fixed a code)
      (WorldShape.follow hp pos whole b.reblock b.cuts
        (reentryWorldShape split b.reset b.terminals key (b.reset.unit/p) hp fit (resetMenu b) one wide)) := by
  dsimp only
  unfold Encoding.reset
  apply follow_layouts
  unfold reentryWorldShape
  apply install_layouts
  · rfl
  · exact gate_eq op b menu ((actual_eq b).trans fixed)
  · intro x
    exact previous ⟨x.1,x.2⟩
  · intro v u
    exact lane_layout _ _ hp _ u

variable {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {last : Reached W₁ G q ε S k i₁ z₁ D₁ wire hist}

theorem archive_layouts (path : Path first last) (hp : 0<p) (one : 1≤R) (pins : ∀a,p∣bits a)
    (whole : path.whole p) (aligned : path.aligned p R) (fixed : path.OnlyRotor op)
    (a : Archive W₀) (code : Encoding (Label G s z₀ op) (dictionary G op menu p) a.bit)
    (sh : WorldShape p R a.bit) (previous : Layouts code sh) :
    Layouts (encodePath op menu path hp whole fixed a code) (archiveShape hp one pins a sh path whole aligned) := by
  induction path with
  | here=>exact previous
  | @ordinary _ _ z D z' D' source prev u he T c norm target ticket ih=>
    have limit : T.z≤z₀ := ticket.quantum.trans source.grain ▸ grain_le prev
    have prior:=ih whole aligned.1 fixed
    let earlier:=prev.archive p hp a whole
    let oldCode:=encodePath op menu prev hp whole fixed a code
    let oldShape:=archiveShape hp one pins a sh prev whole aligned.1
    intro x
    change (classify G p s (((Encoding.scanned G op menu oldCode T he c limit).follow norm).atNode x)).correct
      ((afterOrdinary hp one pins ticket earlier oldShape aligned.2).nodeFields x)
    have fieldsAt := ordinary_fields ticket earlier oldShape hp one pins aligned.2 x
    change (afterOrdinary hp one pins ticket earlier oldShape aligned.2).nodeFields x = _ at fieldsAt
    rw [ordinary_at op menu ticket earlier oldCode limit x,fieldsAt]
    rcases hroot : roots ticket earlier x with y|⟨j,r⟩
    · simpa only [hroot, Sum.elim_inl] using (prior y)
    · simp only [Sum.elim_inr]
      rfl
  | reset prev b ih=>
    exact reset_layouts menu b hp one aligned.2.1 whole.2 fixed.2 aligned.2.2.2 _ _ _
      (ih whole.1 aligned.1 fixed.1)

end Path
end
end Hierarchy.DescentTerminalSliceRuns

end OAI
