import OAI.Hierarchy.DescentPrivateBookTransport
import OAI.Hierarchy.DescentIssuedDonorChart
import OAI.Hierarchy.DescentActorDestination

namespace OAI
/-! # A common issued chart for the occupied nodes and their private operand books -/
namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentKernelHistory
noncomputable section
variable {F P : Type} [Field F] {d p R q : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {B : BitDescription W} (hp : 0<p) (pos : 0<q) (unit : p∣q)

open private SiteBooks.follow_split from OAI.Hierarchy.DescentPrivateBookTransport

private theorem merge_split_shape {V : Type} [DecidableEq V] (s : WorldShape p R B)
    (key : W.graph.Site → DescentHostDirectory.Key V) (hub : V → Bool) (k g : ℕ)
    (m : (W.coalesced key hub k g).graph.Edge → ℕ)
    (cut : ∀ e ∈ (W.coalesced key hub k g).core, (W.coalesced key hub k g).graph.width e = m e * q)
    (a : Normalize.CutsEqual q (.merge W V key hub k g (.split _ q m cut (.done _)))) :
    WorldShape.follow hp pos unit (.merge W V key hub k g (.split _ q m cut (.done _))) a s =
      (s.coalesced key hub k g).pieces m q cut hp pos unit := by
  have ha : a = (⟨rfl, trivial⟩ : Normalize.CutsEqual q
      (.merge W V key hub k g (.split _ q m cut (.done _)))) := Subsingleton.elim _ _
  subst a
  unfold WorldShape.follow
  rfl

private theorem home_mpr {Y : MarkedWorld F d P bits} {B' : BitDescription Y}
    {a a' : WorldShape p R B} {b b' : WorldShape p R B'}
    (ha : a = a') (hb : b = b') (books : SiteBooks hp a' b') :
    (Eq.mpr (congrArg₂ (fun s t => SiteBooks hp s t) ha hb) books).home = books.home := by
  cases ha
  cases hb
  rfl

theorem SiteBooks.appended_home (n : Normalize W) (valid : Normalize.CutsEqual q n) (s : WorldShape p R B)
    (vs : Equiv.Perm n.result.graph.Site) (es : Equiv.Perm n.result.graph.Edge) (v : W.graph.Site) :
    (SiteBooks.appended hp q pos unit n valid s vs es).home ((n.appendNames vs es).destination v)=n.destination v := by
  induction n with
  | done=>exact vs.symm_apply_apply v
  | merge W H key hub k g rest ih=>exact ih valid (s.coalesced key hub k g) vs es (MarkedWorld.address W key hub k g v)
  | named W v₀ e₀ rest ih=>exact ih valid (s.renamed v₀ e₀) vs es (v₀ v)
  | split W q' m cut rest ih=>
    obtain ⟨rfl,tail⟩:=valid
    let inner := SiteBooks.appended hp q' pos unit rest tail (s.pieces m q' cut hp pos unit) vs es
    have left := SiteBooks.follow_split hp q' pos unit m cut (rest.appendNames vs es)
      ((Normalize.cutsEqual_appendNames q' rest vs es).2 tail) s
    have right := SiteBooks.follow_split hp q' pos unit m cut rest tail s
    change (SiteBooks.appended hp q' pos unit (.split W q' m cut rest) ⟨rfl,tail⟩ s vs es).home
      ((rest.appendNames vs es).destination v) = rest.destination v
    let carried := Eq.mpr (congrArg₂ (fun a b => SiteBooks hp a b) left right) inner
    have hcarry : (SiteBooks.appended hp q' pos unit (.split W q' m cut rest) ⟨rfl,tail⟩ s vs es) = carried := by
      unfold SiteBooks.appended
      rfl
    rw [hcarry]
    exact (congrArg (fun h : _ ≃ _ => h ((rest.appendNames vs es).destination v))
      (home_mpr hp left right inner)).trans (ih tail (s.pieces m q' cut hp pos unit) vs es v)

/-- Read the original unflattened chronological node of a retained operand book. -/
def SiteBooks.nodeAt {Y : MarkedWorld F d P bits} {B' : BitDescription Y}
    {s : WorldShape p R B} {t : WorldShape p R B'} (books : SiteBooks hp s t)
    (x : NodeOrder.All B) : NodeOrder.All B' := ⟨books.home x.1,(books.atSite x.1).node x.2⟩

private theorem nodeAt_mpr {Y : MarkedWorld F d P bits} {B' : BitDescription Y}
    {a a' : WorldShape p R B} {b b' : WorldShape p R B'}
    (ha : a = a') (hb : b = b') (books : SiteBooks hp a' b') (x : NodeOrder.All B) :
    (Eq.mpr (congrArg₂ (fun s t => SiteBooks hp s t) ha hb) books).nodeAt hp x = books.nodeAt hp x := by
  cases ha
  cases hb
  rfl

theorem SiteBooks.appended_node (n : Normalize W) (valid : Normalize.CutsEqual q n) (s : WorldShape p R B)
    (vs : Equiv.Perm n.result.graph.Site) (es : Equiv.Perm n.result.graph.Edge)
    (x : NodeOrder.All (B.follow (n.appendNames vs es))) :
    NodeOrder.followNames n B ((SiteBooks.appended hp q pos unit n valid s vs es).nodeAt hp x)=
      NodeOrder.followNames (n.appendNames vs es) B x := by
  induction n with
  | done =>
    cases x with
    | mk v a =>
      rfl
  | merge W H key flag k g rest ih =>
    exact congrArg (NodeOrder.coalescedNames B key flag k g)
      (ih valid (s.coalesced key flag k g) vs es x)
  | named W vs₀ es₀ rest ih =>
    exact congrArg (NodeOrder.renamedNames B vs₀ es₀) (ih valid (s.renamed vs₀ es₀) vs es x)
  | split W q' m fit rest ih =>
    obtain ⟨rfl,tail⟩:=valid
    let inner := SiteBooks.appended hp q' pos unit rest tail (s.pieces m q' fit hp pos unit) vs es
    have left := SiteBooks.follow_split hp q' pos unit m fit (rest.appendNames vs es)
      ((Normalize.cutsEqual_appendNames q' rest vs es).2 tail) s
    have right := SiteBooks.follow_split hp q' pos unit m fit rest tail s
    exact congrArg (NodeOrder.splitNames B m q' fit)
      ((congrArg (NodeOrder.followNames rest (B.pieces m q' fit)) (nodeAt_mpr hp left right inner x)).trans
        (ih tail (s.pieces m q' fit hp pos unit) vs es x))
end
end Hierarchy.DescentBundleHistory

namespace Hierarchy.DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.StarKeys DescentKernelHistory DescentBundleHistory
open DescentHostDirectory DescentHostDegree DescentHistoryOrder DescentNetworkPartition DescentPacking
open scoped Classical
noncomputable section
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d p R : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ}
variable (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice) {old : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)}
  {root : H↪ℕ} {U : MarkedWorld F d P bits} {n : Normalize U} {t : Tape n.result.graph.Edge} {pair : ScanNumbers he T}
set_option quotPrecheck false
local notation "sel" => scanWorld he T c

local notation "r" => BitDescription.scannedRows he T
local notation "layout" => bestLayout (branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c))
local notation "venue" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack
local notation "shelf" => 2^(packExponent 20 T.Δ)+2
local notation "rate" => gainExponent 20 T.Δ

theorem IssuedRows.common_chart (issued : IssuedRows he T c old root U n t pair) (state : U=sel) :
    ∃ b : IssuedDonorChart he T H,
      ((∀v,b.key he T c v∈keys T.k shelf) ∧
       ∀x y : (rawGraph he T c).Site,n.destination (rawInput he T c state x)=n.destination (rawInput he T c state y) ↔
         mergeHub b.hub T.k rate (b.key he T c (venue x))=mergeHub b.hub T.k rate (b.key he T c (venue y))) ∧
      ∀{p R : ℕ} (hp : 0<p) {B : BitDescription sel} (before : WorldShape p R B) (unit : p∣T.z)
        (cut : Normalize.CutsEqual T.z n),
      ∃ book : SiteBooks hp (WorldShape.follow hp T.unitPos unit n cut (before.transport state.symm))
          (before.coalesced (b.key he T c) b.hub T.k rate),
        (∀x : (rawGraph he T c).Site,book.home (n.destination (rawInput he T c state x))=
          MarkedWorld.address sel (b.key he T c) b.hub T.k rate (venue x)) ∧
        ∀x,NodeOrder.coalescedNames B (b.key he T c) b.hub T.k rate (book.nodeAt hp x)=
          NodeOrder.castNames state.symm B (NodeOrder.followNames n _ x) := by
  induction issued with
  | stage col same hub k g q legal source prior marked cuts =>
    obtain ⟨_,size,gain,valid,native,code,oldHome⟩:=source
    subst k
    subst g
    let b : IssuedDonorChart he T H:=⟨col,same,hub,native,code,oldHome⟩
    refine ⟨b,⟨valid,fun _ _=>Subtype.ext_iff⟩,?_⟩
    intro p R hp B before unit cut
    have hq : q=T.z:=cut.1
    subst q
    have state_refl : state = (rfl : sel = sel) := Subsingleton.elim _ _
    rw [state_refl]
    let base := before.coalesced (b.key he T c) b.hub T.k rate
    let counts := W.repetitions G (r).pick (fun _ => T.z) (fun _ => T.unitPos) (r).fit (r).pack
      ((r).profile c) (b.key he T c) b.hub T.k rate T.z
    have fit := W.repetition_width G (r).pick (fun _ => T.z) (fun _ => T.unitPos) (r).fit (r).pack
      ((r).profile c) (b.key he T c) b.hub T.k rate T.z prior marked cuts
    let part := SiteBooks.split hp base counts T.z fit T.unitPos unit
    have shape := DescentBundleHistory.merge_split_shape hp T.unitPos unit before
      (b.key he T c) b.hub T.k rate counts fit cut
    let book := Eq.mpr (congrArg₂ (fun a b => SiteBooks hp a b) shape (Eq.refl base)) part
    refine ⟨book,fun x => ?_,fun x => ?_⟩
    · exact congrArg (fun h : _ ≃ _ => h (MarkedWorld.address sel (b.key he T c) b.hub T.k rate (venue x)))
        (home_mpr hp shape (Eq.refl base) part)
    · exact congrArg (NodeOrder.coalescedNames B (b.key he T c) b.hub T.k rate)
        (nodeAt_mpr hp shape (Eq.refl base) part x)
  | named previous tape kept site ih =>
    obtain ⟨b,measured,prior⟩:=ih state
    refine ⟨b,⟨measured.1,fun x y=>(Normalize.destination_appendNames previous _ _ _ _).trans (measured.2 x y)⟩,?_⟩
    intro p R hp B before unit cut
    let s:=DescentPhysicalOrder.rename site
    let e:=DescentPhysicalOrder.rename (tape.sourceKey previous.result.graph.src site previous.result.graph.width)
    have checked:=(Normalize.cutsEqual_appendNames T.z previous s e).1 cut
    obtain ⟨book,home,node⟩:=prior hp before unit checked
    let carry:=SiteBooks.appended hp T.z T.unitPos unit previous checked (before.transport state.symm) s e
    refine ⟨SiteBooks.trans hp carry book,fun x=>?_,fun x=>?_⟩
    · exact (congrArg book.home (SiteBooks.appended_home hp T.unitPos unit previous checked (before.transport state.symm)
        s e (rawInput he T c state x))).trans (home x)
    · exact (node (carry.nodeAt hp x)).trans (congrArg (NodeOrder.castNames state.symm B)
        (SiteBooks.appended_node hp T.unitPos unit previous checked (before.transport state.symm) s e x))

end
end Hierarchy.DescentStageEdgeReceipt

end OAI
