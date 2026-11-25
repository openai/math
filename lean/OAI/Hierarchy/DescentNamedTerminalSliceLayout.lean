import OAI.Hierarchy.DescentArchiveSliceLayout
import OAI.Hierarchy.DescentNamedPrimitivePalette
import OAI.Hierarchy.DescentTerminalSeedRoleWords

namespace OAI
/-! # Authentic terminal operand boundaries from the named archive's seed and three later origins -/
namespace Hierarchy.DescentSixParty.SeedNamed.Palette
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentInitialHost DescentColonies
open DescentRotor DescentResetGates DescentEpochTagKeys DescentPrimitivePalette Chronology
open DescentPackedSeed DescentMixedRouter DescentResetInvoice DescentTerminalSliceRuns DescentTerminalCombinedRole Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

open private encodedOrigin renameEncoding carryEncoding changeEncoding from
  OAI.Hierarchy.DescentNamedPrimitivePalette
open private Origin.archiveShape Origin.archive_eq changeShapeArchive shapeOfTransfer from
  OAI.Hierarchy.DescentNamedHistoryShape
open private renamedShape shapeTransfer ShapeTransfer ShapeTransfer.move ShapeTransfer.source ShapeTransfer.destination
  Origin.transferFor Origin.transferInput Origin.physicalShape Origin.originalShape from
  OAI.Hierarchy.DescentNamedSeedInitialShape
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive

section
variable {P : Type} {d : ℕ} {bits : P → ℕ} {W V : MarkedWorld F d P bits}
    {G : PoweredGadget F} {op : RotorSpec} {s z p R : ℕ} {dict : Label G s z op → List (List Bool) → F}

private theorem changed_layouts (a b : Archive W) (same : a = b)
    (code : Encoding (Label G s z op) dict a.bit) (sh : WorldShape p R a.bit) (ok : Layouts code sh) :
    Layouts (changeEncoding a b same code) (changeShapeArchive a b same p R sh) := by
  cases same
  exact ok

private theorem carried_layouts (a : Archive W) (same : W = V)
    (code : Encoding (Label G s z op) dict a.bit) (sh : WorldShape p R a.bit) (ok : Layouts code sh) :
    Layouts (carryEncoding (transportArchive a same) code)
      ((transportArchive a same).carry (fun _ b => WorldShape p R b.bit) sh) := by
  cases same
  exact ok

private theorem package_layouts (a : Archive W) (pkg : ArchiveTransport a V) (same : W = V)
    (identity : pkg = transportArchive a same)
    (code : Encoding (Label G s z op) dict a.bit) (sh : WorldShape p R a.bit) (ok : Layouts code sh) :
    Layouts (carryEncoding pkg code) (pkg.carry (fun _ b => WorldShape p R b.bit) sh) := by
  subst pkg
  exact carried_layouts a same code sh ok

private def transferSource {a : Archive W} (pkg : ArchiveTransport a V) (p R : ℕ)
    (record : ShapeTransfer) (same : record = shapeTransfer pkg p R)
    (sh : WorldShape p R a.bit) : ShapeTransfer.source record := by
  subst record
  exact sh

private theorem transferred_move {a : Archive W} (pkg : ArchiveTransport a V) (p R : ℕ)
    (record : ShapeTransfer) (same : record = shapeTransfer pkg p R) (sh : WorldShape p R a.bit)
    (input : ShapeTransfer.source record) (ident : input = transferSource pkg p R record same sh) :
    shapeOfTransfer pkg p R record same (ShapeTransfer.move record input) =
      pkg.carry (fun _ b => WorldShape p R b.bit) sh := by
  subst record
  subst input
  rfl

private theorem renamed_layouts (a : Archive W) (places : Equiv.Perm W.graph.Site)
    (edges : Equiv.Perm W.graph.Edge) (code : Encoding (Label G s z op) dict a.bit)
    (sh : WorldShape p R a.bit) (ok : Layouts code sh) :
    Layouts (renameEncoding a places edges code) (renamedShape a places edges sh) := by
  intro x
  exact ok ⟨places.symm x.1,x.2⟩
end

private theorem seeded_layouts {cp pins : ℕ} (X : Approximation F cp pins) (copies s : ℕ)
    (c : (initialGroup X copies s).Choice) {G : PoweredGadget F} {z p R : ℕ}
    (op : RotorSpec) (menu : Runnable F op) (hp : 0<p) (one : 1≤R) (divides : p∣s) (hs : 0<s) :
    Layouts (seeded (G := G) (Z := z) (p := p) op menu X c) (seedRetained X copies s hp one divides c).shape := by
  intro x
  rcases x with ⟨⟨j,v⟩,u⟩
  exact ⟨Nat.div_pos (Nat.le_of_dvd hs divides) hp,legArity X v,seed_slices X c j v hp divides u⟩

section SeedLayout
attribute [local irreducible] Origin.archivePackage Origin.source
set_option maxHeartbeats 80000
section
variable {cp pins : ℕ} {X : Approximation F cp pins} {G : PoweredGadget F}
    {S : AtomSchedule} {q fee : ℝ} {k s z wire p R : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (S:=S) (s:=s) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)

variable (op : RotorSpec) (menu : Runnable F op) (hp : 0<p) (one : 1≤R) (divides : p∣s) (hs : 0<s)

private def placedCode :=
  renameEncoding (seedArchive X S.copies s c) (site o.raw) (edge o.raw)
    (seeded (G := G) (Z := z) (p := p) op menu X c)

local notation "placed_" => placedCode (p := p) o op menu
local notation "shaped_" => Origin.physicalShape o p R hp one divides

include hs in
private theorem placed_layouts : Layouts placed_ shaped_ := by
  apply renamed_layouts (seedArchive X S.copies s c) (site o.raw) (edge o.raw)
  exact seeded_layouts X S.copies s c (G := G) (z := z) op menu hp one divides hs

private def outputShape : WorldShape p R o.archivePackage.data.bit :=
  shapeOfTransfer o.archivePackage p R (Origin.transferFor o p R) rfl (o.bundleShape p R hp one divides)

local notation "carried_" => carryEncoding o.archivePackage placed_
local notation "outShape_" => outputShape o hp one divides

private def movedShape : WorldShape p R o.archivePackage.data.bit :=
  shapeOfTransfer o.archivePackage p R (Origin.transferFor o p R) rfl
    (ShapeTransfer.move (Origin.transferFor o p R) (Origin.transferInput o p R hp one divides))

private theorem bundle_move_function :
    @Origin.bundleShape (F := F) (S := S) (G := G) (q := q) (ε := fee) (k := k) (s := s) (z := z)
      (wire := wire) (X := X) (c := c) (digits := digits) =
    fun root p R hp stride width => ShapeTransfer.move (Origin.transferFor root p R)
      (Origin.transferInput root p R hp stride width) := rfl

private theorem bundle_move : o.bundleShape p R hp one divides =
    ShapeTransfer.move (Origin.transferFor o p R) (Origin.transferInput o p R hp one divides) := by
  have all := bundle_move_function (X := X) (G := G) (S := S) (q := q) (fee := fee) (k := k)
    (s := s) (z := z) (wire := wire) (c := c) (digits := digits)
  exact congrFun (congrFun (congrFun (congrFun (congrFun (congrFun all o) p) R) hp) one) divides

private theorem output_moved : outShape_ = movedShape o hp one divides :=
  congrArg (shapeOfTransfer o.archivePackage p R (Origin.transferFor o p R) rfl) (bundle_move o hp one divides)

private theorem input_shape : Origin.transferInput o p R hp one divides =
    transferSource o.archivePackage p R (Origin.transferFor o p R) rfl shaped_ := rfl

private theorem moved_carry : movedShape o hp one divides =
    o.archivePackage.carry (fun _ b => WorldShape p R b.bit) shaped_ :=
  transferred_move o.archivePackage p R (Origin.transferFor o p R) rfl shaped_
    (Origin.transferInput o p R hp one divides) (input_shape o hp one divides)

private theorem shape_carry : outShape_ =
    o.archivePackage.carry (fun _ b => WorldShape p R b.bit) shaped_ :=
  (output_moved o hp one divides).trans (moved_carry o hp one divides)

private theorem package_identity : o.archivePackage =
    transportArchive (renamedArchive (seedArchive X S.copies s c) (site o.raw) (edge o.raw))
      (linked_world X c digits o.seed) := by
  unfold Origin.archivePackage
  rfl

include hs in
private theorem witnessed_carry : Layouts carried_ (o.archivePackage.carry (fun _ b => WorldShape p R b.bit) shaped_) :=
  package_layouts _ o.archivePackage (linked_world X c digits o.seed)
    (package_identity o) placed_ shaped_ (placed_layouts o op menu hp one divides hs)

include hs in
private theorem received_layouts : Layouts carried_ outShape_ := by
  rw [shape_carry o hp one divides]
  exact witnessed_carry o op menu hp one divides hs

include hs in
private theorem origin_layouts :
    Layouts (encodedOrigin (p := p) o op menu) (Origin.archiveShape o p R hp one divides) := by
  exact changed_layouts o.archivePackage.data o.archive (Origin.archive_eq o).symm carried_ outShape_
    (received_layouts o op menu hp one divides hs)
end


end SeedLayout

attribute [local irreducible] Origin.archivePackage Origin.source encodedOrigin Origin.archiveShape encodePath

section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q₀*(wire₀:ℝ)
local notation "depthBound_" => GroupStage.depthBound (atRound S.rounds) n f g
private theorem layoutsOnBranch {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    (prior : Layouts (F:=F) (G:=G) (s:=s₀) (Z:=S.grainAt G.b p 0) (op:=op) (p:=p) («R»:=R) (dict:=dictionary (s:=s₀) (Z:=S.grainAt G.b p 0) G op menu p) (B:=b.origin.archive.bit) (encodedOrigin (p:=p) b.origin op menu)
      (Origin.archiveShape b.origin p R hp stride (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b))) :
    Layouts (F:=F) (G:=G) (s:=s₀) (Z:=S.grainAt G.b p 0) (op:=op) (p:=p) («R»:=R) (dict:=dictionary (s:=s₀) (Z:=S.grainAt G.b p 0) G op menu p) (B:=(Branch.archive X G S (r:=r) (c:=c) b hp).bit) (encodePath op menu b.path hp (b.path.recorded_whole p b.recorded) fixed b.origin.archive
      (encodedOrigin (p:=p) b.origin op menu)) (Branch.bundleShape X G S (r:=r) (c:=c) b hp stride) := by
  let divides : p ∣ s₀ := dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
  exact archive_layouts menu b.path hp stride (fun _ => dvd_mul_of_dvd_left divides 1)
    (b.path.recorded_whole p b.recorded) b.aligned fixed b.origin.archive
    (encodedOrigin (p:=p) b.origin op menu) (Origin.archiveShape b.origin p R hp stride divides) prior
end

private theorem view_layout {P : Type} {d s Z p R : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {op : RotorSpec} {B : BitDescription W}
    (dict : Label G s Z op → List (List Bool) → F) (e : Encoding (Label G s Z op) dict B)
    (shape : WorldShape p R B) (ok : Layouts e shape)
    (v : W.graph.Site) (u : ((e.view dict).recipe v).Node) :
    (classify G p s (((e.view dict).recipe v).tag u)).correct
      (((Encoding.viewShape dict e shape).sites v).sliceFields u) := ok ⟨v,u⟩

variable {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
set_option quotPrecheck false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint (p:=p) X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "initialWidth_" => S.firstWidth G.b p
local notation "rot" => RotorSpec.ofRates reset
local notation "strideN_" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "branchAt" c_:arg => ((cert).choose_spec.2.2.choose_spec.choose_spec c_).choose
local notation "outputAt" c_:arg => relabel X G S ordinary reset branch positive room shorten c_
local notation "shapeAt" c_:arg => leafShape X G S ordinary reset branch positive room shorten c_
local notation "stride_" => Nat.le_max_left 1 (max reset.bitsR (C * reset.bitsR))
local notation "divides_" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b

attribute [local irreducible] Branch.archive Branch.bundleShape
open private chosenArchive from OAI.Hierarchy.DescentNamedPrimitivePalette
local notation "grain_" => S.grainAt G.b p 0
local notation "dict_" => dictionary (s:=initialWidth_) (Z:=grain_) G rot reset.menu p
local notation "archAt" v_:arg => chosenArchive X G S ordinary reset branch positive room shorten v_
local notation "encAt" v_:arg => atLeaf X G S ordinary reset branch positive room shorten v_
local notation "rawShape" v_:arg => Branch.bundleShape (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=(cert).choose) (c:=v_) (p:=p) X G S (branchAt v_) positive stride_
theorem terminal_layout (c : (last).Choice) (v : ((last).state c).graph.Site) (u : ((outputAt c).recipe v).Node) :
    (classify G p initialWidth_ (((outputAt c).recipe v).tag u)).correct (((shapeAt c).sites v).sliceFields u) := by
  have pos : 0 < initialWidth_ := Nat.mul_pos (Nat.mul_pos positive (Nat.pow_pos G.base_pos)) G.base_pos
  apply view_layout (G:=G) (s:=initialWidth_) (Z:=grain_) (p:=p) («R»:=strideN_) (B:=(archAt c).bit) dict_ (encAt c) (rawShape c) _ v u
  unfold atLeaf
  apply layoutsOnBranch X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (r:=(cert).choose) (c:=c) (branchAt c) positive stride_ rot reset.menu ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.2.1.2
  exact origin_layouts (branchAt c).origin rot reset.menu positive stride_ divides_ pos

theorem terminal_partition (c : (last).Choice) (v : ((last).state c).graph.Site) (u : ((outputAt c).recipe v).Node) :
    (classify G p initialWidth_ (((outputAt c).recipe v).tag u)).restore
      (repeatFields (((shapeAt c).sites v).sliceFields u).flatten) = ((shapeAt c).sites v).sliceFields u :=
  classify_read G p initialWidth_ ((shapeAt c).sites v) u positive _
    (terminal_layout X G S ordinary reset branch positive room shorten c v u)

end
end Hierarchy.DescentSixParty.SeedNamed.Palette

end OAI
