import OAI.Hierarchy.DescentFundedCensusRoles

namespace OAI
/-! # Actual input expressions consumed by the reset's funded atlas -/
set_option quotPrecheck false
namespace Hierarchy.DescentFundedCensus
open DescentSIMDLookup DescentPackedZip DescentResetHostSize DescentContacts DescentCommonHost DescentHostDirectory
open DescentPaidResidentCount.Reset DescentPaidResidentCount.Reset.BankIssue
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {w n h r Ht C packet batch oldCap f degree ports field sf : ℕ} {s : Shape}
  (board : NonlinearExpanders.Graph n h)
local notation "atlas" => Node Unit (Unit×Endpoint (2^n)) (DescentCommonPalette.rotor board).Site
local notation "ticketCount" => (2^r:ℕ)
local notation "size" => s.bits
local notation "arity" => DescentFallbackPeriod.inputCount degree ticketCount ports n r
variable (qs : Fin s.jobs → Node Unit (Unit×Endpoint (2^n)) (DescentCommonPalette.rotor board).Site) (io : Ports r n) (seen : Fin s.jobs→Expr)
local notation "job" => fun j=>compile (Ht:=Ht) board C packet batch size oldCap f degree ports field sf io (seen j) (qs j)

structure AtlasValues (n r Q H G b D cap field sf : ℕ) where
  present : Fin Q→Fin H→Fin G→Cell 1
  stencil : Fin H→Fin G→Cell (sf*2^r)
  old : Fin H→Fin G→Cell (b*2^r)
  relay : Fin H→Fin G→Cell (b*2^r)
  bank : Bool → Code r×Option (Fin (2^n))→Fin H→Fin G→Cell (field*DescentFallbackPeriod.inputCount D (2^r) cap n r)

local notation "V" => AtlasValues n r s.jobs s.hosts s.groups size degree ports field sf
variable (v : AtlasValues n r s.jobs s.hosts s.groups s.bits degree ports field sf)

def operands (j : Fin s.jobs) (h₀ : Fin s.hosts) (g : Fin s.groups) (shape : atlas) :
    let chosenJob:=compile (Ht:=Ht) board C packet batch size oldCap f degree ports field sf io (seen j) shape
    Cell chosenJob.left × Cell chosenJob.right :=by
  cases shape with
  | good _ _ _=>exact (v.present j h₀ g,0)
  | trunk side label=>exact (v.stencil h₀ g,if side then v.relay h₀ g else v.old h₀ g)
  | fall side label path=>
    exact if legal : label.2.1.1 ≤ r ∧ label.2.1.2 < 2^label.2.1.1 ∧ path.length ≤ Ht then
      ((v.present j h₀ g).val,(v.bank side (⟨label.2.1,mem_codes legal.1 legal.2.1⟩,label.2.2) h₀ g).val)
    else (0,0)

def atlasValues : Values job where
  first j h₀ g:=(operands (Ht:=Ht) (C:=C) (packet:=packet) (batch:=batch) (oldCap:=oldCap) (f:=f)
    board io seen v j h₀ g (qs j)).1
  second j h₀ g:=(operands (Ht:=Ht) (C:=C) (packet:=packet) (batch:=batch) (oldCap:=oldCap) (f:=f)
    board io seen v j h₀ g (qs j)).2
  present:=v.present

local notation "arr" => atlasValues (Ht:=Ht) (C:=C) (packet:=packet) (batch:=batch) (oldCap:=oldCap) (f:=f)
  board qs io seen v

structure RawSources {s : Shape} (io : Ports r n) (seen : Fin s.jobs→Expr)
    (v : AtlasValues n r s.jobs s.hosts s.groups s.bits degree ports field sf) (m : Memory w) : Prop where
  present : ∀q,Source (seen q) (v.present q) s.lanes m
  stencil : Source io.stencil v.stencil s.lanes m
  old : Source io.old v.old s.lanes m
  relay : Source io.relay v.relay s.lanes m
  middle : ∀side key, Source (io.bank side key) (v.bank side key) s.lanes m

private theorem source_zero {H G M w b : ℕ} (m : Memory w) :
    Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell b)) M m :=by
  intro j
  change 0=(((finFunctionFinEquiv (fun i : Fin M=>if _ : j.2.val*M+i.val<G then (0:Cell b) else 0)).val:ℕ):Word w)
  simp

private theorem cell_from_nat {bits : ℕ} (x : Cell bits) : ((x.val : ℕ) : Cell bits) = x :=
  Fin.ext (Fin.val_cast_of_lt x.isLt)

private theorem source_width {H G M w b c : ℕ} (same : b = c) {e : Expr} {m : Memory w}
    {v : Fin H → Fin G → Cell b} (src : Source e v M m) :
    Source e (fun h g => ((v h g).val : Cell c)) M m := by
  subst c
  simpa only [cell_from_nat] using src

theorem atlas_sources (m : Memory w) (raw : RawSources io seen v m) : Sources job arr m :=by
  constructor
  · intro j
    dsimp only [atlasValues]
    cases state:qs j with
    | good s z a=>exact raw.present j
    | trunk s z=>exact raw.stencil
    | fall s z path=>
      by_cases legal:z.2.1.1≤r ∧ z.2.1.2<2^z.2.1.1 ∧ path.length≤Ht
      · simp [operands,compile,legal]
        apply source_width _ (raw.present j)
        simp [legal,fallback,whenPresent]
      · simp [operands,compile,legal]
        exact source_zero m
  · intro j
    dsimp only [atlasValues]
    cases state:qs j with
    | good s z a=>exact source_zero (b:=0) m
    | trunk s z=>cases s <;> first | exact raw.old | exact raw.relay
    | fall s z path=>
      by_cases legal:z.2.1.1≤r ∧ z.2.1.2<2^z.2.1.1 ∧ path.length≤Ht
      · simp [operands,compile,legal]
        apply source_width _ (raw.middle s (⟨z.2.1,mem_codes legal.1 legal.2.1⟩,z.2.2))
        simp [legal,fallback,whenPresent]
      · simp [operands,compile,legal]
        exact source_zero m
  · intro j
    dsimp only [atlasValues]
    cases state:qs j with
    | good side z a => exact raw.present j
    | trunk side z => exact raw.present j
    | fall side z path =>
      rcases z with ⟨u,z⟩
      by_cases legal : z.1.1 ≤ r ∧ z.1.2 < 2^z.1.1 ∧ path.length ≤ Ht <;>
        simpa [compile,legal] using raw.present j

theorem raw_read {base : ℕ} (m : Memory w) (limits : Room job w base) (raw : RawSources io seen v m)
    (q : Fin s.jobs) (whereAt : Row s.hosts s.groups s.lanes) :
    memory job base m (s.column base q+(row _ _ _ whereAt).val)=(data (quantity job arr q) whereAt).val :=
  read job limits m arr (atlas_sources board qs io seen v m raw) q whereAt

theorem no_charge (q : Fin s.jobs) (h₀ : Fin s.hosts) (g : Fin s.groups) (absent : v.present q h₀ g=0) :
    quantity job arr q h₀ g=0 :=by simp [quantity,mask,atlasValues,absent]

theorem trunk_value (j : Fin s.jobs) (h₀ : Fin s.hosts) (g : Fin s.groups) (side : Bool) (label : Unit×Endpoint (2^n))
    (kind : qs j=.trunk side label) (yes : v.present j h₀ g=1) :
    quantity job arr j h₀ g=(trunk sf size ticketCount (DescentFallbackShapeTable.cell r label.2)).apply
      (v.stencil h₀ g) (if side then v.relay h₀ g else v.old h₀ g) :=by
  rcases label with ⟨⟨⟩, z⟩
  dsimp only [quantity,atlasValues]
  rw [kind]
  simp [mask,operands,compile,yes]

theorem good_value (j : Fin s.jobs) (h₀ : Fin s.hosts) (g : Fin s.groups) (side : Bool) (label) (a)
    (kind : qs j=.good side label a) (yes : v.present j h₀ g=1) :
    quantity job arr j h₀ g=((Rotor.funded board C packet batch
      (DescentRecordedRotorLayers.layers n packet f oldCap) a:ℕ):Cell size) :=by
  dsimp only [quantity,atlasValues]
  rw [kind]
  simp [mask,operands,compile,yes]
  exact good_read board C packet batch size oldCap f a 0

theorem fall_value (j : Fin s.jobs) (h₀ : Fin s.hosts) (g : Fin s.groups) (side : Bool) (z : Endpoint (2^n))
    (path : List Bool) (kind : qs j=.fall side ((),z) path) (yes : v.present j h₀ g=1)
    (legal : z.1.1≤r ∧ z.1.2<2^z.1.1 ∧ path.length≤Ht) :
    let key : Code r×Option (Fin (2^n)):=(⟨z.1,mem_codes legal.1 legal.2.1⟩,z.2)
    quantity job arr j h₀ g=((amount board C packet batch
      (.tree ⟨path.length,Nat.lt_succ_of_le legal.2.2⟩ path.get)
      (treeInput (ht:=Ht) (levels:=0) (degree:=degree) (L:=ticketCount) (cap:=ports) side key (v.bank side key h₀ g)):ℕ):Cell size) :=by
  intro key
  dsimp only [quantity,atlasValues]
  rw [kind]
  simp [mask,operands,yes,legal,key]
  let applyNat (j : Job size) (x y : ℕ) := j.apply x y
  change applyNat (compile (Ht:=Ht) board C packet batch size oldCap f degree ports field sf io (seen j)
    (.fall side ((),z) path)) 1 (v.bank side key h₀ g).val = _
  simp only [compile, dite_eq_left legal]
  have round := cell_from_nat (v.bank side key h₀ g)
  let role := fallback board C packet batch size degree ports field side key ⟨path.length,Nat.lt_succ_of_le legal.2.2⟩ path.get
  exact (congrArg (fun x => role.apply 1 x) round).trans
    (fallback_read board C packet batch size degree ports field side key ⟨path.length,Nat.lt_succ_of_le legal.2.2⟩ path.get _)

end
end Hierarchy.DescentFundedCensus

end OAI
