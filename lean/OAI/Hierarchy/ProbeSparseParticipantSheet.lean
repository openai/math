import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.TaggedWideSitePublisher
import OAI.Hierarchy.ProtocolRAMBoughtLocations
import OAI.Hierarchy.TaggedWideStripParties

namespace OAI
/-! # Scattering the selected candidate and its actual finite party at every original site -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM SiteScatter
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing

variable {W sites : ℕ} {p : Shape}

/-- Keep one original candidate row together with its finite local role. -/
def ballotRow (selected : Finset (Fin p.candidates)) : selected × Fin p.parties ↪ Fin p.candidates × Fin p.parties :=
  ⟨fun a=>(a.1.val,a.2), fun _ _ eq => Prod.ext
    (Subtype.ext (congrArg (fun z : Fin p.candidates × Fin p.parties => z.1) eq))
    (congrArg (fun z : Fin p.candidates × Fin p.parties => z.2) eq)⟩

theorem ballotRow_range (selected : Finset (Fin p.candidates)) (i : Fin p.candidates×Fin p.parties) :
    i∈Set.range (ballotRow (p:=p) selected) ↔ i.1∈selected := by
  constructor
  · rintro ⟨a,rfl⟩;exact a.1.property
  · intro live;exact ⟨(⟨i.1,live⟩,i.2),Prod.ext rfl rfl⟩

/-- A mounted public sheet can serve arbitrary installed finite fields. -/
structure PublicSheet (p : Shape) (sites rom start W : ℕ) (fields : Fields p) (m : Memory W) : Prop where
  mounted : ∀j : Fin 3,RoleROM.Mounted (rom+j.val*p.count) (SiteScatter.directory p.candidates p.parties p.columns j) m
  size : p.count≤2^W
  parties : p.parties≤2^W
  columns : p.columns≤2^W
  stride : ∀s : Fin sites,(RoleROM.bank (rom+3*p.count) sites).read m (s.val:Word W)=((s.val*p.columns:ℕ):Word W)
  value : (p.sheet sites rom start fields).value.Fits W (start+1)
  address : (p.sheet sites rom start fields).address.Fits W (start+1)
  space : start+1+sites*p.columns+p.count+p.count<2^W

/-- The sheet's own RAM program and its full output. Every absent physical
participant reads zero. The stored words at each present party are precisely
the field expressions compiled for its original candidate index. -/
theorem scatter_ballot (selected : Finset (Fin p.candidates)) (party : selected×Fin p.parties ↪ Fin sites)
    (rom start : ℕ) (fields : Fields p) (m : Memory W) (boot : PublicSheet p sites rom start W fields m)
    (choose : ∀(i : Fin p.candidates) (j : Fin p.parties),(fields.selected j).eval m (i.val:Word W)≠0 ↔ i∈selected)
    (named : ∀i : selected×Fin p.parties,(fields.site i.2).eval m (i.1.val.val:Word W)=((party i).val:Word W)) :
    let sheet:=p.sheet sites rom start fields
    let data (i : selected×Fin p.parties) (j : Fin p.columns):=(fields.value i.2 j).eval m (i.1.val.val:Word W)
    ∃out,(sheet.code W).Exec m out sheet.ticks ∧
      (∀s c,out (start+1+(SiteScatter.pos s c).val)=SiteScatter.table party data s c) ∧
      ∀u,(u<start+1 ∨ start+1+sites*p.columns≤u) →
        (u<start+1+sites*p.columns ∨ start+1+sites*p.columns+p.count+p.count≤u) → u≠start → out u=m u := by
  intro sheet data
  exact SiteScatter.replay (ballotRow (p:=p) selected) party data rom (start+1) (start+1+sites*p.columns) start
    (RoleROM.bank (rom+3*p.count) sites) fields.selected fields.site fields.value m
    boot.mounted boot.size boot.parties boot.columns (fun q=>(choose q.1 q.2).trans (ballotRow_range selected q).symm)
    named (fun _ _=>rfl) boot.stride boot.value boot.address le_rfl boot.space (Nat.lt_succ_self start)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

namespace Hierarchy.ProbeStage.CoreBoard.SiteDirectory
open AdaptiveProbe Strip
open scoped Classical

/-- Place selected ballots by their real disjoint strip and local party label. -/
def selectedParties {n l sites : ℕ} {Ball X : Type*} (selected : Finset (Fin n)) (owner : selected ↪ Ball)
    (site : Ball×X ↪ Fin sites) (name : X≃Fin l) : selected×Fin l ↪ Fin sites :=
  (Function.Embedding.prodMap owner name.symm.toEmbedding).trans site

def payloadRoots {h n : ℕ} (selected : Finset (Fin n)) (valid : ∀i∈selected,i.val<2^h) : selected ↪ Fin (2^h) :=
  ⟨fun j=>⟨j.val.val,valid j.val j.property⟩,
    fun _ _ eq => Subtype.ext (Fin.ext (congrArg (fun i : Fin (2^h) => i.val) eq))⟩

/-- The native issued row is the inverse of a genuine single birth flag. -/
def purchaseRoots {h W k depth n : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {mark : StageAt h (2^W)→Fin k×Bool→Finset (Fin (2^h))}
    (selected : Finset (Fin n))
    (live : ∀i∈selected,∃u : LiveChains S π depth mark,(ProtocolRAM.BoughtLocation.relative u).val=i.val) :
    selected ↪ LiveChains S π depth mark where
  toFun i := (live i.val i.property).choose
  inj' := by
    intro i j h
    apply Subtype.ext
    exact Fin.ext ((live i.val i.property).choose_spec.symm.trans
      ((congrArg (fun u=>(ProtocolRAM.BoughtLocation.relative u).val) h).trans (live j.val j.property).choose_spec))

end Hierarchy.ProbeStage.CoreBoard.SiteDirectory
end

end OAI
