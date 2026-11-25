import OAI.Computability.BorderVNP.DiagonalTagProgramRead
import OAI.Computability.BorderVNP.DiagonalProfileGuardTags
import OAI.Computability.BorderVNP.DiagonalProfilePaidTags
import OAI.Computability.BorderVNP.DiagonalSpecializedDenseStep

/-! # Pointwise tags of the actual newly installed private programs at a dense stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.DenseReplay

open Cover Crossing Shortening Adaptive CombiningStep StaticRows Packing Packing.Inherited PackedHistoryCircuit.Normalized
open Packing.InheritedProfile Packing.BankSite
open scoped Classical

set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

variable {D m k d next exp : ℕ} [NeZero D] {P I K B E : Type} [Fintype P] [Fintype I] [Fintype B]
    [Field K] [Field E] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    {Team Param Gadget : Type} [Fintype Team] [Fintype Param]
    (s : Stage m B next child) (input : ∀ j, Tracked Team Param Gadget exp (child j).pack.layout)
    (e : PaidIdentity K D m) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ) (q : s.Index e)
    (old : ∀ j, Site.Programs (child j).pack.layout)
    {ns ne np : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (portID : (Fin k × P) ↪ Fin np)
    (seedName : ((I → Deck (next+1)) × B) → ℕ)

local notation3 "G₀" => (s.result e q).pack.layout
local notation3 "tags₀" => (stageOutput s input e y hy pos q).tags
local notation3 (prettyPrint := false) "programs₀" => s.privatePrograms e q old siteID edgeID portID seedName (num ∘ pos)

/-- All three kinds of fresh sites have their true sparse observation fiber on the
same sorted stage and histogram as the specialized tagged history. -/
theorem stage_birth_tagModel (a : (I → Deck (next+1)) × B) (v : TemplateSite e) :
    Site.Lineage.TagModel G₀ edgeID portID (.inr ⟨a,v⟩) (programs₀ (.inr ⟨a,v⟩))
      (fun _ => True) tags₀ num := by
  rcases v with ⟨⟩ | t | ⟨i,v⟩
  · intro z x
    let aux := workAt e s.input s.label s.perm s.orient (0,false) q
    let site := originSite e s.input s.label s.perm s.orient (0,false) q a siteID edgeID portID
    apply guard_tag_read G₀ (.inr ⟨a,.inl ()⟩) aux edgeID portID site rfl rfl
      (profile_noLoop e s.input s.label s.perm s.orient (0,false) q a (.inl ()))
      (s.result e q).pack.table (originWork e s.input s.label s.perm s.orient (0,false) q a siteID edgeID portID)
      (origin_observe e s.input s.label s.perm s.orient (0,false) q a siteID edgeID portID) z x _ num
    exact guard_agrees _
  · intro z x
    let aux := workAt e s.input s.label s.perm s.orient (0,false) q
    let site := terminalSite e s.input s.label s.perm s.orient (0,false) q a siteID edgeID portID seedName t
    apply guard_tag_read G₀ (.inr ⟨a,.inr (.inl t)⟩) aux edgeID portID site rfl rfl
      (profile_noLoop e s.input s.label s.perm s.orient (0,false) q a (.inr t))
      (s.result e q).pack.table (terminalWork e s.input s.label s.perm s.orient (0,false) q a siteID edgeID portID seedName t)
      (fun ext bank => terminal_observe e s.input s.label s.perm s.orient (0,false) q a siteID edgeID portID ext bank seedName t)
      z x _ num
    exact guard_agrees _
  · intro z x
    let src : Pack D (Fin k × P) (fun p => bits p.2) (Entry Param Gadget) :=
      ⟨s.input.layout,(ordered s input).tags⟩
    exact PaidSite.tag_read e src s.input.table s.label s.perm s.orient (0,false) q pos num a i v edgeID portID z x

end Diagonal.CellEntries.DenseReplay

end BorderVNP
end Computability
end OAI
