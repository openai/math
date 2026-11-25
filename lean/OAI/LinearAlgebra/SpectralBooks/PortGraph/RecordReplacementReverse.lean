import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementCatalogue
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecoderIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAcceptedRep

/-! # The reverse map for the checked replacement catalogue

Every passing assignment of catalogue roles gives a certified old
representative and its term indices. This operation descends to isomorphism
classes of the smaller rooted maps.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ShapeCatalogue

open ReplacementChoices ReplacementTemplate UniformDecorations

variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ} (C : ShapeCatalogue F K w c)
  (sys : System N K ε)

section Map
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
  (z : V → RoleLabel (C.templates (N:=N) (ε:=ε))) (ok : (C.rules N ε).Accepts M z)

/-- The decoded expansion for an actual passing smaller map, including its
old root, old verifier, and saved records in canonical order. -/
def decode :
    DecodedChoices sys (fun d : Copies z => d.1.1)
      (recordPairing ok.2.2.choose ok.2.2.choose_spec (fun j => j.1.val) (fun _ => Equiv.refl _)) := by
  apply decodedChoices sys (fun j : C.Tag N ε => j.1) ok.2.2.choose ok.2.2.choose_spec
    (fun j => (C.templates j).root) M.root _ (fun _ => Equiv.refl _) (fun _ _ => rfl)
    (fun _ _ h => h) M.connected
  intro v
  exact and_comm.trans (ok.2.1 v)

end Map

/-- Decode a representative in the smaller role-decorated family into an old
summand with a term position attached to each canonical occurrence. -/
def reverse {h : ℕ} (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h) {S : ℕ}
    (q : ((C.rules N ε).acceptedFamily code C.coefficient S).Rep) :
    (sys.family C.Index).Rep :=
  (C.decode sys q.1.map q.2.val q.2.property).decorated C.Index (fun d => d.1.2)

section Naturality
variable {V E W D : Type} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype D] [DecidableEq W] {M : RootedMap V E} {H : RootedMap W D}
  {z : V → RoleLabel (C.templates (N:=N) (ε:=ε))} {z' : W → RoleLabel C.templates}

/-- Relabelling a passing smaller map preserves the old decorated summand
that the catalogue decodes. -/
theorem decode_iso (f : M.Iso H) (same : ∀ v, z v = z' (f.vertex v))
    (ok : (C.rules N ε).Accepts M z) (ok' : (C.rules N ε).Accepts H z') :
    (sys.family C.Index).IsIso ((C.decode sys M z ok).decorated C.Index (fun d => d.1.2))
      ((C.decode sys H z' ok').decorated C.Index (fun d => d.1.2)) :=
  (DecoderIso.ofIso f same).decorated_iso ok.2.2.choose ok'.2.2.choose ok.2.2.choose_spec ok'.2.2.choose_spec
    (fun _ => Equiv.refl _) (C.decode sys H z' ok') (C.decode sys M z ok) C.Index Sigma.snd

/-- Passing to consecutive integer names before decoding gives the same
decorated old summand. -/
theorem reverse_acceptedRep [DecidableEq E] {S h : ℕ}
    (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h)
    (cap : Fintype.card V ≤ S) (hs : M.Spherical) (ok : (C.rules N ε).Accepts M z) :
    (sys.family C.Index).IsIso
      (C.reverse sys code ((C.rules N ε).acceptedRep code C.coefficient M cap hs z ok))
      ((C.decode sys M z ok).decorated C.Index (fun d => d.1.2)) := by
  let q := (C.rules N ε).acceptedRep code C.coefficient M cap hs z ok
  apply DecoratedMaps.Family.IsIso.symm (sys.family C.Index)
  exact C.decode_iso sys (M.toRepIso cap hs)
    (fun v => ((C.rules N ε).acceptedRep_role code C.coefficient M cap hs z ok v).symm) ok q.2.property

end Naturality

theorem reverse_respects {h : ℕ} (code : RoleLabel (C.templates (N:=N) (ε:=ε)) ↪ Bits h)
    {S : ℕ} (p q : ((C.rules N ε).acceptedFamily code C.coefficient S).Rep)
    (pq : ((C.rules N ε).acceptedFamily code C.coefficient S).IsIso p q) :
    (sys.family C.Index).IsIso (C.reverse sys code p) (C.reverse sys code q) := by
  obtain ⟨f,hf⟩ := pq
  apply C.decode_iso sys f _ p.2.property q.2.property
  intro v
  have h := congrFun (congrArg Subtype.val hf) (f.vertex v)
  change (p.2.val ∘ f.vertex.symm) (f.vertex v) = q.2.val (f.vertex v) at h
  simpa using h

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
