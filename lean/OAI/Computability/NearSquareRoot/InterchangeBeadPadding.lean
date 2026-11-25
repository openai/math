import OAI.Computability.NearSquareRoot.InterchangeBeadRecords

/-!
# Known prefixes on variable-length bead records

Copy a tally from the outer header to each record. Padding and removing the
prefix scan each record once. Neither direction needs the original row length
to be recoverable from the header.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload.BeadPadding

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom

variable {I : Type} {A T : I → Type} {r : Regime I} {L : I → ℕ}
    (s : (i : I) → Series (A i)) (st : Station r s)
    (pad : I → ℕ) (hp : r.Has (tally ∘ pad))

noncomputable section

def stream (words : (i : I) → A i → List Bead) :=
  stackRun s fun i a => send (words i a)

include st hp in
private theorem rowwise (words : (i : I) → A i → List Bead)
    (active : Alive r (fun i => (s i).count) L (stream s words))
    (f : Tally × List Bead → List Bead) (hf : Easy f) :
    Drive r (fun i => (s i).count) L (stream s words)
      (stream s fun i a => f (tally (pad i), words i a)) := by
  have heads := (Drive.fetch st.1 active).chain (clones st (fun _ => le_refl _) _ hp)
  have copied := Rip.coalesce (fun i _ => send (tally (pad i))) (fun i a => send (words i a))
    heads (Drive.self st.1 active)
  let joined i := (s i).tab (fun a => (tally (pad i), words i a))
  have physical : Rip r (fun i => (s i).count) L (together r.header (stream s words))
      (send ∘ joined) := by
    change Rip _ _ _ _ (fun i => stripe (s i) (fun a => send (tally (pad i), words i a))) at copied
    simpa only [stripe_eq', joined, Function.comp_def] using copied
  change Rip _ _ _ (together r.header (stream s words))
    (fun i => stripe (s i) (fun a => send (f (tally (pad i),words i a))))
  simpa only [stripe_eq',joined,Series.map_tab,Function.comp_def] using
    Fatigue.act physical (List.map f) hf.mapping

def words (u : (i : I) → Series (T i)) (v : (i : I) → A i → T i → Bead) (i : I) (a : A i) :=
  (u i).tab (v i a)

def padded (u : (i : I) → Series (T i)) (v : (i : I) → A i → T i → Bead) (i : I) (a : A i) :=
  List.replicate (pad i) (0 : Bead) ++ words u v i a

private theorem cloth_eq (u : (i : I) → Series (T i)) (v : (i : I) → A i → T i → Bead) :
    cloth s u v = stream s (words u v) := by
  funext i
  simp only [cloth, stream, stackRun, stripe_eq', words]

include st hp in
theorem charge (u : (i : I) → Series (T i)) (v : (i : I) → A i → T i → Bead)
    (fit : ∀ i, (u i).count ≤ L i) :
    Drive r (fun i => (s i).count) L (cloth s u v) (stream s (padded pad u v)) ∧
    Drive r (fun i => (s i).count) L (stream s (padded pad u v)) (cloth s u v) := by
  have plain := cloth_size s u st v fit
  rw [cloth_eq] at plain ⊢
  let add (z : Tally × List Bead) := fill (0:Bead) z.1 ++ z.2
  have addEasy : Easy add := by unfold add; fun_prop
  have prep : Drive r (fun i => (s i).count) L (stream s (words u v)) (stream s (padded pad u v)) := by
    change Drive _ _ _ _ (stream s fun i a => List.replicate (pad i) 0 ++ words u v i a)
    simpa only [add,fill_eq,tally_length] using rowwise s st pad hp (words u v) plain add addEasy
  refine ⟨prep, ?_⟩
  let cut (z : Tally × List Bead) := (cutLists z).2
  have cutEasy : Easy cut := (easy_cut easy_id).sndCompose
  have eq (i : I) a : cut (tally (pad i), padded pad u v i a) = words u v i a := by
    simp [cut,cutLists,padded]
  simpa only [eq] using rowwise s st pad hp (padded pad u v) prep.idle cut cutEasy

end
end InterchangePayload.BeadPadding

end NearSquareRoot
end Computability
end OAI
