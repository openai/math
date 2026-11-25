import OAI.Computability.NearSquareRoot.InterchangeBQuestCore

/-!
# Reindexing a bounded family of oracle programs

A single command can be used on any selected subfamily and with extra parent
budget. Child requests can have a new index type when the issue and reply
trees of the calls agree. All of these operations preserve the original
recursive price and the two independent child peak allowances.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.Space

variable {I X Y Z : Type} {job : Job Y} {w : I → ℕ} {uses : I → List Y}
    {p q : I → Tree} {r : Regime I} {n l N L : I → ℕ} {limit : ℤ} {zone : I → Y → Prop}

theorem Body.pull (h : Body job w uses p q) (g : X → I) :
    Body job (w ∘ g) (uses ∘ g) (p ∘ g) (q ∘ g) := by
  obtain ⟨cmd,K,exec⟩ := h.build
  exact ⟨cmd,K, fun x => exec (g x)⟩

/-- Map the typed query indices while reusing the original caller command
and the actual issue/reply trees sent through register zero. -/
theorem Body.mapJob (h : Body job w uses p q) (job' : Job Z) (f : I → Y → Z)
    (issue : ∀ i y, y ∈ uses i → job'.issue (f i y) = job.issue y)
    (reply : ∀ i y, y ∈ uses i → job'.reply (f i y) = job.reply y) :
    Body job' w (fun i => (uses i).map (f i)) p q := by
  obtain ⟨cmd,K,exec⟩ := h.build
  refine ⟨cmd,K,fun i parent env price S D calls d base hd => ?_⟩
  apply (exec i parent env (price ∘ f i) S D ?_ d base hd).mono
  · simp [List.map_map]
  · exact le_rfl
  · exact le_rfl
  · intro y hy deck depth hdeck
    rw [← issue i y hy, ← reply i y hy]
    exact calls (f i y) (List.mem_map_of_mem hy) deck depth hdeck

theorem BHop.pull (h : BHop job r n l zone limit p q) (g : X → I) :
    BHop job (r.pull g) (n ∘ g) (l ∘ g) (zone ∘ g) limit (p ∘ g) (q ∘ g) := by
  obtain ⟨uses,safe,price,⟨k,run⟩⟩ := h.safe
  exact ⟨uses ∘ g, fun x => safe (g x), fun x => price (g x), k, run.pull g⟩

theorem BHop.monoSize (h : BHop job r n l zone limit p q) (hn : ∀ i, n i ≤ N i)
    (hl : ∀ i, l i ≤ L i) : BHop job r N L zone limit p q := by
  obtain ⟨uses,safe,price,⟨k,run⟩⟩ := h.safe
  refine ⟨uses,safe,price,k,run.mono fun i => ?_⟩
  exact Nat.mul_le_mul (hn i) (Nat.add_le_add_right (hl i) _)

theorem BHop.zone_mono (h : BHop job r n l zone limit p q) {zone' : I → Y → Prop}
    (hz : ∀ i y, zone i y → zone' i y) : BHop job r n l zone' limit p q := by
  obtain ⟨uses,safe,price,body⟩ := h.safe
  exact ⟨uses, fun i y hy => hz i y (safe i y hy), price, body⟩

/-- Replace the job index type and admissible-request predicate together.
The equalities need hold only on legal calls, and the request count is exact. -/
theorem BHop.mapJob (h : BHop job r n l zone limit p q) (job' : Job Z) (f : I → Y → Z)
    (zone' : I → Z → Prop) (hz : ∀ i y, zone i y → zone' i (f i y))
    (issue : ∀ i y, zone i y → job'.issue (f i y) = job.issue y)
    (reply : ∀ i y, zone i y → job'.reply (f i y) = job.reply y) :
    BHop job' r n l zone' limit p q := by
  obtain ⟨uses,safe,price,⟨k,run⟩⟩ := h.safe
  refine ⟨fun i => (uses i).map (f i), ?_, ?_, k, run.mapJob job' f
    (fun i y hy => issue i y (safe i y hy)) (fun i y hy => reply i y (safe i y hy))⟩
  · intro i z hd
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hd
    exact hz i y (safe i y hy)
  · simpa only [List.length_map] using price

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
