import OAI.Computability.BorderVNP.CubeLabelISAFramePass

/-! # Separation of the incident-directory inputs from the bin cache

The sparse memory hypothesis refers to the addresses of the cells actually read:
the head, the delivery total, five addresses per incidence, and the cache words.
It permits empty lists and any physical order of the incident nodes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

/-- Probe addresses along the actual pointer chain, including the opposite-end labels. -/
def chainProbes (nodes labels : ℕ) (m : ℕ → ℕ) : ℕ → List Incident → List ℕ
  | _, [] => []
  | ptr, e :: es =>
    let a := nodeAddr nodes ptr
    [a,a+1,a+2,a+3,labels+e.other] ++ chainProbes nodes labels m (m a) es

/-- The input addresses used when scanning one cell in the cable and delivery bins. -/
def Frame.probes (p : Frame) (c : ℕ) (m : ℕ → ℕ) (es : List Incident) : List ℕ :=
  (p.heads+c) :: (p.demands+c) :: chainProbes p.nodes p.labels m (m (p.heads+c)) es

private theorem chain_transport (q : Query) (w : ℕ) (m n : ℕ → ℕ) (ptr : ℕ) (es : List Incident)
    (ch : Chain m q.nodes ptr es) (room : q.room w m ptr es)
    (same : ∀ a ∈ chainProbes q.nodes q.labels m ptr es, n a = m a) :
    Chain n q.nodes ptr es ∧ q.room w n ptr es ∧ q.sums n es = q.sums m es := by
  induction ch with
  | nil => exact ⟨.nil,trivial,rfl⟩
  | @cons ptr e es live dir other width tail ih =>
    let a := nodeAddr q.nodes ptr
    have word (j) (hj : j ∈ ([a,a+1,a+2,a+3,q.labels+e.other] : List ℕ)) : n j = m j :=
      same _ (List.mem_append_left _ hj)
    have next : n a = m a := word a (by simp)
    obtain ⟨ch',room',sums⟩ := ih room.2.2.2 fun j hj => same j (List.mem_append_right _ hj)
    have eEq : q.weights n e = q.weights m e := by
      simp only [Query.weights,word (q.labels+e.other) (by simp)]
    refine ⟨.cons live ((word _ (by simp [a])).trans dir) ((word _ (by simp [a])).trans other)
      ((word _ (by simp [a])).trans width) (next ▸ ch'),⟨room.1,room.2.1,room.2.2.1,next ▸ room'⟩,?_⟩
    have add (f : ℕ → ℕ) : q.sums f (e::es) =
        ((q.weights f e).1+(q.sums f es).1,(q.weights f e).2+(q.sums f es).2) := by
      simp [Query.sums]
    rw [add,add,eEq,sums]

/-- Matching words at the physical input addresses preserve the fit conditions and
both incident numerators, including those for a delivery bin. -/
theorem Frame.transport (p : Frame) (w c v i : ℕ) (m n : ℕ → ℕ) (es : List Incident)
    (room : p.room w c v i m es) (same : ∀ a ∈ p.probes c m es, n a = m a) :
    p.room w c v i n es ∧ p.incident c v i n es = p.incident c v i m es := by
  have head : n (p.heads+c) = m (p.heads+c) := same _ (by simp [probes])
  have demand : n (p.demands+c) = m (p.demands+c) := same _ (by simp [probes])
  rcases room with ⟨hz,cache,room⟩
  by_cases hi : i < p.Z^2
  · simp only [hi,ite_true] at room
    obtain ⟨fit,chain,safe,old,new⟩ := room
    obtain ⟨chain',safe',sums⟩ := chain_transport (p.query c v i) w m n _ es chain safe
      (fun a ha => same a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)))
    simp only [Frame.room, Frame.incident,hi,ite_true,head,sums]
    exact ⟨⟨hz,cache,fit,chain',safe',old,new⟩,trivial⟩
  · simp only [hi,ite_false] at room
    simp only [Frame.room, Frame.incident,hi,ite_false,demand]
    exact ⟨⟨hz,cache,room⟩,trivial⟩

/-- Disjoint input and cache addresses suffice for the scan hypotheses throughout a
pass. Only the preceding bins have been written at ordinal `i`. -/
theorem Frame.pass_room (p : Frame) (commit : Bool) (w c v i : ℕ) (m : ℕ → ℕ) (es : List Incident)
    (room : p.room w c v i m es)
    (off : ∀ a ∈ p.probes c m es, ∀ j < i, a ≠ p.cacheAddr j) :
    let n := (p.bins c v m es).memory commit m i
    p.room w c v i n es ∧ p.incident c v i n es = p.incident c v i m es := by
  apply p.transport w c v i m _ es room
  intro a ha
  cases commit with
  | false => rfl
  | true => exact (p.bins c v m es).image_off m i a (off a ha)

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
