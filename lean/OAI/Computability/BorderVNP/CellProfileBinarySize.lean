import OAI.Computability.BorderVNP.CellCompactFields
import OAI.Computability.BorderVNP.CellProfileBudget

/-! # Logarithmic numeric fields of the sparse profile descriptor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open Prefix

private theorem wordIs_fields (as : List NatExpr) (j B : ℕ) (h : ∀ a ∈ as, a.field ≤ B) :
    (wordIs as j).Fields B := by
  induction as generalizing j with
  | nil => trivial
  | cons a as ih =>
    exact ⟨(Term.fields_equal ..).mpr ⟨h _ List.mem_cons_self,trivial⟩,ih _ (fun j hj => h _ (.tail _ hj))⟩

private theorem port_fields (off : ℕ) (p : Port) (i k : NatExpr) {B : ℕ} (ho : off ≤ B)
    (hp : PortBound B p) (hi : i.field ≤ B) (hk : k.field ≤ B) : (portExpr off p i k).field ≤ B := by
  simp [portExpr,Port.expr,NatExpr.field,ho,hp.1,hp.2.1,hp.2.2,hi,hk]

private theorem selectTerm_fields (off : ℕ) (p : Port) (w t : ℕ) (i : NatExpr) {B : ℕ}
    (ho : off ≤ B) (hp : PortBound B p) (hw : w ≤ B) (hi : i.field ≤ B) :
    (selectTerm off p w t i).Fields B := by
  apply wordIs_fields
  intro a ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  exact port_fields _ _ _ _ ho hp hi ((List.mem_range.mp hk).le.trans hw)

private theorem flag_fields' (base cap : ℕ) (i k : NatExpr) {B : ℕ} (hb : base ≤ B) (hc : cap+1 ≤ B)
    (hi : i.field ≤ B) (hk : k.field ≤ B) : (flagTerm base cap i k).Fields B := by
  simp [flagTerm,Term.Fields,NatExpr.field,hb,hc,hi,hk]

private theorem portBound_mono {M B : ℕ} {p : Port} (h : PortBound M p) (hle : M ≤ B) : PortBound B p :=
  ⟨h.1.trans hle,h.2.1.trans hle,h.2.2.trans hle⟩

private theorem nodes_range (off : ℕ) (s : Port) (w terms : ℕ) :
    (Term.any ((List.range terms).map fun t => selectTerm off s w t (.index 0))).nodes ≤ maxNodes w terms := by
  rw [Term.nodes_any, List.length_map, List.length_range]
  have hh := sum_map_le ((List.range terms).map fun t => selectTerm off s w t (.index 0)) Term.nodes
    (10*w+1) (fun v hv => by obtain ⟨_,_,rfl⟩ := List.mem_map.mp hv; simp)
  simp only [List.length_map,List.length_range] at hh
  unfold maxNodes
  nlinarith

/-- The largest literal in the descriptor is bounded cubically by the numeric
cell scale. Scratch offsets are charged alongside original wire and flag offsets. -/
theorem profileGen_field_le {base off copies w M : ℕ} {s : Port} {hist : List ℕ} {routes : List Route}
    (hbase : base ≤ (M+1)^3) (hoff : off ≤ (M+1)^3) (hc : copies ≤ M) (hw : w ≤ M)
    (hh : hist.length ≤ M) (hs : PortBound M s)
    (hroute : ∀ r ∈ routes, r.term ≤ M ∧ r.lanes ≤ M ∧ PortBound M r.original ∧ PortBound M r.compact) :
    (profileGen base off copies s w hist routes).field ≤ 100*(M+2)^3+1 := by
  let B := 100*(M+2)^3
  have hMB : M+3 ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have ho : off ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have hs' : PortBound B s := portBound_mono hs (by omega)
  have horig (t : ℕ) (ht : t ≤ M) : termBase base copies t ≤ B := by
    unfold termBase
    calc
      _ ≤ (M+1)^3+M*((M+1)*(M+1)) := by gcongr
      _ ≤ _ := by dsimp [B]; nlinarith [Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have hmax : maxNodes w hist.length ≤ B := by
    unfold maxNodes
    calc
      _ ≤ (40*M+40)*(M+1) := by gcongr
      _ ≤ _ := by dsimp [B]; nlinarith [Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have hrow : 4*(10*w+1)+19 ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (M^2),Nat.zero_le (M^3)]
  change _ ≤ B+1
  refine max_le ?_ (max_le (field_sequence_le _ ?_) (field_sequence_le _ ?_))
  · apply Nat.le_succ_of_le
    apply max_le (hc.trans (by omega))
    apply Term.guard_field_le
    · apply Term.fields_any
      intro a ha
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
      exact selectTerm_fields _ _ _ _ _ ho hs' (by omega) (Nat.zero_le _)
    · exact (nodes_range off s w hist.length).trans hmax
  · intro st hst
    obtain ⟨⟨adv,t⟩,hp,rfl⟩ := List.mem_map.mp hst
    have ht : t < hist.length := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hp)).1
    have hb := horig t (ht.le.trans hh)
    apply max_le
    · exact generator_field_le _ _ _ _ B hb.step (by omega) (by omega)
        (selectTerm_fields _ _ _ _ _ ho hs' (by omega) (Nat.zero_le _))
        (by simp [selectTerm_nodes]; omega)
    · apply Nat.le_succ_of_le
      split <;> rename_i h <;> apply Term.guard_field_le
      · exact flag_fields' _ _ _ _ hb (by omega) (by change copies ≤ B; omega) (by change adv ≤ B; omega)
      · simp; omega
      · trivial
      · change 1 ≤ B; omega
  · intro st hst
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hst
    obtain ⟨ht,hl,hpo,hpc⟩ := hroute r hr
    have hb := horig r.term ht
    apply Nat.le_succ_of_le
    apply max_le (Term.guard_field_le (.lit _) trivial (by change 1 ≤ B; omega))
    refine max_le (show copies ≤ B by omega) (max_le (show copies+1 ≤ B by omega)
      (max_le (show r.lanes ≤ B by omega) (Term.guard_field_le _ ?_ ?_)))
    · simp only [laneTest,Term.implies,Term.Fields,Term.fields_equal]
      refine ⟨⟨selectTerm_fields _ _ _ _ _ ho hs' (by omega) (by change 2 ≤ B; omega),
        flag_fields' _ _ _ _ hb (by omega) (by change 2 ≤ B; omega) (by change 1 ≤ B; omega)⟩,?_,?_⟩
      · exact port_fields _ _ _ _ ho (portBound_mono hpo (by omega)) (by change 2 ≤ B; omega) (Nat.zero_le _)
      · exact port_fields _ _ _ _ ho (portBound_mono hpc (by omega)) (by change 1 ≤ B; omega) (Nat.zero_le _)
    · simp [laneTest,Term.implies,Term.nodes]; omega

/-- The public descriptor length is linear in its list of local terms and routes and
in the selector width, with only a binary-length factor for the potentially large
repeat counts and addresses. -/
theorem profileGen_binary_length_le {base off copies w M : ℕ} {s : Port} {hist : List ℕ} {routes : List Route}
    (hbase : base ≤ (M+1)^3) (hoff : off ≤ (M+1)^3) (hc : copies ≤ M) (hw : w ≤ M)
    (hh : hist.length ≤ M) (hs : PortBound M s)
    (hroute : ∀ r ∈ routes, r.term ≤ M ∧ r.lanes ≤ M ∧ PortBound M r.original ∧ PortBound M r.compact) :
    (profileGen base off copies s w hist routes).code.length ≤
      10000*(w+1)*(hist.length+routes.length+1)*(2*(100*(M+2)^3+1).size+10) := by
  apply (profileGen_code_le ..).trans
  gcongr
  exact Nat.size_le_size (profileGen_field_le hbase hoff hc hw hh hs hroute)

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
