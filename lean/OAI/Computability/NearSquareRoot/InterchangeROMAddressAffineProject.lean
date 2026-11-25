import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffine

/-! # The fixed binary field-address program on native shape headers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace AffineAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
  IntegerMultiplication.Bits IntegerMultiplication.Strip IntegerMultiplication.Adic
  IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims

/-- A field may have arbitrary surrounding dimensions. The three shape lists
are precisely the data read by the program. -/
structure Geometry where
  pre : Tape
  field : Tape
  post : Tape
  preSolid : solid pre
  fieldSolid : solid field
  postSolid : solid post

namespace Geometry

abbrev desc (g : Geometry) := (shape g.pre, shape g.field, shape g.post)

abbrev rows (g : Geometry) := Board g.pre (layout g.field) g.post

abbrev bits (g : Geometry) := 2 * Nat.clog 2 (room g.field) + 3

def budget (g : Geometry) : ℕ :=
  size g.desc + (room g.field + 1)^2 + g.rows.count * (g.bits + 2) + 1

noncomputable def result (g : Geometry) : Tree :=
  stripe g.rows (fun x => send (born ((layout g.field).index x.2.1).val))

theorem bitSize (g : Geometry) (x : Pin g.field) :
    (send (born ((layout g.field).index x).val)).count ≤ g.bits := by
  change size (born _) ≤ _
  rw [size_word]
  have c : ((layout g.field).index x).val ≤ room g.field := by
    simpa only [Dims.space] using ((layout g.field).index x).isLt.le
  have a := Carry.depth ((layout g.field).index x).val
  have b := Nat.clog_monotone 2 c
  unfold bits
  omega

private theorem counts (g : Geometry) :
    room g.pre ≤ g.budget ∧ room g.field ≤ g.budget ∧ room g.post ≤ g.budget := by
  have hp := wide _ g.preSolid
  have hd := wide _ g.fieldSolid
  have hs := wide _ g.postSolid
  have ds := Nat.mul_pos hd hs
  have b := Nat.le_mul_of_pos_right (room g.pre * (room g.field * room g.post))
    (by positivity : 0 < g.bits+2)
  have p := Nat.le_mul_of_pos_right (room g.pre) ds
  have h := Nat.le_mul_of_pos_left (room g.field * room g.post) hp
  have d := Nat.le_mul_of_pos_right (room g.field) hs
  have s := Nat.le_mul_of_pos_left (room g.post) hd
  unfold budget rows Board
  simp only [Series.count_cart,Dims.space]
  omega

private theorem ruler (proj : Geometry → Tape) (valid : ∀ g, solid (proj g))
    (pick : ∃ f : List Tally × List Tally × List Tally → List Tally,
      Easy f ∧ ∀ g : Geometry, f g.desc = shape (proj g))
    (sz : ∀ g, room (proj g) ≤ g.budget) :
    Carries (fun g : Geometry => (g.budget : ℝ)) (fun g => send g.desc)
      (fun g => send (tally (layout (proj g)).count)) := by
  have pos (g : Geometry) : (1 : ℝ) ≤ g.budget := by
    exact_mod_cast (show 1 ≤ g.budget by unfold budget; omega)
  have data : Volume (fun g : Geometry => (g.budget : ℝ)) (fun g => send g.desc) := by
    refine ⟨1, fun g => ?_⟩
    simp only [Nat.cast_one,one_mul]
    exact_mod_cast (show size g.desc ≤ g.budget by unfold budget; omega)
  obtain ⟨f,fe,eq⟩ := pick
  have read := Carries.func pos data f fe
  simp_rw [eq] at read
  have prog := Dims.unary.on (fun g : Geometry => (⟨proj g,valid g⟩ : {s : Tape // solid s}))
  simp only [Dims.space]
  exact read.sequence ⟨pos, _, prog, 2, fun g => by
    change (room (proj g) : ℝ)+1 ≤ 2*(g.budget:ℝ)
    have sm : (room (proj g) : ℝ) ≤ g.budget := by exact_mod_cast (sz g)
    linarith [pos g]⟩

theorem carries : Carries (fun g : Geometry => (g.budget : ℝ))
    (fun g => send g.desc) result := by
  let P (g : Geometry) := layout g.pre
  let H (g : Geometry) := layout g.field
  let B (g : Geometry) := layout g.post
  have pp (g : Geometry) : 1 ≤ (P g).count := by rw [show (P g).count = room g.pre from Dims.space _]; exact wide _ g.preSolid
  have ph (g : Geometry) : 1 ≤ (H g).count := by rw [show (H g).count = room g.field from Dims.space _]; exact wide _ g.fieldSolid
  have pb (g : Geometry) : 1 ≤ (B g).count := by rw [show (B g).count = room g.post from Dims.space _]; exact wide _ g.postSolid
  have rp := ruler Geometry.pre Geometry.preSolid ⟨_,Easy.fst, fun _ => rfl⟩ (fun g => (counts g).1)
  have rh := ruler Geometry.field Geometry.fieldSolid ⟨_, Easy.snd.compose Easy.fst, fun _ => rfl⟩
    (fun g => (counts g).2.1)
  have rb := ruler Geometry.post Geometry.postSolid ⟨_, Easy.snd.compose Easy.snd, fun _ => rfl⟩
    (fun g => (counts g).2.2)
  let val (g : Geometry) (x : Pin g.field) := send (born ((H g).index x).val)
  have ranks := binaryRanks H rh (fun g => by
    exact_mod_cast (show ((H g).count+1)^2 ≤ g.budget by
      unfold budget
      simp only [H,Dims.space]
      omega))
  have full (g : Geometry) : (P g).count * ((H g).count * ((B g).count * (g.bits+2))) ≤ g.budget := by
    have a : g.rows.count * (g.bits+2) ≤ g.budget := by unfold budget; omega
    simpa only [rows,Board,Series.count_cart,P,H,B,Nat.mul_assoc] using a
  have r := appendCopies H B val bits bitSize ph pb rh rb ranks (fun g => by
    exact_mod_cast (Nat.le_mul_of_pos_left _ (pp g)).trans (full g))
  apply prepend P (fun g => (H g).cart (B g)) (fun g x => val g x.1) bits
    (fun g x => bitSize _ x.1) pp (fun g => by rw [Series.count_cart]; exact Nat.mul_pos (ph g) (pb g))
    rp r
  intro g
  rw [Series.count_cart,Nat.mul_assoc (H g).count]
  exact_mod_cast full g

/-- The existential command in this contract is shared by every radix, field
width and choice of spectator dimensions. -/
theorem program : Code.Task budget (fun g => send g.desc) result := by
  obtain ⟨_,u,run,K,bound⟩ := carries.runs
  apply run.bound K
  intro g
  have h := bound g
  change (u g : ℝ) + 1 ≤ (K : ℝ) * (g.budget : ℝ) at h
  have b : u g + 1 ≤ K * g.budget := by exact_mod_cast h
  rw [Nat.mul_add]
  omega

end Geometry
end AffineAddress

end NearSquareRoot
end Computability
end OAI
