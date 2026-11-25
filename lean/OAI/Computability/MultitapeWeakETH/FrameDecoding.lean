import OAI.Computability.MultitapeWeakETH.FrameProgram

/-! # Soundness and zero-padding checks for the physical history reader -/

namespace OAI.Computability.MultitapeWeakETH.FrameProgram

open IntegerMultiplication.Code Algorithms.SubexponentialSAT Encoding
open private State base step walk from OAI.Computability.MultitapeWeakETH.FrameProgram

private def escaped (bits : Word) : Word := bits.flatMap fun b => [true,b]

private def closed (rows : List Word) : Word := rows.flatMap fun r => true :: frame r

private theorem frame_eq (bits : Word) : frame bits = escaped bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [escaped,ih]

private theorem records_eq (rows : List Word) : ProgramEncoding.encodeRecords rows = closed rows ++ [false] := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    change true :: (frame r ++ ProgramEncoding.encodeRecords rs) = _
    simp [closed,ih]

/-- The bytes read so far include the unfinished escape or the terminating list bit,
according to the two finite parser flags. -/
private def consumed (s : State) : Word :=
  closed s.2.1 ++
    (bif s.1.1 then true :: (escaped s.2.2.1 ++ (bif s.1.2 then [true] else []))
     else bif s.1.2 then false :: s.2.2.2 else [])

private def WF (s : State) : Prop :=
  (s.1.1 = false → s.2.2.1 = []) ∧ ((s.1.1,s.1.2) ≠ (false,true) → s.2.2.2 = [])

private theorem prefix_step (s : State) (b : Bool) (h : WF s) :
    consumed (step (s,b)) = consumed s ++ [b] ∧ WF (step (s,b)) := by
  rcases s with ⟨⟨v,f⟩,rs,cur,tail⟩
  cases v <;> cases f <;> cases b <;>
    simp_all [WF,step,consumed,closed,frame_eq,escaped,List.append_assoc]

private theorem prefix_walk (xs : Word) (s : State) (h : WF s) :
    consumed (walk xs s) = consumed s ++ xs := by
  induction xs generalizing s with
  | nil => simp [walk]
  | cons b xs ih =>
    change consumed (walk xs (step (s,b))) = _
    obtain ⟨eq,wf⟩ := prefix_step s b h
    rw [ih _ wf,eq,List.append_assoc,List.singleton_append]

theorem read_iff (bits tail : Word) (rows : List Word) :
    read bits = (true,rows,tail) ↔ bits = ProgramEncoding.encodeRecords rows ++ tail := by
  constructor
  · intro hr
    have eq := prefix_walk bits base (by simp [WF,base])
    cases st : walk bits base with
    | mk flags data =>
      obtain ⟨v,f⟩ := flags
      obtain ⟨rs,cur,t⟩ := data
      cases v <;> cases f <;> simp [read,st] at hr
      obtain ⟨rfl,rfl⟩ := hr
      rw [st] at eq
      simpa [consumed,base,closed,records_eq,List.append_assoc] using eq.symm
  · rintro rfl
    exact read_records rows tail

private def zeros (bits : Word) : Bool := (bits.filter id).isEmpty

private theorem zeros_poly : Poly zeros := by
  have empty : Easy (List.isEmpty (α := Bool)) := by
    convert Easy.listCase (X:=Bool) true (Easy.const false) using 1
    funext xs
    cases xs <;> rfl
  exact (Poly.filter id Poly.identity).compose empty.poly

private theorem zeros_iff (bits : Word) : zeros bits = true ↔ bits = List.replicate bits.length false := by
  induction bits with
  | nil => simp [zeros]
  | cons b bs ih => cases b <;> simp_all [zeros,List.replicate_succ]

/-- A single flag validates the framing and all remaining bits. Rejected rows can
be ignored by the subsequent bounded native simulation. -/
def padded (bits : Word) : Bool × List Word :=
  let parsed := read bits
  (parsed.1 && zeros parsed.2.2,parsed.2.1)

theorem padded_poly : Poly padded := by
  have ok := (Easy.fst (X:=Bool) (Y:=List Word × Word)).poly.pair ((Easy.snd.compose Easy.snd).poly.compose zeros_poly)
  exact read_poly.compose ((ok.compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly).pair
    (Easy.snd.compose Easy.fst).poly)

theorem padded_iff (bits : Word) (rows : List Word) :
    padded bits = (true,rows) ↔ ∃ n, bits = ProgramEncoding.encodeRecords rows ++ List.replicate n false := by
  constructor
  · intro h
    rcases hr : read bits with ⟨flag,rs,t⟩
    obtain ⟨⟨hf,hz⟩,rfl⟩ := (by simpa [padded,hr] using h : (flag = true ∧ zeros t = true) ∧ rs = rows)
    subst flag
    exact ⟨t.length, ((read_iff bits t rs).mp hr).trans (congrArg _ ((zeros_iff t).mp hz))⟩
  · rintro ⟨n,rfl⟩
    simp [padded,read_records,zeros_iff]

end OAI.Computability.MultitapeWeakETH.FrameProgram
