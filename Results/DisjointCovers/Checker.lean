import Construction

namespace DisjointCovers

def checkCover (n : Nat) (cs : List Class) : Bool :=
  decide (cs.map Prod.fst).Nodup &&
  cs.all (fun (m,a) => decide (2 ≤ m ∧ a < m ∧ a + m < n)) &&
  (List.range n).all (fun x => decide (cs.countP (hit x) = 1))

theorem cover_of_check {n : Nat} {cs : List Class}
    (h : checkCover n cs = true) : Cover n cs := by
  simp only [checkCover, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

def checkLowerBound (n : Nat) (cs : List Class) : Bool :=
  checkCover n cs && cs.all (fun c => decide (3 ≤ c.1))

theorem lowerBound_of_check {n : Nat} {cs : List Class}
    (h : checkLowerBound n cs = true) : Cover n cs ∧ (∀ c ∈ cs, 3 ≤ c.1) := by
  simp only [checkLowerBound, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨cover_of_check h.1, h.2⟩

def checkCoprime (n : Nat) (cs : List Class) : Bool :=
  checkCover n cs && cs.all (fun c => decide (c.1 % 3 ≠ 0))

theorem coprime_of_check {n : Nat} {cs : List Class}
    (h : checkCoprime n cs = true) : Cover n cs ∧ CoprimeToThree cs := by
  simp only [checkCoprime, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨cover_of_check h.1, h.2⟩

def checkPair (n : Nat) (pair : List Class × List Class) : Bool :=
  checkCover n pair.1 && checkCover n pair.2 &&
  pair.1.all (fun c => decide (c.1 ∉ pair.2.map Prod.fst))

theorem pair_of_check {n : Nat} {cs ds : List Class}
    (h : checkPair n (cs, ds) = true) : Cover n cs ∧ Cover n ds ∧ Separate cs ds := by
  simp only [checkPair, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨cover_of_check h.1.1, cover_of_check h.1.2, ?_⟩
  intro m hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  exact h.2 c hc

def checkTable (test : Nat → α → Bool) (start : Nat) : List α → Bool
  | [] => true
  | row :: rest => test start row && checkTable test (start + 1) rest

theorem checkTable_at {test : Nat → α → Bool} {rows : List α} {start i : Nat}
    (h : checkTable test start rows = true) (hi : i < rows.length) :
    test (start + i) rows[i] = true := by
  induction rows generalizing start i with
  | nil => simp at hi
  | cons row rest ih =>
    simp only [checkTable, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hr : i < rest.length := by simpa using hi
      rw [Nat.add_succ, ← Nat.succ_add]
      exact ih h.2 hr

end DisjointCovers
