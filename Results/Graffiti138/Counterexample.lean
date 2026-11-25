import Graffiti255.Counterexample

namespace Graffiti138

open Graffiti255 (Graph)

private def squareAdj (G : Graph n) (u v : Fin n) : Bool :=
  u != v && (G.adj u v || (List.finRange n).any (fun w => G.adj u w && G.adj v w))

/-- The square graph joins distinct vertices at distance at most two. -/
def square (G : Graph n) : Graph n where
  adj := squareAdj G
  symmetric := by
    intro u v
    have h : (List.finRange n).any (fun w => G.adj u w && G.adj v w) =
        (List.finRange n).any (fun w => G.adj v w && G.adj u w) := by
      simp only [Bool.and_comm]
    unfold squareAdj
    rw [bne_comm, G.symmetric u v, h]
  loopless := by simp [squareAdj]

def degree (G : Graph n) (v : Fin n) : Nat :=
  (List.finRange n).countP (G.adj v)

def IsMaxDegree (G : Graph n) (u : Fin n) : Prop :=
  ∀ v, degree G v ≤ degree G u

/-- The minimum distance over distinct pairs of maximum-degree vertices. -/
def MaxDegreePairDistance (G : Graph n) (d : Nat) : Prop :=
  (∃ a b, a ≠ b ∧ IsMaxDegree G a ∧ IsMaxDegree G b ∧ G.reaches d a b = true) ∧
  ∀ a b k, a ≠ b → IsMaxDegree G a → IsMaxDegree G b → G.reaches k a b = true → d ≤ k

/-- Independent sets in the canonical vertex order. -/
def Independent (G : Graph n) (s : List (Fin n)) : Prop :=
  s.Sublist (List.finRange n) ∧ s.Pairwise (fun a b => G.adj a b = false)

def HasUniqueMaximumIndependentSet (G : Graph n) : Prop :=
  ∃ s, Independent G s ∧ ∀ t, Independent G t → t.length < s.length ∨ t = s

def followsEdges (G : Graph n) : List (Fin n) → Bool
  | a :: b :: rest => G.adj a b && followsEdges G (b :: rest)
  | _ => true

def IsInducedPath (G : Graph n) (p : List (Fin n)) : Prop :=
  p.Nodup ∧ followsEdges G p = true ∧
    ∀ i j : Fin p.length, i.val + 1 < j.val → G.adj (p.get i) (p.get j) = false

/-- The two cases of the conjecture's factor 2+u(G). -/
def Conjecture : Prop :=
  ∀ (n : Nat) (G : Graph n), G.Connected →
    ∀ d, MaxDegreePairDistance (square G) d →
      (∃ p, IsInducedPath G p ∧ 2 * d ≤ p.length) ∧
      (HasUniqueMaximumIndependentSet G → ∃ p, IsInducedPath G p ∧ 3 * d ≤ p.length)

/-- The spine is 0 through 14. The leaves 15,16 are attached to 0,
and the leaves 17,18 are attached to 14. -/
private def orderedAdj (u v : Nat) : Bool :=
  (v ≤ 14 && v == u + 1) ||
  (u == 0 && (v == 15 || v == 16)) ||
  (u == 14 && (v == 17 || v == 18))

private def adjacent (u v : Fin 19) : Bool :=
  orderedAdj (min u.val v.val) (max u.val v.val)

def witness : Graph 19 where
  adj := adjacent
  symmetric := by decide
  loopless := by decide

set_option maxHeartbeats 6000000
set_option maxRecDepth 15000

private theorem reaches_step (G : Graph n) {a b c : Fin n} {k : Nat}
    (hab : G.adj a b = true) (hbc : G.reaches k b c = true) :
    G.reaches (k+1) a c = true := by
  exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr
    ⟨b, List.mem_finRange b, Bool.and_eq_true_iff.mpr ⟨hab, hbc⟩⟩))

private theorem reaches_mono (G : Graph n) (a b : Fin n) {k m : Nat}
    (hkm : k ≤ m) (h : G.reaches k a b = true) : G.reaches m a b = true := by
  induction m with
  | zero => simpa [Nat.eq_zero_of_le_zero hkm] using h
  | succ m ih =>
      by_cases hk : k = m + 1
      · simpa [hk] using h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (ih (by omega)))

private def spinePosition (v : Fin 19) : Nat :=
  if v.val < 15 then v.val else if v.val < 17 then 0 else 14

private def nextVertex (u v : Fin 19) : Fin 19 :=
  if 15 ≤ u.val then Fin.ofNat 19 (spinePosition u)
  else if u.val < spinePosition v then Fin.ofNat 19 (u.val + 1)
  else if spinePosition v < u.val then Fin.ofNat 19 (u.val - 1)
  else v

private def routeMeasure (u v : Fin 19) : Nat :=
  if u = v then 0 else
    (spinePosition u - spinePosition v) + (spinePosition v - spinePosition u) +
      (if 15 ≤ u.val then 1 else 0) + (if 15 ≤ v.val then 1 else 0)

private theorem routing_step :
    ∀ (u v : Fin 19), u ≠ v →
      witness.adj u (nextVertex u v) = true ∧ routeMeasure (nextVertex u v) v < routeMeasure u v := by
  decide

theorem witness_connected : witness.Connected := by
  intro u v
  exact route u v
where
  route (u v : Fin 19) : ∃ k, witness.reaches k u v = true := by
    by_cases heq : u = v
    · exact ⟨0, by simp [Graph.reaches, heq]⟩
    · obtain ⟨hAdj, hDecrease⟩ := routing_step u v heq
      obtain ⟨k, h⟩ := route (nextVertex u v) v
      exact ⟨k+1, reaches_step witness hAdj h⟩
  termination_by routeMeasure u v
  decreasing_by exact hDecrease

/-- Check all independent selections, carrying the selected prefix in reverse. -/
private def checkIndependent (G : Graph n) (ok : List (Fin n) → Bool) :
    List (Fin n) → List (Fin n) → Bool
  | [], selected => ok selected.reverse
  | a :: rest, selected =>
      checkIndependent G ok rest selected &&
        (!(selected.all (fun b => !G.adj b a)) || checkIndependent G ok rest (a :: selected))

private theorem checkIndependent_complete {G : Graph n} {ok : List (Fin n) → Bool}
    {s xs selected : List (Fin n)} (hs : s.Sublist xs)
    (hi : (selected.reverse ++ s).Pairwise (fun a b => G.adj a b = false))
    (hc : checkIndependent G ok xs selected = true) : ok (selected.reverse ++ s) = true := by
  induction hs generalizing selected with
  | slnil => simpa [checkIndependent] using hc
  | cons a _ ih =>
      exact ih hi (Bool.and_eq_true_iff.mp hc).1
  | cons_cons a _ ih =>
      have hAllowed : selected.all (fun b => !G.adj b a) = true := by
        apply List.all_eq_true.mpr
        intro b hb
        have hn := (List.pairwise_append.mp hi).2.2 b (by simpa using hb) a List.mem_cons_self
        simp [hn]
      have hNext := (Bool.and_eq_true_iff.mp hc).2
      simp only [hAllowed, Bool.not_true, Bool.false_or] at hNext
      simpa [List.reverse_cons, List.append_assoc] using
        ih (selected := a :: selected) (by simpa [List.reverse_cons, List.append_assoc] using hi) hNext

def maximumSet : List (Fin 19) := [1, 3, 5, 7, 9, 11, 13, 15, 16, 17, 18]

private theorem maximumSet_independent :
    maximumSet.Sublist (List.finRange 19) ∧
      maximumSet.Pairwise (fun a b => witness.adj a b = false) := by
  decide

private theorem independentSetCertificate :
    checkIndependent witness (fun s => (s.length < maximumSet.length) || s == maximumSet)
      (List.finRange 19) [] = true := by
  decide

theorem unique_maximum_independent_set : HasUniqueMaximumIndependentSet witness := by
  refine ⟨maximumSet, maximumSet_independent, ?_⟩
  intro s hs
  have h := checkIndependent_complete hs.1 (selected := []) (by simpa using hs.2) independentSetCertificate
  simp only [List.reverse_nil, List.nil_append] at h
  rcases Bool.or_eq_true_iff.mp h with hSmall | hSame
  · exact Or.inl (of_decide_eq_true hSmall)
  · exact Or.inr (beq_iff_eq.mp hSame)

private theorem maximum_square_vertices :
    ∀ u : Fin 19, (∀ v : Fin 19, degree (square witness) v ≤ degree (square witness) u) ↔
      (u = 1 ∨ u = 13) := by
  decide

private theorem square_reach_checks :
    (square witness).reaches 6 1 13 = true ∧
      (square witness).reaches 5 1 13 = false ∧
      (square witness).reaches 5 13 1 = false := by
  decide

theorem maximum_degree_pair_distance : MaxDegreePairDistance (square witness) 6 := by
  refine ⟨⟨1, 13, by decide,
    (maximum_square_vertices 1).mpr (Or.inl rfl),
    (maximum_square_vertices 13).mpr (Or.inr rfl), square_reach_checks.1⟩, ?_⟩
  intro a b k hab ha hb hr
  by_cases hk : 6 ≤ k
  · exact hk
  · have hshort := reaches_mono (square witness) a b (m := 5) (by omega) hr
    rcases (maximum_square_vertices a).mp ha with rfl | rfl <;>
      rcases (maximum_square_vertices b).mp hb with rfl | rfl
    · exact (hab rfl).elim
    · rw [square_reach_checks.2.1] at hshort
      contradiction
    · rw [square_reach_checks.2.2] at hshort
      contradiction
    · exact (hab rfl).elim

/-- Whether a simple path ending at u can take k more steps without revisiting. -/
private def canExtend (G : Graph n) : Nat → Fin n → List (Fin n) → Bool
  | 0, _, _ => true
  | k+1, u, used =>
      (List.finRange n).any (fun v => G.adj u v && !used.contains v &&
        canExtend G k v (v :: used))

private theorem extension_complete {G : Graph n} {u : Fin n} {used rest : List (Fin n)}
    (hChain : followsEdges G (u :: rest) = true)
    (hNodup : rest.Nodup) (hFresh : ∀ v ∈ rest, v ∉ used)
    {k : Nat} (hk : k ≤ rest.length) : canExtend G k u used = true := by
  induction k generalizing u used rest with
  | zero => rfl
  | succ k ih =>
      cases rest with
      | nil => simp at hk
      | cons v tail =>
          have hlink : G.adj u v = true ∧ followsEdges G (v :: tail) = true :=
            Bool.and_eq_true_iff.mp hChain
          have hdistinct := List.nodup_cons.mp hNodup
          have hnext : canExtend G k v (v :: used) = true :=
            ih hlink.2 hdistinct.2 (fun w hw hwUsed => by
              rcases List.mem_cons.mp hwUsed with rfl | hOld
              · exact hdistinct.1 hw
              · exact hFresh w (List.mem_cons_of_mem _ hw) hOld) (by simpa using hk)
          have hUnused := hFresh v List.mem_cons_self
          exact List.any_eq_true.mpr
            ⟨v, List.mem_finRange v, by simp [hlink.1, hUnused, hnext]⟩

private theorem noSeventeenStepPath :
    ∀ u : Fin 19, canExtend witness 17 u [u] = false := by
  decide

theorem every_simple_path_has_at_most_seventeen_vertices (p : List (Fin 19))
    (hDistinct : p.Nodup) (hChain : followsEdges witness p = true) :
    p.length ≤ 17 := by
  cases p with
  | nil => simp
  | cons u rest =>
      by_cases h : (u :: rest).length ≤ 17
      · exact h
      · have hDistinct := List.nodup_cons.mp hDistinct
        have hExt := extension_complete hChain hDistinct.2
          (used := [u]) (fun v hv hvUsed => by
            have : v = u := by simpa using hvUsed
            exact hDistinct.1 (this ▸ hv)) (k := 17) (by simp at h; omega)
        rw [noSeventeenStepPath u] at hExt
        contradiction

private def longestPath : List (Fin 19) :=
  [15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17]

theorem induced_path_of_order_seventeen :
    IsInducedPath witness longestPath ∧ longestPath.length = 17 := by
  unfold IsInducedPath
  decide

theorem conjecture138_false : ¬ Conjecture := by
  intro conjecture
  obtain ⟨p, hp, hlen⟩ :=
    (conjecture 19 witness witness_connected 6 maximum_degree_pair_distance).2
      unique_maximum_independent_set
  have hshort := every_simple_path_has_at_most_seventeen_vertices p hp.1 hp.2.1
  omega

#print axioms conjecture138_false

end Graffiti138
