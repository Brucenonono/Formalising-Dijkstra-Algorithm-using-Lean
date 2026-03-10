import Mathlib
open SimpleGraph
/-
# 1. Environment Setup
-/
-- V are vertices
variable {V : Type} [Fintype V] [DecidableEq V]

structure WeightedGraph (V : Type) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  connect : G.Connected
  weight : V → V → ENNReal
  no_edge : ∀ u v, ¬G.Adj u v → weight u v = ⊤
  source : V

structure DijkstraState (V : Type) where
  visited   : Finset V
  distances : V → ENNReal

namespace WeightedGraph

-- Computes the total weight of a walk by summing edge weights.
noncomputable def walk_weight (inst : WeightedGraph V) {u v : V} : inst.G.Walk u v → ENNReal
  | .nil => 0
  | .cons (u := a) (v := b) h w => inst.weight a b + walk_weight inst w
/-
# 2. The Algorithm
Implementing computable versions of the greedy step and the loop.
-/

-- Computable: Picks the unvisited vertex with the minimum distance label
noncomputable def choose_next (inst : WeightedGraph V) (state : DijkstraState V) : V :=
  let unvisited := Finset.univ \ state.visited
  if h : unvisited.Nonempty then
    (Finset.exists_min_image unvisited state.distances h).choose
  else inst.source -- technically we dont enter this

-- choose_next choose an unvisited
lemma h_unvisited {inst : WeightedGraph V} {state : DijkstraState V}
    (hif : state.visited.card < Fintype.card V) :
    inst.choose_next state ∉ state.visited := by
  have hunvisited : (Finset.univ \ state.visited).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
    intro hle
    have hge : state.visited.card ≤ Fintype.card V := Finset.card_le_univ _
    have heq : state.visited.card = Fintype.card V :=
      Nat.le_antisymm hge (Finset.card_le_card hle |>.trans_eq (by simp))
    omega  -- heq contradicts hif
  have hmem : inst.choose_next state ∈ Finset.univ \ state.visited := by
    simp only [choose_next, dif_pos hunvisited]
    exact (Finset.exists_min_image _ state.distances hunvisited).choose_spec.1
  exact (Finset.mem_sdiff.mp hmem).2

-- choose next gives min over unvisited
noncomputable def relax (inst : WeightedGraph V) (state : DijkstraState V) (u : V) : V → ENNReal :=
  λ v => if v ∈ state.visited then state.distances v -- v visited
         else min (state.distances v) (state.distances u + inst.weight u v) -- relaex via u

-- Main algorithm
noncomputable def run_loop (inst : WeightedGraph V) (state : DijkstraState V) : DijkstraState V :=
-- if theres still unvisited
  if h : state.visited.card < Fintype.card V then -- says unused h
    let u := inst.choose_next state
    let next_state := {
      visited := state.visited ∪ {u},
      distances := inst.relax state u
    }
    run_loop inst next_state
  else state
termination_by Fintype.card V - state.visited.card
decreasing_by
  simp_wf -- unfold next_state
  rw [Finset.card_insert_of_notMem (h_unvisited h)] -- but i used h here?
  omega

-- need inital_state to be invariant, so update distances
def initial_state (inst : WeightedGraph V) : DijkstraState V :=
{
  visited := {inst.source},
  distances := (λ v => if v = inst.source then 0 else inst.weight inst.source v)
}

/-
# 3. The Logical Bridge (Correctness)
Formalizing the invariant and the lemmas for the final theorem.
-/

/-
  Invariant Property of DijkstraState:
  1 Visited nodes have the true shortest path.
  2 Unvisited nodes have the restricted shortest path.
-/

-- True shortest path distance.
noncomputable def shortest_path_dist (inst : WeightedGraph V) (v : V) : ENNReal :=
  ⨅ (w : inst.G.Walk inst.source v), inst.walk_weight w -- something went wrong when i use Min?

-- Restricted shortest path distance.

def is_invariant (inst : WeightedGraph V) (state : DijkstraState V) : Prop :=
  (∀ v ∈ state.visited, state.distances v = inst.shortest_path_dist v) ∧
  (∀ v ∉ state.visited, state.distances v =
        ⨅ (u ∈ state.visited), state.distances u + inst.weight u v)
/-
   ⨅ (w : inst.G.Walk inst.source v)
      (h_int : ∀ x ∈ w.toVertices.init, x ∈ state.visited), inst.walk_weight w)
-/

-- Lemma 1: Initial state is valid.
lemma init_invariant (inst : WeightedGraph V) :
  is_invariant inst (inst.initial_state) := by
  constructor
  · -- Part 1: Visited nodes (just the source)
    intro v hv
    simp [initial_state] at hv
    subst hv
    simp [initial_state, shortest_path_dist]
    -- The shortest path from source to source is the nil walk (weight 0)
    apply le_antisymm
    · exact bot_le
    · refine iInf_le_of_le .nil (by simp [walk_weight])

  · -- Part 2: Unvisited nodes
    intro v hv
    -- 1. Unfold the definitions so Lean sees the specific values
    sorry

-- Lemma 2: Greedy choice picks the correct distance (Contradiction proof).
lemma greedy_choice_correct
    (inst : WeightedGraph V) (state : DijkstraState V) (u : V) :
    is_invariant inst state →
    u = inst.choose_next state →
    u ∉ state.visited →
    state.distances u = inst.shortest_path_dist u :=
by
  intro h_inv hu h_unvisited
  rcases h_inv with ⟨h_vis, h_unvis⟩

  -- Step 1: Use the invariant clause for this unvisited u:
  have h_inv_u : state.distances u =
      ⨅ (x : V) (hx : x ∈ state.visited),
        state.distances x + inst.weight x u := by
    have := h_unvis u h_unvisited
    simpa using this

  -- this is where you do the “first unvisited vertex on w” argument
  -- Step 2: Show `state.distances u ≤ inst.shortest_path_dist u`
  -- Usually follows from "relaxation cannot undershoot true distance".
  -- This will need a lemma: for any visited x and any edge x→u,
  --   state.distances x = true_dist x
  --   so state.distances x + w(x,u) ≥ true_dist u
  -- hence the inf ≥ true_dist u.
  have h_le : inst.shortest_path_dist u ≤ state.distances u := by
    -- you'll prove "shortest_path_dist u" is a lower bound of that infimum
    sorry

  -- Step 3: Show `state.distances u ≤ inst.shortest_path_dist u`.
  -- This is where the "greedy choice" and minimality of u are used.
  have h_ge : state.distances u ≤ inst.shortest_path_dist u := by
    unfold shortest_path_dist
    refine le_iInf ?_ -- prove for any path w, it holds
    intro w
    -- we can find the first vertex out of visited set
    have first_unvisited : ∃ (y : V), y ∉ state.visited ∧ y ∈ w.support ∧
    (∀ z ∈ w.support, w.support.idxOf z < w.support.idxOf y →
      z ∈ state.visited) := by  sorry
    -- condition on if this vertex = u
    obtain ⟨y, hy_unvis, hy_supp, hbefore⟩ := first_unvisited
    by_cases hyu : y = u
    ·
      subst hyu
      rw[h_inv_u]
      sorry
    · sorry
  exact le_antisymm h_ge h_le
-- Lemma 3: Relaxation step maintains the restricted infimum for the frontier.
lemma relax_preserves_invariant (inst : WeightedGraph V) (state : DijkstraState V) (u : V) :
  is_invariant inst state →
  u = inst.choose_next state →
  is_invariant inst ({ visited := state.visited ∪ {u}, distances := inst.relax state u }) :=
  by sorry

-- Lemma 4: Loop termination property.
lemma run_loop_visits_all (inst : WeightedGraph V) (state : DijkstraState V) :
  (inst.run_loop state).visited = Finset.univ := by
  sorry

-- main skeleton proof
lemma run_loop_preserves_invariant (inst : WeightedGraph V) (state : DijkstraState V) :
    is_invariant inst state → is_invariant inst (inst.run_loop state) := by
  -- Induct on unvisited nodes, the stop measure
  induction hn :(Fintype.card V - state.visited.card)
    generalizing state with

    -- 0 unvisited means visited = univ, loop returns state unchanged
  | zero =>
    intro h_inv
    unfold run_loop
    have helse : ¬ state.visited.card < Fintype.card V := by
      rw [Nat.sub_eq_zero_iff_le] at hn
      exact Nat.not_lt_of_le hn
    split_ifs
    exact h_inv

    -- n -> n+1, means we drop a node
  | succ n ih =>
    intro h_inv
    unfold run_loop
    have hif : state.visited.card < Fintype.card V := by
      have := state.visited.card_le_univ
      omega
    split_ifs
    let u := inst.choose_next state;
    let next_state : DijkstraState V := {
        visited := state.visited ∪ {u},
        distances := inst.relax state u
    }
    have hu : u = inst.choose_next state := rfl

    -- key bridge here, using lemma3 we proved
    have h_next_inv : is_invariant inst next_state :=
      relax_preserves_invariant inst state u h_inv hu

    have h_measure : Fintype.card V - next_state.visited.card = n := by
      have h_u : u ∉ state.visited := h_unvisited hif
      -- calculate new cardinality
      have h_card : next_state.visited.card = state.visited.card + 1 := by
        simp [next_state]
        rw [Finset.card_insert_of_notMem h_u]
      rw [h_card]
      omega

    exact ih next_state h_measure h_next_inv



/-
# 4. Final Theorem
-/
theorem dijkstra_correct (inst : WeightedGraph V) :
    let final_state := inst.run_loop inst.initial_state
    ∀ v : V, final_state.distances v = inst.shortest_path_dist v := by
  intro final_state v
  -- initial state satisfies invariant (Lemma 1)
  have h_init : is_invariant inst inst.initial_state :=
    init_invariant inst

  have h_inv : is_invariant inst final_state :=
    run_loop_preserves_invariant inst inst.initial_state h_init
  -- every vertex was visited by the end (Lemma 4)
  have h_all : v ∈ final_state.visited := by
    rw [run_loop_visits_all inst inst.initial_state]
    exact Finset.mem_univ v
  exact h_inv.1 v h_all

end WeightedGraph
