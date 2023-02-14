import combinatorics.simple_graph.coloring


--OUTPUT 1
theorem bipartite_graph_two_colorable {G : Type*} [graph G] : 
  (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)) ↔ 
  (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)) :=
begin
  show (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)) ↔ 
  (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)), from iff.intro,
  {
    assume h1 : (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)),
    have h2 : ∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges, from by auto [h1],
    show (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)), from by auto [h1, h2],
  },
  {
    assume h1 : (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)),
    have h2 : ∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges, from by auto [h1],
    show (∃ (V1 V2 : set G), (∀ (v1 v2 : G), v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ G.edges)), from by auto [h1, h2],
  }
end

--OUTPUT 2
theorem bipartite_graph_two_colorable (G : Type*) [graph G] : is_bipartite G ↔ is_two_colorable G :=
begin
  split,
  {
    assume h1 : is_bipartite G,
    have h2 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2, from h1,
    have h3 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E), from h2,
    have h4 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E), from h3,
    have h5 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2)), from h4,
    have h6 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2)) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2), from h5,
    have h7 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2)) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v1, v2) ∉ E), from h6,
    have h8 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2)) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v2, v1) ∉ E), from h7,
    have h9 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2)) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → ¬ (v1 = v2)), from h8,
    have h10 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2)) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → ¬ (v1 = v2)) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2) → v1 ≠ v2), from h9,
    have h11 : ∃ V1 V2 : set G, is_partition V1 V2 ∧ is_independent_set V1 ∧ is_independent_set V2 ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → (v2, v1) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → ¬ (v1 = v2)) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 → v1 ≠ v2 → (v1, v2) ∉ E) ∧ (∀ v1 v2 : G, v1 ∈ V1 ∧ v2 ∈ V2 →
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem bipartite_iff_two_colorable (G : Type*) [graph G] : bipartite G ↔ two_colorable G :=
begin
  split,
  {
    assume h1,
    show two_colorable G, from by auto [h1]
  },
  {
    assume h2,
    show bipartite G, from by auto [h2]
  }
end

--OUTPUT 4
theorem two_colorable_iff_bipartite (G : Type*) [graph G] : (∃ (coloring : G → color), ∀ (x y : G), x ≠ y → coloring x ≠ coloring y) ↔ bipartite G :=
begin
  have h1 : (∃ (coloring : G → color), ∀ (x y : G), x ≠ y → coloring x ≠ coloring y) → bipartite G, from by auto using [bipartite],
  have h2 : bipartite G → (∃ (coloring : G → color), ∀ (x y : G), x ≠ y → coloring x ≠ coloring y), from by auto using [two_colorable],
  show (∃ (coloring : G → color), ∀ (x y : G), x ≠ y → coloring x ≠ coloring y) ↔ bipartite G, from by auto [h1, h2],
end

--OUTPUT 5
theorem bipartite_iff_two_colorable (G : Type*) [graph G] : bipartite G ↔ two_colorable G :=
begin
  have h1 : bipartite G → two_colorable G, from by auto,
  have h2 : two_colorable G → bipartite G, from by auto,
  show bipartite G ↔ two_colorable G, from by auto [h1, h2],
end

--OUTPUT 6
theorem bipartite_graph_two_colorable {G : Type*} [graph G] : G.is_two_colorable ↔ G.is_bipartite :=
begin
  split,
  {
    assume h1 : G.is_two_colorable,
    let A : set G := {x : G | x.is_red},
    let B : set G := {x : G | x.is_blue},
    let h2 : G.is_bipartite, from by auto [h1],
    show G.is_bipartite, from h2,
  },
  {
    assume h1 : G.is_bipartite,
    let A : set G := {x : G | x.is_red},
    let B : set G := {x : G | x.is_blue},
    let h2 : G.is_two_colorable, from by auto [h1],
    show G.is_two_colorable, from h2,
  }
end

/- FEW SHOT PROMPTS TO CODEX(START)
/--`theorem`
Power Set is Closed under Intersection
Let $S$ be a set.

Let $\powerset S$ be the power set of $S$.


Then:
:$\forall A, B \in \powerset S: A \cap B \in \powerset S$
`proof`
Let $A, B \in \powerset S$.

Then by the definition of power set, $A \subseteq S$ and $B \subseteq S$.

From Intersection is Subset we have that $A \cap B \subseteq A$.

It follows from Subset Relation is Transitive that $A \cap B \subseteq S$.

Thus $A \cap B \in \powerset S$ and closure is proved.
{{qed}}
-/
theorem power_set_intersection_closed {α : Type*} (S : set α) : ∀ A B ∈ 𝒫 S, (A ∩ B) ∈ 𝒫 S :=
begin
  assume (A : set α) (hA : A ∈ 𝒫 S) (B : set α) (hB : B ∈ 𝒫 S),
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by auto [set.subset_of_mem_powerset, set.subset_of_mem_powerset],
  have h2 : (A ∩ B) ⊆ A, from by auto [set.inter_subset_left],
  have h3 : (A ∩ B) ⊆ S, from by auto [set.subset.trans],
  show (A ∩ B) ∈  𝒫 S, from by auto [set.mem_powerset],
end

/--`theorem`
Square of Sum
 :$\forall x, y \in \R: \paren {x + y}^2 = x^2 + 2 x y + y^2$
`proof`
Follows from the distribution of multiplication over addition:

{{begin-eqn}}
{{eqn | l = \left({x + y}\right)^2
      | r = \left({x + y}\right) \cdot \left({x + y}\right)
}}
{{eqn | r = x \cdot \left({x + y}\right) + y \cdot \left({x + y}\right)
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = x \cdot x + x \cdot y + y \cdot x + y \cdot y
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = x^2 + 2xy + y^2
      | c = 
}}
{{end-eqn}}
{{qed}}
-/
theorem square_of_sum (x y : ℝ) : (x + y)^2 = (x^2 + 2*x*y + y^2) := 
begin
  calc (x + y)^2 = (x+y)*(x+y) : by auto [sq]
  ... = x*(x+y) + y*(x+y) : by auto [add_mul]
  ... = x*x + x*y + y*x + y*y : by auto [mul_comm, add_mul] using [ring]
  ... = x^2 + 2*x*y + y^2 : by auto [sq, mul_comm] using [ring]
end

/--`theorem`
Identity of Group is Unique
Let $\struct {G, \circ}$ be a group. Then there is a unique identity element $e \in G$.
`proof`
From Group has Latin Square Property, there exists a unique $x \in G$ such that:
:$a x = b$

and there exists a unique $y \in G$ such that:
:$y a = b$

Setting $b = a$, this becomes:

There exists a unique $x \in G$ such that:
:$a x = a$

and there exists a unique $y \in G$ such that:
:$y a = a$

These $x$ and $y$ are both $e$, by definition of identity element.
{{qed}}
-/
theorem group_identity_unique {G : Type*} [group G] : ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a :=
begin
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by auto using [use (a⁻¹ * b)],
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by auto using [use b * a⁻¹], 

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from by auto [h1],
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from by auto [h2],

  have h5 : ∀ a : G, classical.some (h3 a).exists = (1 : G), from by auto [exists_unique.unique, h3, classical.some_spec, exists_unique.exists, mul_one],
  have h6 : ∀ a : G, classical.some (h4 a).exists = (1 : G), from by auto [exists_unique.unique, h4, classical.some_spec, exists_unique.exists, one_mul],

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by auto [h3, h4, exists_unique.unique, classical.some_spec, exists_unique.exists] using [use (1 : G)],
end

/--`theorem`
Bipartite Graph is two colorable
Let $G$ be a graph. Then $G$ is 2-colorable if and only if $G$ is bipartite.
`proof`
Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color. Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue. Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$. This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.

Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$. Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.

QED

-/
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
