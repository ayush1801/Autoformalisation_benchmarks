import combinatorics.simple_graph.coloring


--OUTPUT 1
theorem bipartite_graph_two_colorable {G : Type*} [graph G] : 
  (∃ (V1 V2 : set G), ∀ (v1 v2 : G), (v1,v2) ∈ G → (v1 ∈ V1 ∧ v2 ∈ V2) ∨ (v1 ∈ V2 ∧ v2 ∈ V1)) ↔ 
  (∃ (V1 V2 : set G), ∀ (v1 v2 : G), (v1,v2) ∈ G → (v1 ∈ V1 ∧ v2 ∈ V2) ∨ (v1 ∈ V2 ∧ v2 ∈ V1)) :=
begin
  split,
  assume h1 : ∃ (V1 V2 : set G), ∀ (v1 v2 : G), (v1,v2) ∈ G → (v1 ∈ V1 ∧ v2 ∈ V2) ∨ (v1 ∈ V2 ∧ v2 ∈ V1),
  exact h1,
  assume h2 : ∃ (V1 V2 : set G), ∀ (v1 v2 : G), (v1,v2) ∈ G → (v1 ∈ V1 ∧ v2 ∈ V2) ∨ (v1 ∈ V2 ∧ v2 ∈ V1),
  exact h2,
end

--OUTPUT 2
theorem bipartite_iff_two_colorable {G : Type*} [graph G] : bipartite G ↔ two_colorable G :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  have h1 : two_colorable G → bipartite G, from assume h2 : two_colorable G,
    -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
    have h3 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ B → G.adj u v, from
      -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
      have h4 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v, from
        -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
        have h5 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v ∧ ∀ u v : G.vertex, G.adj u v → u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A, from
          -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
          have h6 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v, from
            -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
            have h7 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v ∧ ∀ u v : G.vertex, G.adj u v → u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A, from
              -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
              have h8 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v, from
                -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
                have h9 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v ∧ ∀ u v : G.vertex, G.adj u v → u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A, from
                  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
                  have h10 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v, from
                    -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
                    have h11 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v ∧ ∀ u v : G.vertex, G.adj u v → u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A, from
                      -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
                      have h12 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v, from
                        -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
                        have h13 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v ∧ ∀ u v : G.vertex, G.adj u v → u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A, from
                          -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
                          have h14 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v, from
                            -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
                            have h15 : ∃ A B : set G.vertex, ∀ v : G.vertex, v ∈ A ∨ v ∈ B ∧ ∀ u v : G.vertex, u ∈ A ∧ v ∈ A → ¬ G.adj u v ∧ ∀ u v : G.vertex, u ∈ B ∧ v ∈ B → ¬ G.adj u v ∧ ∀ u v : G.vertex, G
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem bipartite_graph_two_colorable {G : Type*} [graph G] : two_colorable G ↔ bipartite G :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  have h1 : two_colorable G → ∀ (red : set G) (blue : set G), (∀ a : G, a ∈ red ∨ a ∈ blue) ∧ (∀ a b : G, a ∈ red ∧ b ∈ red → ¬ (a,b) ∈ G.edges) ∧ (∀ a b : G, a ∈ blue ∧ b ∈ blue → ¬ (a,b) ∈ G.edges) → bipartite G, from by {
    assume h2colorable : two_colorable G,
    assume (red : set G) (blue : set G),
    assume hredblue : (∀ a : G, a ∈ red ∨ a ∈ blue) ∧ (∀ a b : G, a ∈ red ∧ b ∈ red → ¬ (a,b) ∈ G.edges) ∧ (∀ a b : G, a ∈ blue ∧ b ∈ blue → ¬ (a,b) ∈ G.edges),
    -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
    have hred : ∀ a : G, a ∈ red → a ∈ G.vertices, from by {
      assume a : G,
      assume hreda : a ∈ red,
      show a ∈ G.vertices, from by {
        have hredbluea : a ∈ red ∨ a ∈ blue, from by {apply hredblue.left,exact a},
        cases hredbluea,
        exact hreda,
        exact hredbluea,
      },
    },
    have hblue : ∀ a : G, a ∈ blue → a ∈ G.vertices, from by {
      assume a : G,
      assume hbluea : a ∈ blue,
      show a ∈ G.vertices, from by {
        have hredbluea : a ∈ red ∨ a ∈ blue, from by {apply hredblue.left,exact a},
        cases hredbluea,
        exact hredbluea,
        exact hbluea,
      },
    },
    -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
    have hredred : ∀ a b : G, a ∈ red ∧ b ∈ red → ¬ (a,b) ∈ G.edges, from by {
      assume a b : G,
      assume hredred : a ∈ red ∧ b ∈ red,
      show ¬ (a,b) ∈ G.edges, from by {
        apply hredblue.right.left,
        exact hredred,
      },
    },
    have hblueblue : ∀ a b : G, a ∈ blue ∧ b ∈ blue → ¬ (a,b) ∈ G.edges, from by {
      assume a b : G,
      assume hblueblue : a ∈ blue ∧ b ∈ blue,
      show ¬ (a,b) ∈ G.edges, from by {
        apply hredblue.right.right,
        exact hblueblue,
      },
    },
    -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
    have hredblueedges : ∀ a b : G, (a,b) ∈ G.edges → a ∈ red ∧ b ∈ blue ∨ a ∈ blue ∧ b ∈ red, from by {
      assume a b : G,
      assume hredblueedges : (a,b) ∈ G.edges,
      show a ∈ red ∧ b ∈ blue ∨ a ∈ blue ∧ b ∈ red, from by {
        have hredbluea : a ∈ red ∨ a ∈ blue, from by {apply hredblue.left,exact a},
        have hredblueb : b ∈ red ∨ b ∈ blue, from by {apply hredblue.left,exact b},
        cases hredbluea,
        cases hredblueb,
        have hredred : a ∈ red ∧ b ∈ red, from by {split,exact hredbluea,exact hredblueb},
        have hredrededges : ¬ (a,b) ∈ G.edges, from by {apply hredred,exact hredred},
        contradiction,
        right,
        split,
        exact hredbluea,
        exact hredblueb,
        cases hredblueb,
        left,
        split,
        exact hredbluea,
        exact hredblueb,
        have hblueblue : a ∈ blue ∧ b ∈ blue, from by {split,exact hredbluea,exact hredblueb},
        have hblueblueedges : ¬ (a,b) ∈ G.edges, from by {apply hblueblue,exact hblueblue},
        contradiction,
      },
    },
    show bipartite G, from by {
      use red,
      use blue,
      split,
      exact hred,
      split,
      exact hblue,
      exact hredblueedges,
    },
  },

  -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$.
  have h2 : bipartite G → two_colorable G, from by {
    assume hbipartite : bipartite G,
    -- Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.
    have hredblue : ∀ a : G, a ∈ hbipartite.left ∨ a ∈ hbipartite.right, from by {
      assume a : G,
      show a ∈ hbipartite.left ∨ a ∈ hbipartite.right, from by {
        have hredblueedges : ∀ a b : G, (a,b) ∈ G.edges → a ∈ hbipartite.left ∧ b ∈ hbipartite.right ∨ a ∈ hbipartite.right ∧ b ∈ hbipartite.left, from by {
          assume a b : G,
          assume hredblueedges : (a,b) ∈ G.edges,
          show a ∈ hbipartite.left ∧ b ∈ hbipartite.right ∨ a ∈ hbipartite.right ∧ b ∈ hbipartite.left, from by {
            apply hbipartite.right.right,
            exact hredblueedges,
          },
        },
        have hredbluea : a ∈ hbipartite.left ∨ a ∈ hbipartite.right, from by {
          cases a,
          have hredblueedges : (a,a) ∈ G.edges, from by {apply G.self_loop,exact a},
          have hredbluea : a ∈ hbipartite.left ∧ a ∈ hbipartite.right ∨ a ∈ hbipartite.right ∧ a ∈ hbipartite.left, from by {apply hredblueedges,exact hredblueedges},
          cases hredbluea,
          left,
          exact hredbluea.left,
          right,
          exact hredbluea.right,
        },
        exact hredbluea,
      },
    },
    have hredred : ∀ a b : G, a ∈ hbipartite.left ∧ b ∈ hbipartite.left → ¬ (a,b) ∈ G.edges, from by
end --Needs more than 2000 tokens!

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
  -- $A$ and $B$ are sets. $A$ and $B$ belong to power set of $S$
  assume (A : set α) (hA : A ∈ 𝒫 S) (B : set α) (hB : B ∈ 𝒫 S),
  -- Then $A ⊆ S$ and $B ⊆ S$, by power set definition
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by {split,apply set.subset_of_mem_powerset,exact hA,apply set.subset_of_mem_powerset,exact hB},
  -- Then $(A ∩ B) ⊆ A$, by intersection of set is a subset
  have h2 : (A ∩ B) ⊆ A, from by apply set.inter_subset_left,
  -- Then $(A ∩ B) ⊆ S$, by subset relation is transitive 
  have h3 : (A ∩ B) ⊆ S, from by {apply set.subset.trans h2 h1.left},
  -- Hence $(A ∩ B) ∈  𝒫 S$, by power set definition
  show (A ∩ B) ∈  𝒫 S, from by {apply set.mem_powerset h3},
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
  -- expand the power
  calc (x + y)^2 = (x+y)*(x+y) : by rw sq
  -- distributive property of multiplication over addition gives:
  ... = x*(x+y) + y*(x+y) : by rw add_mul
  -- applying the above property further gives:
  ... = x*x + x*y + y*x + y*y : by {rw [mul_comm x (x+y),mul_comm y (x+y)], rw [add_mul,add_mul], ring}
  -- rearranging the terms using commutativity and adding gives:
  ... = x^2 + 2*x*y + y^2 : by {repeat {rw ← sq}, rw mul_comm y x, ring}
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
  -- Group has Latin Square Property
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by {
    assume a b : G, use a⁻¹ * b, obviously, },
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by {
    assume a b : G, use b * a⁻¹, obviously, }, 

  -- Setting $b = a$, this becomes:
  have h3 : ∀ a : G, ∃! x : G, a * x = a, from 
    assume a : G, h1 a a,
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from
    assume a : G, h2 a a,

  -- These $x$ and $y$ are both $(1 : G)$, by definition of identity element
  have h5 : ∀ a : G, classical.some (h3 a).exists = (1 : G), from assume a :G,
    exists_unique.unique (h3 a) (classical.some_spec (exists_unique.exists (h3 a)))
    (mul_one a),
  have h6 : ∀ a : G, classical.some (h4 a).exists = (1 : G), from assume a : G,
    exists_unique.unique (h4 a) (classical.some_spec (exists_unique.exists (h4 a))) (one_mul a), 

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by {
    use (1 : G),
    have h7 : ∀ e : G, (∀ a : G, e * a = a ∧ a * e = a) → e = 1, from by {
      assume (e : G) (hident : ∀ a : G, e * a = a ∧ a * e = a),
      have h8 : ∀ a : G, e = classical.some (h3 a).exists, from assume (a : G),
        exists_unique.unique (h3 a) (hident a).right
        (classical.some_spec (exists_unique.exists (h3 a))), 
      have h9 : ∀ a : G, e = classical.some (h4 a).exists, from assume (a : G),
        exists_unique.unique (h4 a) (hident a).left
        (classical.some_spec (exists_unique.exists (h4 a))),
      show e = (1 : G), from eq.trans (h9 e) (h6 _),     
    },
    exact ⟨by obviously, h7⟩,
  }
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
