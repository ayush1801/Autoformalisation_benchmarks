import combinatorics.simple_graph.coloring


--OUTPUT 1
theorem two_colorable_bipartite {G : Type*} [graph G] : 2-colorable G ↔ bipartite G :=
begin
  have h0 : 2-colorable G → ∃ (V1 V2 : set G),
      valid_coloring V1 red ∧ valid_coloring V2 blue ∧
      ∀ (x y : G), x ≠ y → connected x y → ((x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1)),
    assume hcolor,
    by {cases hcolor.2.2 with V1 hV1, cases hcolor.2.1 with V2 hV2, use [V1,V2], split,
      exact hV1, split, exact hV2, assume x y hxy hconn,
      cases hcolor.1 hxy with hcxy hcyx, cases hcxy with hcx hcx',
      cases hcx.1, cases hcyx.1,
      have hconn2 : connected y x, from @connected_comm G (x y) _ _ hconn,
      have hconnxy : connected x y, from @connected_symm G (x y) _ _ hconn,
      have hconnyx : connected y x, from @connected_symm G (y x) _ _ hconn2,
      cases hcyx.2 with hry hrx, rw hry at hcx,
      have hx : x ∈ V2, from @color_member G (x) _ (blue) (hcx) (hconnxy),
      cases hcx'.1, cases hcxy.1,
      cases hcxy.2 with hrx hrx', rw hrx' at hcyx,
      have hy : y ∈ V2, from @color_member G (y) _ (blue) (hcyx) (hconnyx),
      show (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1), from or.inr ⟨hx,hy⟩,
      cases hcx'.2 with hry hrx',
      have hx : x ∈ V2, from @color_member G (x) _ (blue) (hcx') (hconnxy),
      cases hcyx.2 with hry hrx, rw hrx at hcx,
      have hy : y ∈ V1, from @color_member G (y) _ (red) (hcx) (hconnyx),
      show (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1), from or.inr ⟨hx,hy⟩,
      cases hcx.2 with hry hrx, rw hry at hcx',
      have hx : x ∈ V1, from @color_member G (x) _ (red) (hcx') (hconnxy),
      cases hcyx.2 with hry hrx', rw hrx' at hcx',
      have hy : y ∈ V1, from @color_member G (y) _ (red) (hcyx) (hconnyx),
      show (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1), from or.inl ⟨hx,hy⟩,
      cases hcx'.2 with hry hrx',
      have hx : x ∈ V1, from @color_member G (x) _ (red) (hcx') (hconnxy),
      cases hcyx.2 with hry hrx', rw hry at hcx,
      have hy : y ∈ V1, from @color_member G (y) _ (red) (hcyx) (hconnyx),
      show (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1), from or.inl ⟨hx,hy⟩,},

  have h1 : bipartite G → 2-colorable G,
    assume hbipart,
    by {cases h0 hbipart with V1 hV1, cases hV1 with V2 hV2,
      cases hV2 with hV1red hV2, cases hV2 with hV2blue hV2,
      use (V1, V2), split, from hV1blue,
      split, from hV1red,
      from hV2},

  split, from h1, from h0
end

--OUTPUT 2
theorem two_colorable_iff_bipartite {G : Type*} [graph G] : (∃ (A B : set G), is_valid_coloring A B) ↔ is_bipartite G :=
begin
    split,
    { assume h, by {
        cases h with A h,
        cases h with B h,
        have h1: is_valid_coloring A B, from h,
        have h2: ∀ v e, v ∈ A ∧ v = head e → tail e ∉ A,
          assume v e hv, assume h,
          apply h1 v e hv (and.intro h (and.intro rfl rfl)),
        have h3: ∀ v e, v ∈ B ∧ v = tail e → head e ∉ B,
          assume v e hv, assume h,
          apply h1 v e (and.intro h (and.intro rfl rfl)) hv,
        have h4: ∀ v e, v ∈ A ∧ v = tail e → head e ∉ A,
          assume v e hv, assume h,
          have h5: head e = tail e, from calc
            head e = v : and.left hv
            ... = tail e : (and.right hv).left
            ... = head e : (and.right hv).right,
          have h6: v = head e, from calc
            v = head e : h5
            ... = v : and.left hv,
          have h7: v ∈ B, from h3 v e (and.intro h6 (and.intro rfl rfl)) h,
          have h8: head e ∈ A, from h2 v e (and.intro h6 (and.intro rfl rfl)) h7,
          show false, from absurd h (and.intro h8 (and.intro rfl rfl)),
        have h5: ∀ v e, v ∈ B ∧ v = head e → tail e ∉ B,
          assume v e hv, assume h,
          have h6: head e = tail e, from calc
            head e = v : and.left hv
            ... = tail e : (and.right hv).left
            ... = head e : (and.right hv).right,
          have h7: v = tail e, from calc
            v = tail e : h6
            ... = v : and.left hv,
          have h8: v ∈ A, from h2 v e (and.intro h7 (and.intro rfl rfl)) h,
          have h9: tail e ∈ B, from h3 v e (and.intro h7 (and.intro rfl rfl)) h8,
          show false, from absurd h (and.intro h9 (and.intro rfl rfl)),
        have h6: ∀ v e, v ∈ A ∧ v = head e → tail e ∈ B,
          assume v e hv, assume h,
          have h7: head e ∉ B, from h5 v e hv h,
          have h8: tail e ∈ A, from h2 v e hv h,
          have h9: tail e ∉ A, from h4 v e (and.intro h8 (and.intro rfl rfl)) h,
          show tail e ∈ B, from or.cases_on (set.mem_or_mem_of_ne h9 h7)
            (λ h10, absurd h10 h7) (λ h11, h11),
        have h7: ∀ v e, v ∈ B ∧ v = tail e → head e ∈ A,
          assume v e hv, assume h,
          have h8: tail e ∉ A, from h4 v e hv h,
          have h9: head e ∈ B, from h3 v e hv h,
          have h10: head e ∉ B, from h5 v e (and.intro h9 (and.intro rfl rfl)) h,
          show head e ∈ A, from or.cases_on (set.mem_or_mem_of_ne h10 h8)
            (λ h11, absurd h11 h8) (λ h12, h12),
        show is_bipartite G, from is_bipartite.mk A B h6 h7,
        },
    { assume h, by {
        cases h with A B h,
        cases h with h3 h4,
        use A,
        use B,
        assume v e hv,
        assume h,
        have h5: v ∈ A ∨ v ∈ B, from set.mem_or_mem_of_ne hv.right,
        have h6: v ∈ A ∧ v = head e, from or.cases_on h5
          (λ h5a, and.intro h5a
            (calc
              v = head e : hv.left
              ... = v : h5a
            )
          )
          (λ h5b, and.intro h5b
            (calc
              head e = v : hv.left
              ... = tail e : (and.right hv).left
              ... = head e : (and.right hv).right
            )
          ),
        have h7: v ∈ B ∧ v = tail e, from or.cases_on h5
          (λ h5a, and.intro h5a
            (calc
              head e = v : hv.left
              ... = tail e : (and.right hv).left
              ... = head e : (and.right hv).right
            )
          )
          (λ h5b, and.intro h5b
            (calc
              v = tail e : hv.left
              ... = v : h5b
            )
          ),
        or.cases_on (set.mem_or_mem_of_ne h)
          (λ h8, absurd (h4 v e h7 h8) h8)
          (λ h9, absurd (h3 v e h6 h9) h9),
        },
    },
end

--OUTPUT 3
theorem is_bipartite_iff {α : Type*} (G : graph α) : is_bipartite G ↔ is_two_colorable G :=
begin
  split,
  { --Suppose $G$ is bipartite.
    assume hbip : is_bipartite G,
    use (λ x, by {
      apply by_cases,
      { --Suppose $x \in V_{1}$.
        assume hV1 : x ∈ G.V_1,
        exact (1 : ℕ), },
      { --Suppose $x \in V_{2}$.
        assume hV2 : x ∉ G.V_1,
        have hV2' : x ∈ G.V_2, from @is_bipartite.in_V_2 _ G hbip hV2,
        exact (2 : ℕ), },
    }),   
    assume a b,
    apply by_cases,
    {
      assume haV1 : a ∈ G.V_1,
      apply by_cases,
      {
        assume hbV1 : b ∈ G.V_1,
        have h : _ := @is_bipartite.V_1_V_2_disjoint _ G hbip haV1 hbV1,
        rw h, },
      {
        assume hbV2 : b ∉ G.V_1,
        have hbV2' : _ := @is_bipartite.in_V_2 _ G hbip hbV2,
        have h : _ := @is_bipartite.no_edge_V_1_V_2 _ G hbip haV1 hbV2',
        rw h,
        show (1 : ℕ) ≠ (2 : ℕ), from assume hne, by {
          rw hne at hbV2,
          contradiction, }, }, },
    {
      assume haV2 : a ∉ G.V_1,
      apply by_cases,
      {
        assume hbV1 : b ∈ G.V_1,
        have hbV1' : b ∈ G.V_2, from @is_bipartite.in_V_1 _ G hbip hbV1,
        have h : _ := @is_bipartite.no_edge_V_1_V_2 _ G hbip hbV1' haV2,
        rw h,
        show (2 : ℕ) ≠ (1 : ℕ), from assume hne, by {
          rw hne at haV2,
          contradiction, }, },
      {
        assume hbV2 : b ∈ G.V_2,
        have h : _ := @is_bipartite.V_1_V_2_disjoint _ G hbip hbV2 haV2,
        rw h, }, }, },
  { --Suppose that $G$ is two-colourable.
    assume hcol : is_two_colorable G,
    let V_1 := {a : α | hcol.coloring a = (1 : ℕ)},
    let V_2 := {a : α | hcol.coloring a = (2 : ℕ)},
    have hV_1_V_2_disjoint : ∀ a : α, a ∈ V_1 ∧ a ∈ V_2 → false, from 
      assume a : α, assume haV1V2 : a ∈ V_1 ∧ a ∈ V_2, by {
        have hV1 : hcol.coloring a = (1 : ℕ), from haV1V2.left,
        have hV2 : hcol.coloring a = (2 : ℕ), from haV1V2.right,
        have h : (1 : ℕ) = (2 : ℕ), from congr_arg hcol.coloring hV1,
        rw h at hV2,
        contradiction,
    },
    have hno_edge_V_1_V_2 : ∀ a b : α, edge_between G a b ∧ a ∈ V_1 ∧ b ∈ V_2 → false, from 
      assume a b : α, assume habV_1V_2 : edge_between G a b ∧ a ∈ V_1 ∧ b ∈ V_2, by {
        have hV1 : hcol.coloring a = (1 : ℕ), from habV_1V_2.right.left,
        have hV2 : hcol.coloring b = (2 : ℕ), from habV_1V_2.right.right,
        have he : hcol.coloring a ≠ hcol.coloring b, from habV_1V_2.left,
        have h : (1 : ℕ) ≠ (2 : ℕ), from congr_arg hcol.coloring he,
        rw hV1 at h,
        rw hV2 at h,
        contradiction,
    },
    show is_bipartite G, from ⟨V_1, V_2, hV_1_V_2_disjoint, hno_edge_V_1_V_2⟩,
  },
end

--OUTPUT 4
theorem by_perez_graph_bipartite_iff_twocolorable (G : Type*) [simple_graph G] :
  bipartite G ↔ twocolorable G :=
begin
  show bipartite G → twocolorable G, from by {
    assume h : bipartite G,
    
    have 
  },
  show twocolorable G → bipartite G, from by {obviously},
end

--OUTPUT 5
theorem two_colorable_bipartite {G : Type*} [graph G] : two_colorable G ↔ bipartite G :=
begin
  show two_colorable G ↔ bipartite G,
    split,
    intro hcolorable,
    unfold two_colorable at hcolorable,
    cases two_colorable.elim hcolorable with A hA,
    cases two_colorable.elim hcolorable with B hB,
    show bipartite G, from by
    refine ⟨A,B,λ (x : G) (y : G) (hconnected : connected G x y), _⟩,
    have h1 : ∃ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ B ∧ v1 ≠ v2 ∧ connected G v1 v2, from two_colorable.elim hcolorable,
    cases h1 with v1 h1,
    cases h1 with v2 h1,
    cases h1 with hv1 h1,
    cases h1 with hv2 h1,
    cases h1 with hdifferent hconnected,
    have hconnected' : connected G v1 v2 ∧ connected G v2 v1, from by {
      split,
      show connected G v1 v2, from by apply hconnected,
      show connected G v2 v1, from by {apply connected_symm,exact hconnected}
    },
    rw ← hA v1 at hv1,
    rw ← hB v2 at hv2,
    show h1.left, from by {
      cases hconnected' with hconnected1 hconnected2,
      have h2 : v1 = v2, from by 
      apply two_colorable.elim(hcolorable) v1 v2 h1.right.right h1.right.left hconnected1 hconnected2 hv1 hv2,
      rw (mt hdifferent h2),
      apply h1.right,
    },
    intro hbipartite,
    cases hbipartite with V1 hbipartite,
    cases hbipartite with V2 hbipartite,
    have hunion : disjoint V1 V2 ∧ V1 ∪ V2 = G, from by {
      split,
      from hbipartite.left,
      from hbipartite.right,
    },
    have h1 : (V1 ∪ V2) × G ⊆ V1 × V2 ∨ (V1 ∪ V2) × G ⊆ V2 × V1, from by 
    refine or.elim (hbipartite.right.elim _ _) _,
    cases h1,
      have h2 : (V1 ∪ V2) × G ⊆ V1 × V2, from by {
        apply h1,
      },
    have h3 : (V1 ∪ V2) × G ⊆ V2 × V1, from by {
      apply h1,
    },
    have color : (V1 ∪ V2) × G → 2, from 
    assume (x y : G), if h : (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1) then 0 else 1,
    have h4 : ∀ (x y z w : G), connected G x y → connected G z w → (color (x,z) = color (y,w)), from 
    assume (x y z w : G) (hconnected1 : connected G x y) (hconnected2 : connected G z w),
           if h : (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1) then 
              if h' : (z ∈ V1 ∧ w ∈ V2) ∨ (z ∈ V2 ∧ w ∈ V1) then 0 else 1
           else 1,
    have h5 : ∀ (x y : G), (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1) → connected G x y, from 
    assume (x y : G) (h1 : (x ∈ V1 ∧ y ∈ V2) ∨ (x ∈ V2 ∧ y ∈ V1)),
           if h : x ∈ V1 ∧ y ∈ V2 then hbipartite.right (x,y) 
           else if h' : x ∈ V2 ∧ y ∈ V1 then hbipartite.right (y,x)
           else false.elim (mt h1 ⟨h,h'⟩),
    show two_colorable G, from ⟨V1∪V2, color, h2, h3, h4, h5⟩,
end

--OUTPUT 6
theorem bipartite_2_colorable (G : Type*) [simple_graph G] : 
  is_bipartite G ↔ is_two_colorable G :=
begin
  simp [is_two_colorable],
  apply iff_of_eq,
  split;
  assume h1 h2;
  have h3 : ∃ (A : set G.V) (B : set G.V), h2 = ⟨A, B⟩, from by {exact h2.2},
  rcases h3 with ⟨A, B, h3⟩,
  rw h3,
  have h4 : ∀ (v : G.V), v ∈ A ∨ v ∈ B, from λ v, by {rw h3, exact h2.1.2 v},
  have h5 : ∀ (u : G.V) (v : G.V), G.E v u → (u ∈ A → v ∈ B) ∧ (u ∈ B → v ∈ A), from by {
    assume (u : G.V) (v : G.V) (h_edge : G.E v u);
    simp [h1.2] at h_edge,
    show (u ∈ A → v ∈ B) ∧ (u ∈ B → v ∈ A), from by {split,
      assume h_u_A : (u ∈ A), have h_v_B : v ∈ B, from by {
        rw h_edge,
        exact h2.1.1 v,
        exact h_u_A,
      }, exact h_v_B,
      assume h_u_B : u ∈ B, have h_v_A : v ∈ A, from by {
        rw h_edge,
        exact h2.1.1 v,
        exact h_u_B,
      }, exact h_v_A,
    },
  },
  have h6 : ∀ (v : G.V), v ∉ G.E.range, from λ (v : G.V),
    assume h_v_range : v ∈ G.E.range,
    by {have h_dom : v ∈ G.E.domain, from by {exact G.E.has_mem_range.1 h_v_range},
      rw h1.2 at h_dom,
      contradiction},
  have h7 : ∀ (v : G.V), ∀ (u : G.V), G.E v u → (v ∉ A ∧ u ∈ B) ∨ (v ∈ A ∧ u ∉ B), from by {
    assume (v : G.V) (u : G.V) (h_edge : G.E v u),
    assume h_v_A : (v ∈ A),
    assume h_u_A : (u ∈ A),
    have h_v_range : v ∈ G.E.range, from by {
      have h_dom : u ∈ G.E.domain, from by {exact G.E.has_mem_domain.2 h_edge},
      exact G.E.has_mem_range.2 ⟨h_dom, h_v_A⟩
    }, 
    have h_u_range : u ∈ G.E.range, from by {
      have h_dom : v ∈ G.E.domain, from by {exact G.E.has_mem_domain.2 h_edge},
      exact G.E.has_mem_range.2 ⟨h_dom, h_u_A⟩
    },
    show (v ∉ A ∧ u ∈ B) ∨ (v ∈ A ∧ u ∉ B), from ii.elim h_u_A (by {
      assume h_u_A : (u ∉ A),
      show (v ∉ A ∧ u ∈ B) ∨ (v ∈ A ∧ u ∉ B), from or.inl ⟨h_v_range, h_u_A⟩
    }) (by {
      assume h_u_A : (u ∈ A),
      show (v ∉ A ∧ u ∈ B) ∨ (v ∈ A ∧ u ∉ B), from or.inr ⟨h_v_A, h_u_range⟩
    }),
  },

  have h8 : ∀ (v : G.V), v ∉ G.E.domain, from λ (v : G.V),
    assume h_v_domain : v ∈ G.E.domain,
    by {have h_range : v ∈ G.E.range, from by {exact G.E.has_mem_domain.1 h_v_domain},
      rw h1.2 at h_range,
      contradiction},

  have h9 : ∀ (u : G.V), ∀ (v : G.V), G.E u v → (u ∉ B ∧ v ∈ A) ∨ (u ∈ B ∧ v ∉ A), from by {
    assume (u : G.V) (v : G.V) (h_edge : G.E u v),
    have h_dom : u ∈ G.E.domain, from by {exact G.E.has_mem_domain.2 h_edge},
    have h_range : v ∈ G.E.range, from by {exact G.E.has_mem_range.2 ⟨h_dom, h2.1.1 v⟩},
    rw h1.2 at h_range,
    show (u ∉ B ∧ v ∈ A) ∨ (u ∈ B ∧ v ∉ A), from ii.elim h2.1.1 v (by {
      assume h_v_A : (v ∈ A),
      show (u ∉ B ∧ v ∈ A) ∨ (u ∈ B ∧ v ∉ A), from or.inr ⟨h_dom, h_v_A⟩
    }) (by {
      assume h_v_A : (v ∉ A),
      show (u ∉ B ∧ v ∈ A) ∨ (u ∈ B ∧ v ∉ A), from or.inl ⟨h_range, h_v_A⟩
    })
  },
  {split, 
    show ∀ (v : G.V), v ∈ A ∨ v ∈ B, from h4,
    show ∀ (u v : G.V), G.E u v → (u ∈ A → v ∈ B) ∧ (u ∈ B → v ∈ A), from h5,
  },
  {split,
    show ∀ (v : G.V), v ∈ A ∨ v ∈ B, from h4,
    show ∀ (u v : G.V), G.E u v → (u ∈ A → v ∈ B) ∧ (u ∈ B → v ∈ A), from h9,
  },
end

--OUTPUT 7
theorem two_colorable_iff_bipartite {α : Type*} [fintype α] (G : graph α) : two_colorable G ↔ bipartite G :=
begin
  split,
    assume (h1 : two_colorable G),
    use (color_set h1 0),
    use (color_set h1 1),
    show ∀ e : α × α, e ∈ G.E → e.fst ∈ (color_set h1 0) ∧ e.snd ∈ (color_set h1 1), from
    begin
      assume (e : α × α) (he : e ∈ G.E),
      have h2 : (e.fst ∈ (color_set h1 0)) ∨ (e.fst ∈ (color_set h1 1)), from (color_def h1 e.fst e.fst e.snd he).left,
      have h3 : (e.snd ∈ (color_set h1 0)) ∨ (e.snd ∈ (color_set h1 1)), from (color_def h1 e.snd e.fst e.snd he).right,
      have h4 : (e.fst ∈ (color_set h1 0)) ∧ (e.snd ∈ (color_set h1 1)) ∨ (e.fst ∈ (color_set h1 1)) ∧ (e.snd ∈ (color_set h1 0)), from or.imp_or_distrib h2 h3,
      cases h4,
        assume h5 : (e.fst ∈ (color_set h1 0)) ∧ (e.snd ∈ (color_set h1 1)),
        show (e.fst ∈ (color_set h1 0)) ∧ (e.snd ∈ (color_set h1 1)), from h5,
      assume h5 : (e.fst ∈ (color_set h1 1)) ∧ (e.snd ∈ (color_set h1 0)),
      have h6 : (e.fst ∈ (color_set h1 0)) ∧ (e.snd ∈ (color_set h1 1)), from and.intro h5.right h5.left,
      show (e.fst ∈ (color_set h1 0)) ∧ (e.snd ∈ (color_set h1 1)), from h6,
    end,

    assume hbip : bipartite G,
    show two_colorable G, from two_colorable.mk hbip,
end

--OUTPUT 8
theorem bipartite_graph_two_colorable {G : Type*} [graph G] : 
∀ (G : Type*) [graph G], (∀ A : set G, pairwise_disjoint A ∧ complete G A) → (∃! coloring : coloring G 2, ∀ u v ∈ G.E, coloring u ≠ coloring v) :=
begin
  assume (G : Type*) [graph G],
  assume hpartite : ∀ A : set G, pairwise_disjoint A ∧ complete G A,
  have h1 : ∃! A : set G, pairwise_disjoint A ∧ complete G A, from 
    exists_unique_partition G,
  have h2 : ∃! A : set G, set.finite A, from exists_unique_finite A,
  have h3 : ∃! A : set G, ∃! B : set G, set.finite A ∧ set.finite B ∧ A ∪ B = G.V, from 
    by {unfold exists_unique_finite,use A,use B,exact ⟨h2.1.1,h2.1.2,set.ext.2 (h2.1.3).symm⟩,use B,use A,exact ⟨h2.2.1,h2.2.2,set.ext.2 (h2.2.3).symm⟩},
  have h4 : ∃! A : set G, ∃! B : set G, set.finite A ∧ set.finite B ∧ A ∪ B = G.V ∧ pairwise_disjoint A ∧ pairwise_disjoint B ∧ complete G A ∧ complete G B, from
    by {use A,use B,unfold exists_unique_disjoint,unfold exists_unique_finite,use A,use B,exact ⟨h2.1.1,h2.1.2,set.ext.2 (h2.1.3).symm,⟨(hpartite A).1,(hpartite B).1⟩,⟨(hpartite A).2,(hpartite B).2⟩⟩,use B,use A,exact ⟨h2.2.1,h2.2.2,set.ext.2 (h2.2.3).symm,⟨(hpartite B).1,(hpartite A).1⟩,⟨(hpartite B).2,(hpartite A).2⟩⟩},
  have h5 : ∃! coloring : coloring G 2, ∀ u v ∈ G.E, coloring u ≠ coloring v, from
    by {
      have h6 : ∀ A B : set G, set.finite A ∧ set.finite B ∧ A ∪ B = G.V ∧ pairwise_disjoint A ∧ pairwise_disjoint B ∧ complete G A ∧ complete G B → ∃! coloring : coloring G 2, ∀ u v ∈ G.E, coloring u ≠ coloring v, from by {
        assume (A B : set G) (h : set.finite A ∧ set.finite B ∧ A ∪ B = G.V ∧ pairwise_disjoint A ∧ pairwise_disjoint B ∧ complete G A ∧ complete G B),
        set coloring := λ (v : G.V), if v ∈ A then 0 else 1,
        have h1 : ∀ u v : G.V, u ≠ v → coloring u ≠ coloring v, from by {
          assume (u v : G.V) (huv : u ≠ v),
          have h1 : u ∉ A ↔ v ∈ A, from set.finite.finite_inter_iff_ne_empty (A ∩ B) (h.1.1) (h.2.1) huv,
          have h2 : u ∉ B ↔ v ∈ B, from set.finite.finite_inter_iff_ne_empty (A ∩ B) (h.2.1) (h.1.1) huv,
          by_contradiction (assume h3 : coloring u = coloring v), rw h3 at h1, rw h3 at h2,
          show false, from if (u ∈ A) then h1.elim (h.4 huv.symm) else h2.elim (h.5 huv.symm),
        },
        have h2 : ∀ u v ∈ G.E, coloring u ≠ coloring v, from by {
          assume (u v : G.V) (huv : u ∈ G.E) (vuv : v ∈ G.E),
          by_contradiction (assume hne : coloring u = coloring v), rw hne at huv, rw hne at vuv,
          show false, from if (u ∈ A) then huv.elim (h.6 v vuv) else vuv.elim (h.7 u huv),
        },
        show ∃! coloring : coloring G 2, ∀ u v ∈ G.E, coloring u ≠ coloring v, from by {
          use coloring, unfold coloring.fst, unfold coloring.snd,
          have h1 : ∀ u v : G.V, u ∈ A → v ∈ A → u ≠ v → u = v, from by {
            assume (u v : G.V) (huv : u ∈ A) (hvu : v ∈ A) (h3 : u ≠ v), rw ←h3 at huv, exact huv,
          },
          have h2 : ∀ u v : G.V, u ∈ B → v ∈ B → u ≠ v → u = v, from by {
            assume (u v : G.V) (huv : u ∈ B) (hvu : v ∈ B) (h3 : u ≠ v), rw ←h3 at hvu, exact hvu,
          }, 
          have h3 : ∀ u v : G.V, u ≠ v → coloring u ≠ coloring v, from by {
            assume (u v : G.V) (huv : u ≠ v),
            have h1 : u ∉ A ↔ v ∈ A, from set.finite.finite_inter_iff_ne_empty (A ∩ B) (h.1.1) (h.2.1) huv,
            have h2 : u ∉ B ↔ v ∈ B, from set.finite.finite_inter_iff_ne_empty (A ∩ B) (h.2.1) (h.1.1) huv,
            by_contradiction (assume h3 : coloring u = coloring v), rw h3 at h1, rw h3 at h2,
            show false, from if (u ∈ A) then h1.elim (h.4 huv.symm) else h2.elim (h.5 huv.symm),
          },
          exact ⟨h1,h2,h3⟩
        },
      },
      have h7 : ∀ A B : set G, A ∪ B = G.V ∧ pairwise_disjoint A ∧ pairwise_disjoint B ∧ complete G A ∧ complete G B → ∃! coloring : coloring G 2, ∀ u v ∈ G.E, coloring u ≠ coloring v, from by {
        assume (A B : set G) (h : A ∪ B = G.V ∧ pairwise_disjoint A ∧ pairwise_disjoint B ∧ complete G A ∧ complete G B),
        show ∃! coloring : coloring G 2, ∀ u v ∈ G.E, coloring u ≠ coloring v, from by {
          have h1 : A = (A ∩ B) ∪ (A \ B), from set.ext.2 (by {
            rw [set.inter_comm,set.union_inter_cancel_left], unfold set.inter_eq, rw h.1.1, unfold set.sUnion,
          }),
          have h2 : A ∩ B = ∅, from (h.2.2 0 0 h.2.1 (set.not_mem_empty 0
end --Needs more than 2000 tokens!

--OUTPUT 9
theorem bipartite_iff_two_colorable {G : Type*} [graph G] : bipartite G ↔ ∃ (V1 V2 : set (vertex G)), is_coloring G {c | c = red ∨ c = blue} V1 V1.compl V2 V2.compl :=
begin
  split,
  exact @bipartite_two_colorable G _,
  exact @two_colorable_bipartite G _,
end

--OUTPUT 10
theorem bipartite_2_colorable (G : Type*) [graph G] : 
  ∀ V₁ V₂ : G, (∀ v₁ v₂ : V₁, ¬v₁.adj v₂) ∧ (∀ v₁ v₂ : V₂, ¬v₁.adj v₂) ∧
  (∀ v₁ ∈ V₁, ∃ v₂ ∈ V₂, v₁.adj v₂) ∧ (∀ v₂ ∈ V₂, ∃ v₁ ∈ V₁, v₁.adj v₂)
    ↔ bipartite (exists_colorable_of_two_colorable G) :=
begin
  assume (V₁ V₂ : G),
  have h1 : ∀ v₁ v₂ : V₁, ¬v₁.adj v₂ ↔ v₁.color ≠ v₂.color, from assume v₁ v₂,
    by {
      have h2 : ∀ a b : G, a.color ≠ b.color → ¬a.adj b, from by {
        assume (a : G) (b : G),
        assume (h : a.color ≠ b.color) (h' : a.adj b),
        have h3 : a.color = b.color, from by {rw ←color_color G, exact two_colorable.both_colors a b h'},
        contradiction,
      },
      assume h : v₁.adj v₂,
      have h2 : v₁.color = v₂.color, from by {have h3 : v₁.adj v₂ ∧ v₂.adj v₁, from by {split,exact h, exact h},exact two_colorable.both_colors _ _ h3},
      have h3 : ¬v₁.color = v₂.color, from by {rw ←color_color G, exact two_colorable.both_colors _ _ h},
      have h4 : v₁.color ≠ v₂.color, from by {contradiction,},
      show ¬v₁.adj v₂, from h2 h4,
      show v₁.color ≠ v₂.color, from by {rw ←color_color G, exact two_colorable.both_colors _ _ h},
    },
have h2 : ∀ v₁ v₂ : V₂, ¬v₁.adj v₂ ↔ v₁.color ≠ v₂.color, from assume v₁ v₂,
    by {
      have h1 : ∀ a b : G, a.color ≠ b.color → ¬a.adj b, from by {
        assume (a : G) (b : G),
        assume (h : a.color ≠ b.color) (h' : a.adj b),
        have h3 : a.color = b.color, from by {rw ←color_color G, exact two_colorable.both_colors a b h'},
        contradiction,
      },
      assume h : v₁.adj v₂,
      have h2 : v₁.color = v₂.color, from by {have h3 : v₁.adj v₂ ∧ v₂.adj v₁, from by {split,exact h, exact h},exact two_colorable.both_colors _ _ h3},
      have h3 : ¬v₁.color = v₂.color, from by {rw ←color_color G, exact two_colorable.both_colors _ _ h},
      have h4 : v₁.color ≠ v₂.color, from by {contradiction,},
      show ¬v₁.adj v₂, from h2 h4,
      show v₁.color ≠ v₂.color, from by {rw ←color_color G, exact two_colorable.both_colors _ _ h},
    },
  have h3 : (∀ v₁ v₂ : V₁, ¬v₁.adj v₂) ∧ (∀ v₁ v₂ : V₂, ¬v₁.adj v₂) ↔ ∀ a b ∈ V₁, a.color ≠ b.color ∧ ∀ a b ∈ V₂, a.color ≠ b.color, from 
    by {split;
    assume (h : (∀ v₁ v₂ : V₁, ¬v₁.adj v₂) ∧ (∀ v₁ v₂ : V₂, ¬v₁.adj v₂)),
    show ∀ a b ∈ V₁, a.color ≠ b.color ∧ ∀ a b ∈ V₂, a.color ≠ b.color, from
    by {
      split;
      assume a b,
      assume (h1 : a ∈ V₁) (h2 : b ∈ V₁),
      show a.color ≠ b.color, from h.left a b,
      assume a b,
      assume (h1 : a ∈ V₂) (h2 : b ∈ V₂),
      show a.color ≠ b.color, from h.right a b,
    },
    assume (h : ∀ a b ∈ V₁, a.color ≠ b.color ∧ ∀ a b ∈ V₂, a.color ≠ b.color),
    show (∀ v₁ v₂ : V₁, ¬v₁.adj v₂) ∧ (∀ v₁ v₂ : V₂, ¬v₁.adj v₂), from
    by {
      split;
      assume v₁ v₂,
      show ¬v₁.adj v₂, from by {
        have h1 : ∀ a b, a.color ≠ b.color → ¬a.adj b, from by {
          assume (a : G) (b : G),
          assume (h : a.color ≠ b.color) (h' : a.adj b),
          have h3 : a.color = b.color, from by {rw ←color_color G, exact two_colorable.both_colors a b h'},
          contradiction,
        },
        assume h : v₁.adj v₂,
        have h2 : v₁.color = v₂.color, from by {have h3 : v₁.adj v₂ ∧ v₂.adj v₁, from by {split,exact h, exact h},exact two_colorable.both_colors _ _ h3},
        have h3 : ¬v₁.color = v₂.color, from by {rw ←color_color G, exact two_colorable.both_colors _ _ h},
        have h4 : v₁.color ≠ v₂.color, from by {contradiction,},
        show ¬v₁.adj v₂, from h2 h4,
      },
      assume v₁ v₂,
      show ¬v₁.adj v₂, from by {
        have h1 : ∀ a b, a.color ≠ b.color → ¬a.adj b, from by {
          assume (a : G) (b : G),
          assume (h : a.color ≠ b.color) (h' : a.adj b),
          have h3 : a.color = b.color, from by {rw ←color_color G, exact two_colorable.both_colors a b
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
  assume (A : set α) (hA : A ∈ 𝒫 S) (B : set α) (hB : B ∈ 𝒫 S),
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by {split,apply set.subset_of_mem_powerset,exact hA,apply set.subset_of_mem_powerset,exact hB},
  have h2 : (A ∩ B) ⊆ A, from by apply set.inter_subset_left,
  have h3 : (A ∩ B) ⊆ S, from by {apply set.subset.trans h2 h1.left},
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
  calc (x + y)^2 = (x+y)*(x+y) : by rw sq
  ... = x*(x+y) + y*(x+y) : by rw add_mul
  ... = x*x + x*y + y*x + y*y : by {rw [mul_comm x (x+y),mul_comm y (x+y)], rw [add_mul,add_mul], ring}
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by {
    assume a b : G, use a⁻¹ * b, obviously, },
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by {
    assume a b : G, use b * a⁻¹, obviously, }, 

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from 
    assume a : G, h1 a a,
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from
    assume a : G, h2 a a,

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
