#[cfg(verus_keep_ghost)]
pub mod symbol;

#[cfg(verus_keep_ghost)]
pub mod word;

#[cfg(verus_keep_ghost)]
pub mod reduction;

#[cfg(verus_keep_ghost)]
pub mod presentation;

// pred_presentation: FORK-A DE-RISK PROBE (non-committing). A faithful predicate-base port of
// `presentation` with `relators: spec_fn(Word) -> bool`, kept SEPARATE from the verified finite
// tower. Measures scoping #2 (does the derivation algebra port verbatim + does the word-carrying
// relator core still close under the Lean backend?). See docs/cohen-faithfulness-primary-source.md
// §4/§7. Reversible: delete the file + this line. Full Fork-A build remains gated on Danielle.
#[cfg(verus_keep_ghost)]
pub mod pred_presentation;

// FORK-A brick 2: predicate-base equivalence-congruence algebra
// (analog of presentation_lemmas.rs core). Reversible, zero regression.
#[cfg(verus_keep_ghost)]
pub mod pred_presentation_lemmas;

// FORK-A brick 1: predicate-base HNN extensions (analog of `hnn.rs`).
// docs/FORK-DECISION.md, cohen-faithfulness-primary-source.md §1/§6c.
// Separate from the verified finite `hnn` module: reversible, zero regression.
#[cfg(verus_keep_ghost)]
pub mod pred_hnn;

// FORK-A brick 3: predicate-base free products (analog of free_product.rs).
// Introduces the predicate shift (§4); word-level shift reused from finite
// free_product. Reversible, zero regression.
#[cfg(verus_keep_ghost)]
pub mod pred_free_product;

// FORK-A brick 4: predicate-base amalgamated free products + add_relators_pred
// (analog of amalgamated_free_product.rs + quotient.rs add_relators). The last
// piece of the relator-agnostic CONSTRUCTION layer. Reversible, zero regression.
#[cfg(verus_keep_ghost)]
pub mod pred_amalgamated_free_product;

// FORK-A brick 5: predicate-base homomorphisms (analog of homomorphism.rs).
// The BOTTOM of the AFP normal-form / Britton-tower port: free-product
// injectivity (normal_form_free_product) is proven via retraction homomorphisms
// routing through lemma_hom_pred_preserves_equiv. Reversible, zero regression.
#[cfg(verus_keep_ghost)]
pub mod pred_homomorphism;

#[cfg(verus_keep_ghost)]
pub mod presentation_lemmas;

#[cfg(verus_keep_ghost)]
pub mod quotient;

#[cfg(verus_keep_ghost)]
pub mod benign;

// base_swap: the *reflecting* base-swap — adding relators that are already consequences of a
// presentation does not change the group. Foundation stone for the Brick-5 completeness reroute
// (C3.0): augment the Britton base with finite family-(II) relators (group-preserving via
// lemma_II), making the a-levels literal isos. See docs/brick5-completeness-plan.md §2.2ter.
#[cfg(verus_keep_ghost)]
pub mod base_swap;

#[cfg(verus_keep_ghost)]
pub mod hnn;

#[cfg(verus_keep_ghost)]
pub mod britton;

#[cfg(verus_keep_ghost)]
pub mod free_product;

#[cfg(verus_keep_ghost)]
pub mod homomorphism;

#[cfg(verus_keep_ghost)]
pub mod shortlex;

#[cfg(verus_keep_ghost)]
pub mod amalgamated_free_product;

#[cfg(verus_keep_ghost)]
pub mod normal_form_free_product;

#[cfg(verus_keep_ghost)]
pub mod normal_form_amalgamated;

#[cfg(verus_keep_ghost)]
pub mod abelianization;

#[cfg(verus_keep_ghost)]
pub mod concrete;

#[cfg(verus_keep_ghost)]
pub mod britton_infra;

#[cfg(verus_keep_ghost)]
pub mod finite;

#[cfg(verus_keep_ghost)]
pub mod completeness;

#[cfg(verus_keep_ghost)]
pub mod coset_group;

#[cfg(verus_keep_ghost)]
pub mod todd_coxeter;

#[cfg(verus_keep_ghost)]
pub mod runtime;

#[cfg(verus_keep_ghost)]
pub mod tower;

#[cfg(verus_keep_ghost)]
pub mod normal_form_afp_textbook;

#[cfg(verus_keep_ghost)]
pub mod britton_via_tower;

#[cfg(verus_keep_ghost)]
pub mod higman_operations;

// free_word_problem: the free-group word problem IS free reduction —
// `equiv_in_presentation(free_group(n), w1, w2) ⟹ freely_equivalent(w1, w2)` (converse of
// `lemma_freely_equivalent_implies_equiv`). The bridge from `≡_{free_group}` to a free NORMAL FORM,
// needed by the Higman–Neumann–Neumann `{a⁻ⁱbaⁱ}`-free cancellation argument (Layer 0.5).
#[cfg(verus_keep_ghost)]
pub mod free_word_problem;

// conj_free: Layer 0.5 crux (Miller §4.1) — `{a⁻ⁱbaⁱ}` free in F₂. The counting infra (`count1`,
// `lemma_count1_emb`: count1(φ(w)) = |w|) + family defs; the core "central b survives" is the
// remaining work (blueprint plan).
#[cfg(verus_keep_ghost)]
pub mod conj_free;

// conj_free_core: the core "central b survives" — the net-exponent invariant `bsep`, its
// preservation under reduction, the base case, and the assembled `{a⁻ⁱbaⁱ}`-free family lemma.
#[cfg(verus_keep_ghost)]
pub mod conj_free_core;

// conj_free_b: Layer 0.5 (Miller §4.1) SECOND free basis — `{b⁻ⁱabⁱ}` free in F₂, the swap-
// automorphism image of `conj_free_core`'s `{a⁻ⁱbaⁱ}`. The F₂-part of Miller's `B = ⟨a, b⁻ⁱabⁱ⟩`.
#[cfg(verus_keep_ghost)]
pub mod conj_free_b;

#[cfg(verus_keep_ghost)]
pub mod tietze;

// machine_group: the Aanderaa–Cohen machine group (Layer 1 of the constructive
// finitely-presented-group-for-ZFC build). Fresh, faithful to the canonical
// construction (docs/aanderaa-cohen-construction.md) — replaces the superseded
// stub whose config word q_state·αᵃ·βᵇ was provably wrong.
#[cfg(verus_keep_ghost)]
pub mod machine_group;

// ii_subset: property (ii)⊆ structural-decomposition work — kept in its own module so its
// predicate-heavy in_residue_class goals don't pollute machine_group's triggers.
#[cfg(verus_keep_ghost)]
pub mod ii_subset;

// kp_pinch: E2.C / L1 — the ⟨K,p⟩ pinch-elimination engine (property II central core).
// Its own module to avoid trigger pollution / concurrent-edit churn with ii_subset.
#[cfg(verus_keep_ghost)]
pub mod kp_pinch;

// tower_peel: E2.D — property (vi) A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M) via the top-down tower peel,
// reusing the single-letter engine in kp_pinch.  See docs/e2d-tower-peel-plan.md.
#[cfg(verus_keep_ghost)]
pub mod tower_peel;

// config_reduce: E2.B — config reduction core (property (v) T-free uniqueness).
// Run-merge / zero-drop atoms → reduction function → ≡_A / coord lemmas → uniqueness.
// See docs/property-v-tfree-architecture.md.
#[cfg(verus_keep_ghost)]
pub mod config_reduce;

// prop_v: E2.B — property (v) assembly (prop_v_holds), consuming config_reduce + the quad wiring.
#[cfg(verus_keep_ghost)]
pub mod prop_v;

// word_numbering: Layer 2 / Brick 1 — pure word combinatorics for Cohen §9.6's α↔word numbering
// (w_α(c), w_α(b), w_α(bc) substitution maps + the numbering predicate I). Self-contained on
// symbol.rs / word.rs; abstract base-offsets leave the global layout to Brick 2 (h1.rs).
#[cfg(verus_keep_ghost)]
pub mod word_numbering;

// layout: Layer 2 / Brick 2 foundation — the global generator-index table for the Higman tower
// H₁ ⊆ H₂ ⊆ H₃ (K_M, c, b, d, p, a-block, k blocks). Pure arithmetic; reused across bricks 2–5.
#[cfg(verus_keep_ghost)]
pub mod layout;

// h1: Layer 2 / Brick 2 — the H₁-level finite generators/relators (word-numbering maps at the
// layout bases + the b_i c_j = c_j b_i commutator relators of set (I)). Approach (b): finite only.
#[cfg(verus_keep_ghost)]
pub mod h1;

// h2: Layer 2 / Brick 3 — the p-level HNN H₂ = HNN(H₁, p | p⁻¹ t p = t d). The single schematic
// p-relation of set (I); built over h1_base, stable letter at the layout's p slot.
#[cfg(verus_keep_ghost)]
pub mod h2;

// h3: Layer 2 / Brick 4 — the top of the tower H₃ = HNN(H₂; a_i, k | a_i:A↔A_i, k:A₊↔A₋). The
// finite a_i (φ_i) / k (ψ) HNN associations of set (I); iterated single-letter HNN over h2_pres.
#[cfg(verus_keep_ghost)]
pub mod h3;

// free_basis: Layer 2 / Brick 2 (deep half) — the FREE-BASIS LEMMA (blueprint p.279,
// Cohen Cor-1-to-Prop-1.8). The kill homomorphism φ:H₁→K_M + the abstract pullback engine
// (lemma_pullback_free) + F2 (config words {t_α} free in K_M, lemma_config_emb_free) ⟹
// "{t_α w_α(b) d} is a free basis of H₁" (lemma_basis_elt_free + lemma_free_to_basis_elt).
#[cfg(verus_keep_ghost)]
pub mod free_basis;

// higman_consequences: Layer 2 / Brick 5 — the Higman payoff. SOUNDNESS of the BRIDGE THEOREM
// COMPLETE (60/0): the headline `lemma_III` proves `(α,0)∈H₀(M) ⟹ h3_pres ⊢ w_α(c)=1` — Cohen's
// "(II),(III) are consequences of the finite set (I)", so h3_pres IS the f.p. Higman group. The c.e.
// set S={w_α(c)} is realized as H₃'s word problem among the c-gens. Completeness (⟹) is the remaining
// arc (see docs/brick5-plan.md: h3_pres = h3_with_S + benign/kp_pinch).
#[cfg(verus_keep_ghost)]
pub mod higman_consequences;

// h3_ii: Layer 2 / Brick 5 COMPLETENESS, C3.1 — the finite family-(II) augmentation. Builds the
// augmenting relator words (family_II), proves each ≡_{h3_pres} ε (lemma_II → relator form), and
// (C3.1c) the bottom-augmented tower h3_II + the group-preservation iff via base_swap's
// lemma_same_group_iff. See docs/brick5-completeness-plan.md §2.2ter / §4 C3.1.
#[cfg(verus_keep_ghost)]
pub mod h3_ii;

// f_free: Layer 2 / Brick 5 COMPLETENESS, C3.2c / F1 — the free subgroup F=⟨t,x,d,b_j⟩ of h2_II.
// The Route-B prerequisite (docs/brick5-c3.2c-plan.md §3b): F free in h1_base (mirror of the free-
// product structure K_M ∗ (F(c)×F(b)) ∗ ⟨d⟩) makes A=⟨t,x,d,b_j,p⟩=HNN(F free, p | family II) a
// legitimate presentation, so von Dyck reduces to "φ_l respects the p-conjugations". F1a (⟨t,x⟩
// free in K_M) built; the free-product assembly follows.
#[cfg(verus_keep_ghost)]
pub mod f_free;

// f_free_tower: Layer 2 / Brick 5, C3.2c / F1, B2 — iterate f_free's single free-stable-letter step
// into the H₁ free basis. `[t,x,b_j,d]` is free in the (n+1)-fold empty-association HNN tower over
// K_M, i.e. K_M ∗ F(b) ∗ ⟨d⟩. Seed = F1a (lemma_tx_is_free_family); the tower induction is
// lemma_free_stable_tower_extends. Closed forms pin the generator layout for the B3 h1_base bridge.
#[cfg(verus_keep_ghost)]
pub mod f_free_tower;

// f_free_h1: Layer 2 / Brick 5, C3.2c / F1, B3 — lift the B2 free family to h1_base. The
// homomorphism kill_c: h1_base → K_M ∗ F(b) ∗ ⟨d⟩ (kill c's, fix K_M, shift b/d down by n) is valid
// (commutators map to cancelling pairs), so the free_basis pullback engine reduces "F free in
// h1_base" to B2. Next: B4 (lift via A1, the prop_v-scale residue/p-conjugation iso).
#[cfg(verus_keep_ghost)]
pub mod f_free_h1;

// higman_completeness: Layer 2 / Brick 5 COMPLETENESS — the `C ↪ H₃` faithful direction.
// Owns the `in_C` predicate (C1: `w ∈ ncl(S)` over the k-HNN base h3_upto(2n)) + its three
// subgroup-closure props, and (in progress) the Fork-B virtual-iso k-descent (C4) + assembly
// (C5). See docs/brick5-completeness-plan.md.
#[cfg(verus_keep_ghost)]
pub mod higman_completeness;

// f_free_a1: Layer 2 / Brick 5, C3.2c / A1 — the recognition-datum association isomorphism
// `hnn_associations_isomorphic(recog_data)`. Rung 1 = lemma_km_faithful_in_h1 (the kill_hom
// retraction: K_M ↪ h1_base faithful). Rung 2 = lemma_config_emb_free_in_h1 (config family free in
// h1_base = F2 lifted via the retraction). See docs/brick5-c3.2c-plan.md §4.2.
#[cfg(verus_keep_ghost)]
pub mod f_free_a1;

// h2_faithful: Layer 2 / Brick 3 payoff — `H₂ = HNN(H₁, p)` faithfully contains `H₁` (hence `C`).
// `lemma_h2_associations_isomorphic` (the single p-association `(t,t·d)` is a subgroup iso) +
// `lemma_h1_faithful_in_h2_pres` (`H₁ ↪ H₂` faithful). Both = A1 (`f_free_a1`) at the empty index set
// (`recog_data(…,[]) = h2_data`, `h2_II(…,[]) = h2_pres`). Closes AGENDA §3.2's H₂ checkbox.
#[cfg(verus_keep_ghost)]
pub mod h2_faithful;

// pa_data: Layer 2 / Brick 5, C3.2c / the C-arc — the abstract source presentation
// `P_A = HNN(F=free_group(n+3), p | family II over F)`. F-indexing matches the a_words order
// [t=0,x=1,d=2,b_j=2+j,p=n+3]. Pins the definition + validity; both crux directions route through
// `w ≡_{P_A} ε`. See docs/brick5-c3.2c-plan.md §5.
#[cfg(verus_keep_ghost)]
pub mod pa_data;

// free_family_perm: Layer 2 / Brick 5, C3.2c / the C-arc — free-family permutation invariance
// (`lemma_free_family_permute`): reordering a free family's generator list preserves freeness,
// via F3 + relabeling embeddings. The "permute once, early" tool (Route A) that turns B3's
// `[t,x,b_j,d]` h1_base-freeness into the C-arc `a_words` order `[t,x,d,b_j]`.
#[cfg(verus_keep_ghost)]
pub mod free_family_perm;

// phi_l_maps: Layer 2 / Brick 5, C3.2c / the C-arc — the F-part embeddings map_a/map_b of
// P_A → h2_II. map_a's F-part a_words_F=[t,x,d,b_j] proven FREE in h1_base (lemma_map_a_faithful)
// via B3 + lemma_free_family_permute (the Route-A reorder). See docs/brick5-c3.2c-plan.md §5.
#[cfg(verus_keep_ghost)]
pub mod phi_l_maps;

// phi_l_iso: Layer 2 / Brick 5, C3.2c / the C-arc — the per-level iso crux
// `lemma_phi_l_iso_at_h2II` (emb(a_words,w) ≡ ε ⟺ emb(b_words,w) ≡ ε over h2_II), via the
// unified HNN lifting lemma (faithfulness lifts base→HNN under an association-preserving
// embedding), instantiated for map_a/map_b. First brick = the φ_l digit-scaling identity
// φ_l(config(β,0)) = config(mβ+l,0). See docs/brick5-c3.2c-plan.md §5.
#[cfg(verus_keep_ghost)]
pub mod phi_l_iso;

// phi_l_lift: Layer 2 / Brick 5, C3.2c / the C-arc — the von-Dyck-backward halves of the two
// faithful P_A → h2_II embeddings (generic `lemma_pa_von_dyck_backward` via
// `lemma_emb_respects_source_equiv`, P_A's free base ⟹ relators = the p-conjugations), plus
// map_a's instantiation. The forward unified HNN lifting lemma lands here next.
#[cfg(verus_keep_ghost)]
pub mod phi_l_lift;

// phi_l_forward: Layer 2 / Brick 5, C3.2c / the C-arc — the FORWARD (faithful) direction of the
// unified HNN lifting lemma (emb(map,w) ≡_{h2_II} ε ⟹ w ≡_{P_A} ε). map_a is a length-preserving
// relabeling ⟹ same-index pinch descent; the real content is the intersection property. Starts
// with generic leaves (free-family injectivity, concat_all distribution, cancellation).
#[cfg(verus_keep_ghost)]
pub mod phi_l_forward;

// phi_l_pinch: Layer 2 / Brick 5, C3.2c / the C-arc — map_a's forward Britton-peel assembly:
// the column correspondence (recog columns = a_words_F-images of pa columns), the same-index
// pinch descent, and the forward injectivity. Wires phi_l_forward's generic leaves to recog_data.
#[cfg(verus_keep_ghost)]
pub mod phi_l_pinch;

// phi_l_mapb: Layer 2 / Brick 5, C3.2c / the C-arc — map_b's forward (faithful) direction via the
// "map_b = ψ_a ∘ φ_l" source-level factoring (φ_l_src = the P_A-level φ_l subst).  M1 (down-payment):
// emb(b_words,w) = emb(a_words, emb(φ_l_src, w)), reducing map_b forward to map_a forward (DONE) +
// φ_l_src injective on P_A. See docs/brick5-c3.2c-plan.md §5.
#[cfg(verus_keep_ghost)]
pub mod phi_l_mapb;

// r_prime: Layer 2 / Brick 5, C3.2c / map_b forward — the (R') canw index-tracking core.
// emb(φ_F,u) ∈ ⟨config_emb(bet)⟩ ⟹ ∈ ⟨config_emb(σ(bet))⟩ (σ(β)=mβ+l), under σ-backward-saturation.
// The irreducible "Image(φ_F)∩⟨t,x⟩ = config-products with indices ≡ l (mod m)" fact, via canw
// coordinate-tracking reusing lemma_tfree_coord_restrict. See docs/brick5-c3.2c-plan.md §7.
#[cfg(verus_keep_ghost)]
pub mod r_prime;

// r_prime_b: Layer 2 / Brick 5, C3.2c / map_b forward — the b-side (R') reflection over pa_rhs.
// The M2 pinch-descent's b-column orientation; via kill_db projection + a-side coord core +
// free-basis transfer (config_emb ↔ pa_rhs_emb). See docs/brick5-c3.2c-plan.md §6.
#[cfg(verus_keep_ghost)]
pub mod r_prime_b;

// phi_l_mapb_fwd: Layer 2 / Brick 5, C3.2c / map_b forward — M2 (φ_l_src injective on P_A) +
// the map_b forward assembly. Spanning Britton peel over pa_data, (R) a/b for the pinch middle.
#[cfg(verus_keep_ghost)]
pub mod phi_l_mapb_fwd;

// phi_l_iso_tower: Layer 2 / Brick 5, C3.2d — lift the bottom crux up the a-tower (decreases-l
// faithfulness induction, mirror lemma_b_m_upto_faithful) → lemma_phi_l_iso at every level.
#[cfg(verus_keep_ghost)]
pub mod phi_l_iso_tower;
// C3.2 obstruction: machine-checked proof that `sigma_sat_upto` (the a-tower iso side condition) is
// UNSATISFIABLE for finite `alphas` — so `lemma_phi_l_iso`/`lemma_h3_II_upto_faithful` are vacuous and
// C3.2 must be reframed to a word-restricted virtual iso (docs/brick5-c4-plan.md §7).
#[cfg(verus_keep_ghost)]
pub mod phi_l_iso_unsat;
// C3.2 reframe (step 2): the BOUNDED σ-ORBIT — the finite, satisfiable replacement for the
// unsatisfiable universal σ-forward-closure (the word-restricted virtual-iso side condition).
#[cfg(verus_keep_ghost)]
pub mod sigma_orbit;
