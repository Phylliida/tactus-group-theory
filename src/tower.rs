//  Tower construction for Britton's lemma.
//
//  Defines the iterated amalgamated free product T_n = G_0 *_A G_1 *_A ... *_A G_n
//  and proves that G = G_0 embeds in T_n (conditional on Cayley table existence).
//
//  The tower is built recursively:
//    tower(data, 0) = data.base
//    tower(data, n+1) = AFP(tower(data, n), data.base, identifications at junction n↔n+1)
//
//  Copy k uses generators k*ng .. (k+1)*ng - 1 where ng = base.num_generators.
//  Junction k↔k+1 identifies a_i in copy k with b_i in copy k+1.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::normal_form_amalgamated::*;
use crate::hnn::*;

verus! {

//  ============================================================
//  Part A: Tower definitions
//  ============================================================

///  The AFP data at tower junction k: tower(k) *_A base.
///    p1 = tower(k)
///    p2 = base
///    identifications[i] = (shift(a_i, k*ng), b_i)
pub open spec fn tower_afp_data(data: HNNData, k: nat) -> AmalgamatedData
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    AmalgamatedData {
        p1: tower_presentation(data, k),
        p2: data.base,
        identifications: Seq::new(
            data.associations.len(),
            |i: int| (
                shift_word(data.associations[i].0, k * ng),
                data.associations[i].1,
            ),
        ),
    }
}

///  Tower presentation: (n+1) copies of G, glued by identification relators.
///    tower(data, 0) = data.base
///    tower(data, n+1) = amalgamated_free_product(tower_afp_data(data, n))
pub open spec fn tower_presentation(data: HNNData, n: nat) -> Presentation
    decreases n, 0nat,
{
    if n == 0 {
        data.base
    } else {
        amalgamated_free_product(tower_afp_data(data, (n - 1) as nat))
    }
}

///  Shift a word to copy k in the tower.
pub open spec fn word_in_copy(w: Word, ng: nat, k: nat) -> Word {
    shift_word(w, k * ng)
}

///  Curry a 2-argument spec_fn into a 1-argument spec_fn at a fixed first argument.
pub open spec fn curry(f: spec_fn(nat, nat) -> nat, k: nat) -> spec_fn(nat) -> nat {
    |h: nat| f(k, h)
}

///  h_prereqs holds at tower level k with indexed Cayley tables and phi maps.
pub open spec fn tower_h_prereqs_at(
    data: HNNData,
    tower_cts: Seq<crate::todd_coxeter::CosetTable>,
    base_ct: crate::todd_coxeter::CosetTable,
    phi_at: spec_fn(nat, nat) -> nat,
    phi_inv_at: spec_fn(nat, nat) -> nat,
    k: nat,
) -> bool {
    k < tower_cts.len() &&
    h_prereqs(tower_cts[k as int], base_ct,
              curry(phi_at, k), curry(phi_inv_at, k),
              tower_afp_data(data, k))
}

///  All tower AFP levels 0..n-1 have suitable Cayley tables for AFP injectivity.
pub open spec fn tower_cayley_chain(
    data: HNNData, n: nat,
    tower_cts: Seq<crate::todd_coxeter::CosetTable>,
    base_ct: crate::todd_coxeter::CosetTable,
    phi_at: spec_fn(nat, nat) -> nat,
    phi_inv_at: spec_fn(nat, nat) -> nat,
) -> bool {
    &&& tower_cts.len() >= n
    &&& forall|k: nat| k < n ==>
        #[trigger] tower_h_prereqs_at(data, tower_cts, base_ct, phi_at, phi_inv_at, k)
}

//  ============================================================
//  Part B: Tower structural lemmas
//  ============================================================

///  Tower has (n+1)*ng generators.
pub proof fn lemma_tower_num_generators(data: HNNData, n: nat)
    requires
        hnn_data_valid(data),
    ensures
        tower_presentation(data, n).num_generators == (n + 1) * data.base.num_generators,
    decreases n,
{
    let ng = data.base.num_generators;
    if n == 0 {
        assert(tower_presentation(data, 0).num_generators == ng);
        assert(ng == 1 * ng);
    } else {
        let prev = (n - 1) as nat;
        lemma_tower_num_generators(data, prev);
        let afp_data = tower_afp_data(data, prev);
        crate::amalgamated_free_product::lemma_add_relators_num_generators(
            free_product(afp_data.p1, afp_data.p2),
            amalgamation_relators(afp_data),
        );
        assert(free_product(afp_data.p1, afp_data.p2).num_generators
            == afp_data.p1.num_generators + afp_data.p2.num_generators);
        assert(afp_data.p1.num_generators == n * ng);
        assert(afp_data.p2.num_generators == ng);
        assert(tower_presentation(data, n).num_generators == n * ng + ng);
        assert(n * ng + ng == (n + 1) * ng) by (nonlinear_arith);
    }
}

///  word_valid monotonicity: valid for m implies valid for any m' >= m.
proof fn lemma_word_valid_weaken(w: Word, m: nat, m_prime: nat)
    requires
        word_valid(w, m),
        m <= m_prime,
    ensures
        word_valid(w, m_prime),
{
    assert forall|k: int| 0 <= k < w.len()
        implies symbol_valid(w[k], m_prime)
    by {
        assert(symbol_valid(w[k], m));
        match w[k] {
            Symbol::Gen(i) => {}
            Symbol::Inv(i) => {}
        }
    }
}

///  Tower presentation is valid at every level.
pub proof fn lemma_tower_valid(data: HNNData, n: nat)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(tower_presentation(data, n)),
    decreases n, 0nat,
{
    if n == 0 {
        reveal(presentation_valid);
    } else {
        let prev = (n - 1) as nat;
        lemma_tower_afp_data_valid(data, prev);
        lemma_amalgamated_valid(tower_afp_data(data, prev));
    }
}

///  The tower AFP data at level k has valid amalgamated data.
pub proof fn lemma_tower_afp_data_valid(data: HNNData, k: nat)
    requires
        hnn_data_valid(data),
    ensures
        amalgamated_data_valid(tower_afp_data(data, k)),
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);

    reveal(presentation_valid);
    assert(presentation_valid(data.base));

    lemma_tower_valid(data, k);
    lemma_tower_num_generators(data, k);

    assert forall|i: int| 0 <= i < afp_data.identifications.len()
        implies ({
            &&& word_valid(afp_data.identifications[i].0, afp_data.p1.num_generators)
            &&& word_valid(afp_data.identifications[i].1, afp_data.p2.num_generators)
        })
    by {
        let a_i = data.associations[i].0;
        let b_i = data.associations[i].1;
        let u_i = shift_word(a_i, k * ng);
        assert(afp_data.identifications[i] == (u_i, b_i));
        assert(word_valid(a_i, ng));
        assert(word_valid(b_i, ng));
        //  shift(a_i, k*ng) is word_valid for (k+1)*ng = tower(k).num_generators
        assert(afp_data.p1.num_generators == (k + 1) * ng);
        assert forall|j: int| 0 <= j < u_i.len()
            implies symbol_valid(u_i[j], (k + 1) * ng)
        by {
            assert(symbol_valid(a_i[j], ng));
            match a_i[j] {
                Symbol::Gen(idx) => {
                    assert(u_i[j] == Symbol::Gen((idx + k * ng) as nat));
                    assert(idx + k * ng < (k + 1) * ng) by (nonlinear_arith)
                        requires idx < ng;
                }
                Symbol::Inv(idx) => {
                    assert(u_i[j] == Symbol::Inv((idx + k * ng) as nat));
                    assert(idx + k * ng < (k + 1) * ng) by (nonlinear_arith)
                        requires idx < ng;
                }
            }
        }
    }
}

//  ============================================================
//  Part C: Main embedding theorem
//  ============================================================

///  G_0 embeds in the tower: if w is a base word and w ≡ ε in tower(n), then w ≡ ε in G.
///
///  Proof by induction on n:
///    n = 0: tower(0) = base, trivial.
///    n > 0: tower(n) = AFP(tower(n-1), base, identifications).
///           By AFP injectivity: w ≡ ε in tower(n-1).
///           By IH: w ≡ ε in base.
pub proof fn lemma_g0_embeds_in_tower(
    data: HNNData, n: nat, w: Word,
    tower_cts: Seq<crate::todd_coxeter::CosetTable>,
    base_ct: crate::todd_coxeter::CosetTable,
    phi_at: spec_fn(nat, nat) -> nat,
    phi_inv_at: spec_fn(nat, nat) -> nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(tower_presentation(data, n), w, empty_word()),
        tower_cayley_chain(data, n, tower_cts, base_ct, phi_at, phi_inv_at),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
    decreases n,
{
    if n == 0 {
        //  tower(0) = base, nothing to do.
    } else {
        let prev = (n - 1) as nat;
        let ng = data.base.num_generators;
        let afp_data = tower_afp_data(data, prev);

        //  tower(n) = amalgamated_free_product(afp_data)

        //  w is valid for p1 = tower(prev) which has n*ng generators
        lemma_tower_num_generators(data, prev);
        assert(ng <= n * ng) by (nonlinear_arith)
            requires n >= 1;
        lemma_word_valid_weaken(w, ng, n * ng);

        //  Get Cayley tables for level prev directly from the indexed parameters
        assert(tower_h_prereqs_at(data, tower_cts, base_ct, phi_at, phi_inv_at, prev));
        let ct1 = tower_cts[prev as int];
        let phi = curry(phi_at, prev);
        let phi_inv = curry(phi_inv_at, prev);

        //  Apply AFP injectivity: w ≡ ε in tower(prev)
        lemma_afp_injectivity(ct1, base_ct, phi, phi_inv, afp_data, w);

        //  tower_cayley_chain for prev levels (monotonicity)
        assert(tower_cayley_chain(data, prev, tower_cts, base_ct, phi_at, phi_inv_at)) by {
            assert forall|k: nat| k < prev
                implies #[trigger] tower_h_prereqs_at(data, tower_cts, base_ct, phi_at, phi_inv_at, k)
            by { assert(k < n); }
        }

        //  IH: w ≡ ε in base
        lemma_g0_embeds_in_tower(data, prev, w, tower_cts, base_ct, phi_at, phi_inv_at);
    }
}

//  ============================================================
//  Part D: Textbook tower embedding (uses one-shot AFP injectivity)
//  ============================================================

///  Textbook prerequisites at tower level k:
///  - identifications_isomorphic: the identification map is an isomorphism
///  - action_preserves_canonical: the van der Waerden action preserves canonical states
///  (identity state canonicality is now proved from amalgamated_data_valid via lemma_identity_state_canonical)
pub open spec fn tower_textbook_prereqs_at(data: HNNData, k: nat) -> bool {
    let afp_data = tower_afp_data(data, k);
    &&& crate::normal_form_amalgamated::identifications_isomorphic(afp_data)
    &&& crate::normal_form_afp_textbook::action_preserves_canonical(afp_data)
}

///  Textbook prerequisites hold at all tower levels 0..n-1.
pub open spec fn tower_textbook_chain(data: HNNData, n: nat) -> bool {
    forall|k: nat| k < n ==> #[trigger] tower_textbook_prereqs_at(data, k)
}

///  Textbook tower embedding: G_0 embeds in tower(n) via one-shot AFP injectivity.
///  Same structure as lemma_g0_embeds_in_tower but with simpler prerequisites.
pub proof fn lemma_g0_embeds_in_tower_textbook(
    data: HNNData, n: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(tower_presentation(data, n), w, empty_word()),
        tower_textbook_chain(data, n),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
    decreases n,
{
    if n == 0 {
    } else {
        let prev = (n - 1) as nat;
        let ng = data.base.num_generators;
        let afp_data = tower_afp_data(data, prev);

        lemma_tower_num_generators(data, prev);
        assert(ng <= n * ng) by (nonlinear_arith) requires n >= 1;
        lemma_word_valid_weaken(w, ng, n * ng);

        lemma_tower_valid(data, prev);
        lemma_tower_afp_data_valid(data, prev);

        //  Textbook AFP injectivity at level prev
        assert(tower_textbook_prereqs_at(data, prev));
        crate::normal_form_afp_textbook::lemma_afp_injectivity(afp_data, w);

        //  IH
        assert(tower_textbook_chain(data, prev)) by {
            assert forall|k: nat| k < prev
                implies #[trigger] tower_textbook_prereqs_at(data, k)
            by { assert(k < n); }
        }
        lemma_g0_embeds_in_tower_textbook(data, prev, w);
    }
}

//  ============================================================
//  Part E: Britton's lemma via tower (statement)
//  ============================================================

///  Level at position j in an HNN word: count of Gen(n) minus count of Inv(n) in positions j+1..len-1.
///  With right-to-left processing, this tracks the "current copy" after processing from position j.
pub open spec fn level_at(data: HNNData, w: Word, j: int) -> int
    decreases (w.len() - j),
{
    let n = data.base.num_generators;
    if j >= w.len() {
        0
    } else if w[j] == Symbol::Gen(n) {
        level_at(data, w, j + 1) + 1
    } else if w[j] == Symbol::Inv(n) {
        level_at(data, w, j + 1) - 1
    } else {
        level_at(data, w, j + 1)
    }
}

///  Maximum level reached in a word.
pub open spec fn max_level(data: HNNData, w: Word) -> int {
    //  The max over all positions j of level_at(data, w, j)
    //  For a base word w (no stable letters), this is 0.
    //  For words with stable letters, bounded by the number of Gen(n) occurrences.
    0 //  placeholder — will be properly defined when derivation translation is implemented
}

///  Translate a base-only HNN word (no stable letters) to its tower copy.
///  Base word w at level 0 maps to w itself (copy 0 generators = base generators).
pub open spec fn translate_base_word(data: HNNData, w: Word) -> Word {
    //  For base words: tower copy 0 uses generators 0..ng-1 = base generators.
    //  So the translation is the identity.
    w
}

///  Britton's lemma: if w is a base word and w ≡ ε in the HNN extension G*, then w ≡ ε in G.
///
///  Proof sketch:
///  1. w ≡ ε in G* → derivation → translate to tower of sufficient height
///  2. tower(m) equivalence for w
///  3. lemma_g0_embeds_in_tower_textbook → w ≡ ε in G
///
///  The derivation translation (step 1) requires tracking levels through intermediate words
///  and showing each HNN step maps to a valid tower step. This is ~400 lines of
///  step-by-step translation (future work).
///
///  For now, we state the theorem with the tower prerequisites as conditions.
///  The key structural contribution: AFP injectivity (204 verified) + tower induction.
pub proof fn britton_lemma_via_tower(
    data: HNNData, n: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        //  Tower prerequisites (derivable from hnn_associations_isomorphic in principle)
        tower_textbook_chain(data, n),
        //  The derivation fits within tower height n
        equiv_in_presentation(tower_presentation(data, n), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    lemma_g0_embeds_in_tower_textbook(data, n, w);
}

} //  verus!
