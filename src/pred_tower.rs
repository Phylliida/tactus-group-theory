//  FA-9a: Predicate-base port of `tower.rs` (the Britton-via-tower scaffold).
//
//  Defines the iterated amalgamated free product T_n = G_0 *_A G_1 *_A ... *_A G_n
//  over a PREDICATE base (`PredHNNData`/`PredAmalgamatedData`/`PredPresentation`)
//  and proves that G = G_0 embeds in T_n via the TEXTBOOK one-shot AFP injectivity.
//
//  Cayley LEAPFROG (cohen-faithfulness-primary-source.md §11/§12): the original
//  `tower.rs` carried a parallel Cayley-table path (`tower_h_prereqs_at`,
//  `tower_cayley_chain`, `lemma_g0_embeds_in_tower`) built on `h_prereqs` +
//  `normal_form_amalgamated`'s coset-table `lemma_afp_injectivity`.  That path is
//  OFF the critical path — `britton_via_tower` consumes only the TEXTBOOK chain —
//  and the Cayley machinery was leapfrogged in the predicate port (no pred analog).
//  So this module ports the textbook chain (+ structural lemmas + the Part E
//  scaffold) and drops the Cayley trio (+ its `curry`/`word_in_copy` helpers).
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
use crate::free_product::shift_word;
use crate::pred_presentation::*;
use crate::pred_free_product::*;
use crate::pred_amalgamated_free_product::*;
use crate::pred_normal_form_amalgamated::*;
use crate::pred_hnn::*;

verus! {

//  ============================================================
//  Part A: Tower definitions
//  ============================================================

///  The AFP data at tower junction k: tower(k) *_A base.
///    p1 = tower(k)
///    p2 = base
///    identifications[i] = (shift(a_i, k*ng), b_i)
pub open spec fn tower_afp_data(data: PredHNNData, k: nat) -> PredAmalgamatedData
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    PredAmalgamatedData {
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
///    tower(data, n+1) = amalgamated_free_product_pred(tower_afp_data(data, n))
pub open spec fn tower_presentation(data: PredHNNData, n: nat) -> PredPresentation
    decreases n, 0nat,
{
    if n == 0 {
        data.base
    } else {
        amalgamated_free_product_pred(tower_afp_data(data, (n - 1) as nat))
    }
}

//  ============================================================
//  Part B: Tower structural lemmas
//  ============================================================

///  Tower has (n+1)*ng generators.
pub proof fn lemma_tower_num_generators(data: PredHNNData, n: nat)
    requires
        hnn_pred_data_valid(data),
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
        crate::pred_normal_form_afp_textbook::lemma_afp_num_gens_pred(
            free_product_pred(afp_data.p1, afp_data.p2),
            amalgamation_relators_pred(afp_data),
        );
        assert(free_product_pred(afp_data.p1, afp_data.p2).num_generators
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
pub proof fn lemma_tower_valid(data: PredHNNData, n: nat)
    requires
        hnn_pred_data_valid(data),
    ensures
        pred_presentation_valid(tower_presentation(data, n)),
    decreases n, 0nat,
{
    if n == 0 {
        reveal(pred_presentation_valid);
    } else {
        let prev = (n - 1) as nat;
        lemma_tower_afp_data_valid(data, prev);
        lemma_amalgamated_pred_valid(tower_afp_data(data, prev));
    }
}

///  The tower AFP data at level k has valid amalgamated data.
pub proof fn lemma_tower_afp_data_valid(data: PredHNNData, k: nat)
    requires
        hnn_pred_data_valid(data),
    ensures
        amalgamated_data_pred_valid(tower_afp_data(data, k)),
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);

    reveal(pred_presentation_valid);
    assert(pred_presentation_valid(data.base));

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
//  Part D: Textbook tower embedding (uses one-shot AFP injectivity)
//  ============================================================

///  Textbook prerequisites at tower level k:
///  - identifications_isomorphic_pred: the identification map is an isomorphism
///  - action_preserves_canonical: the van der Waerden action preserves canonical states
///  (identity state canonicality is proved from amalgamated_data_pred_valid via
///   lemma_identity_state_canonical)
pub open spec fn tower_textbook_prereqs_at(data: PredHNNData, k: nat) -> bool {
    let afp_data = tower_afp_data(data, k);
    &&& crate::pred_normal_form_amalgamated::identifications_isomorphic_pred(afp_data)
    &&& crate::pred_normal_form_afp_textbook::action_preserves_canonical(afp_data)
}

///  Textbook prerequisites hold at all tower levels 0..n-1.
pub open spec fn tower_textbook_chain(data: PredHNNData, n: nat) -> bool {
    forall|k: nat| k < n ==> #[trigger] tower_textbook_prereqs_at(data, k)
}

///  Textbook tower embedding: G_0 embeds in tower(n) via one-shot AFP injectivity.
pub proof fn lemma_g0_embeds_in_tower_textbook(
    data: PredHNNData, n: nat, w: Word,
)
    requires
        hnn_pred_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_pred_presentation(tower_presentation(data, n), w, empty_word()),
        tower_textbook_chain(data, n),
    ensures
        equiv_in_pred_presentation(data.base, w, empty_word()),
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
        crate::pred_normal_form_afp_textbook::lemma_afp_injectivity(afp_data, w);

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
//  Part E: Britton's lemma via tower (statement + scaffold)
//  ============================================================

///  Level at position j in an HNN word: count of Gen(n) minus count of Inv(n) in positions j+1..len-1.
///  With right-to-left processing, this tracks the "current copy" after processing from position j.
pub open spec fn level_at(data: PredHNNData, w: Word, j: int) -> int
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
pub open spec fn max_level(data: PredHNNData, w: Word) -> int {
    //  Placeholder (matches the finite tower.rs scaffold) — properly defined when
    //  the derivation translation is implemented in the FA-9b britton port.
    0
}

///  Translate a base-only HNN word (no stable letters) to its tower copy.
///  Base word w at level 0 maps to w itself (copy 0 generators = base generators).
pub open spec fn translate_base_word(data: PredHNNData, w: Word) -> Word {
    w
}

///  Britton's lemma: if w is a base word and w ≡ ε in the HNN extension G*, then w ≡ ε in G.
///
///  States the theorem with the tower prerequisites as conditions; the derivation
///  translation (HNN derivation → tower of sufficient height) is the FA-9b britton port.
///  The key structural contribution: AFP injectivity + tower induction.
pub proof fn britton_lemma_via_tower(
    data: PredHNNData, n: nat, w: Word,
)
    requires
        hnn_pred_data_valid(data),
        hnn_pred_associations_isomorphic(data),
        word_valid(w, data.base.num_generators),
        equiv_in_pred_presentation(hnn_pred_presentation(data), w, empty_word()),
        //  Tower prerequisites (derivable from hnn_pred_associations_isomorphic in principle)
        tower_textbook_chain(data, n),
        //  The derivation fits within tower height n
        equiv_in_pred_presentation(tower_presentation(data, n), w, empty_word()),
    ensures
        equiv_in_pred_presentation(data.base, w, empty_word()),
{
    lemma_g0_embeds_in_tower_textbook(data, n, w);
}

} //  verus!
